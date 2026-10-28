"""BSF name/token routing using the production parser and a non-media backend.

The fixture reflects frozen upstream token grammar. Backend option semantics,
codec compatibility and media correctness are intentionally separate checks.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("LFFMPEG_BINARY", str(ROOT / ".lake/build/bin/lffmpeg")))
VECTORS = json.loads((ROOT / "tests/vectors/bsf_routing.json").read_text())
FLAGS = ("-bsf", "-bsf:v", "-bsf:a", "-bsf:s", "-vbsf", "-absf", "-sbsf")


class BsfRoutingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file() or not os.access(BINARY, os.X_OK):
            raise AssertionError(f"reviewed executable required: {BINARY}")

    def setUp(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.source = self.root / "input with spaces.mp4"
        self.source.write_bytes(b"routing placeholder; not media")
        self.output = self.root / "output with spaces.nut"
        self.log = self.root / "argv.json"
        shim = self.root / "backend.py"
        shim.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "args = sys.argv[1:]\n"
            "with open(os.environ['BSF_ROUTING_LOG'], 'w') as stream:\n"
            "    json.dump({'argv': args, 'argv_hex': [os.fsencode(a).hex() for a in args]}, stream)\n"
            "sys.stderr.write('BSF_ROUTING_BACKEND\\n')\n"
            "sys.exit(int(os.environ['BSF_ROUTING_EXIT']))\n"
        )
        shim.chmod(0o755)
        self.env = dict(os.environ, LEANAV_FFMPEG_BIN=str(shim),
                        BSF_ROUTING_LOG=str(self.log), BSF_ROUTING_EXIT="0")

    def arguments(self, value, flag="-bsf:v", before_input=False):
        option = [flag, value]
        tail = ["-c", "copy", str(self.output)]
        return (option + ["-i", str(self.source)] + tail if before_input else
                ["-i", str(self.source)] + option + tail)

    def plan(self, args):
        result = subprocess.run([str(BINARY), "plan", *args], capture_output=True,
                                text=True, timeout=10, env=self.env)
        return result, json.loads(result.stdout)

    def invoke(self, args, code=0):
        self.log.unlink(missing_ok=True)
        argv = ["-nostdin", "-y", "-v", "error", *args]
        result = subprocess.run([str(BINARY), *argv], capture_output=True,
                                text=True, timeout=10,
                                env=dict(self.env, BSF_ROUTING_EXIT=str(code)))
        return result, argv

    def assert_delegated(self, args, code=0):
        result, plan = self.plan(args)
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertEqual(plan["error_count"], 0)
        self.assertEqual(plan["backend"]["tier"], "delegated_faithful")
        actual, argv = self.invoke(args, code)
        self.assertEqual(actual.returncode, code, actual.stderr)
        record = json.loads(self.log.read_text())
        self.assertEqual(record["argv"], argv)
        self.assertEqual(record["argv_hex"], [os.fsencode(a).hex() for a in argv])
        self.assertEqual(actual.stdout, "")
        self.assertIn("BSF_ROUTING_BACKEND", actual.stderr)
        self.assertFalse(self.output.exists())

    def assert_rejected(self, args, reason=None):
        result, plan = self.plan(args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(plan["backend"]["tier"], "unsupported")
        if reason:
            self.assertIn(reason, plan["backend"]["reasons"])
        actual, _ = self.invoke(args)
        self.assertNotEqual(actual.returncode, 0)
        self.assertFalse(self.log.exists())
        self.assertFalse(self.output.exists())

    def test_pure_token_and_name_gate_regressions(self):
        # lake may spawn Lean, so a timeout must reap the whole owned group.
        child = subprocess.Popen(["lake", "env", "lean", "--run", "tests/bsf_chain.lean"],
                                 cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, start_new_session=True)
        try:
            stdout, stderr = child.communicate(timeout=60)
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.communicate()
            raise
        self.assertEqual(child.returncode, 0, stdout + stderr)

    def test_upstream_lexical_edge_vectors(self):
        self.assertEqual(len(VECTORS["gate_vectors"]), 32)
        for vector in VECTORS["gate_vectors"]:
            with self.subTest(value=vector["value"], accepted=vector["accepted"]):
                args = self.arguments(vector["value"])
                if vector["accepted"]:
                    self.assert_delegated(args)
                else:
                    self.assert_rejected(args)

    def test_actual_escaped_setts_and_trim_values_are_preserved(self):
        self.assertEqual(len(VECTORS["escaped_fate_values"]), 10)
        for vector in VECTORS["escaped_fate_values"]:
            for before_input in (True, False):
                with self.subTest(target=vector["target"], before_input=before_input):
                    self.assert_delegated(self.arguments(vector["value"], vector["flag"],
                                                          before_input))

    def test_existing_bsf_flags_and_aliases_use_same_gate(self):
        value = r"setts=ts=if(eq(N\,0)\,PTS\,DTS),trim=end=5"
        for flag in FLAGS:
            for before_input in (True, False):
                with self.subTest(flag=flag, before_input=before_input):
                    self.assert_delegated(self.arguments(value, flag, before_input))
                    self.assert_rejected(self.arguments("null,,trim", flag, before_input))

    def test_five_evidenced_public_names_delegate(self):
        for name in VECTORS["new_names"]:
            for value in (name, "'" + name + "'", "==" + name):
                with self.subTest(value=value):
                    self.assert_delegated(self.arguments(value))
            with self.subTest(uppercase=name.upper()):
                self.assert_rejected(self.arguments(name.upper()))

    def test_unknown_names_do_not_bypass_gate_through_quotes_or_escapes(self):
        for value in ("unknown_bsf", "'unknown_bsf'", r"unknown\_bsf", "==unknown_bsf",
                      "null,unknown_bsf", "'source'", "sink", "null,,", "=", "==="):
            with self.subTest(value=value):
                self.assert_rejected(self.arguments(value))

    def test_repeated_options_keep_original_order_and_literal_values(self):
        first = r"setts=ts=if(eq(N\,0)\,PTS\,DTS)"
        args = ["-bsf:v", first, "-i", str(self.source), "-bsf:a", "'trim'=end=5",
                "-bsf:v", "null,", "-c", "copy", str(self.output)]
        self.assert_delegated(args)

    def test_backend_semantic_errors_and_diagnostics_are_preserved(self):
        for value in ("setts=ts=(", "jpegapp=sidecar=not_hex", "trim=unknown_option=1"):
            for code in (1, 73):
                with self.subTest(value=value, code=code):
                    self.assert_delegated(self.arguments(value), code)

    def test_option_values_are_not_evaluated_by_a_shell(self):
        marker = self.root / "shell-marker"
        for value in (f"setts=ts=$(touch {marker})", f"setts=ts=`touch {marker}`",
                      f"setts=ts=PTS;touch {marker}"):
            with self.subTest(value=value):
                self.assert_delegated(self.arguments(value), 1)
                self.assertFalse(marker.exists())

    def test_missing_value_and_unrelated_co_blockers_remain_rejected(self):
        self.assert_rejected(["-i", str(self.source), str(self.output), "-bsf:v"])
        for option in (["-xerror"], ["-stream_loop", "2"], ["-c:v", "apv"], ["-f", "apv"]):
            with self.subTest(option=option):
                self.assert_rejected(["-i", str(self.source), "-bsf:v", "trim=end=5",
                                      *option, str(self.output)])

    def test_path_and_protocol_security_is_unchanged(self):
        for unsafe in ("concat:first.mp4|second.mp4", "https://invalid.example/input.mp4",
                       "file:input.mp4", "pipe:0", "/proc/self/mem", "media/../outside.mp4"):
            for position in ("input", "output"):
                with self.subTest(unsafe=unsafe, position=position):
                    args = (["-i", unsafe, "-bsf:v", "'trim'=end=5", str(self.output)]
                            if position == "input" else
                            ["-i", str(self.source), "-bsf:v", "'trim'=end=5", unsafe])
                    self.assert_rejected(args, "unsafe_protocol_or_path_traversal")


if __name__ == "__main__":
    unittest.main()
