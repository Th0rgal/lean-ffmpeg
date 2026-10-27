import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "scripts/fate_target_exec.py"


class FateAdapterTests(unittest.TestCase):
    def test_exact_target_replacement_and_library_passthrough(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for name in ("reference", "candidate", "helper"):
                path = root / name
                path.write_text(f"#!{sys.executable}\nimport os,sys,json\n"
                                f"print(json.dumps([{name!r},sys.argv[1:],os.environ.get('LEANAV_FFMPEG_BIN')]))\n")
                path.chmod(0o755)
            env = dict(os.environ, FATE_REFERENCE_FFMPEG=str(root / "reference"),
                       FATE_CANDIDATE=str(root / "candidate"), FATE_EXEC_TRACE=str(root / "trace"),
                       FATE_CASE_NAME="fate-control")
            for target, expected in (("reference", "candidate"), ("helper", "helper")):
                p = subprocess.run([sys.executable, str(SCRIPT), str(root / target), "a b", "-flag"],
                                   env=env, capture_output=True, text=True, check=True)
                self.assertEqual(json.loads(p.stdout), [expected, ["a b", "-flag"], str((root / "reference").resolve())])
            trace = [json.loads(s) for s in (root / "trace").read_text().splitlines()]
            self.assertEqual([r["candidate_exercised"] for r in trace], [True, False])
            self.assertTrue(all(r["test"] == "fate-control" for r in trace))
            self.assertTrue(all(r["pid"] > 0 and r["timestamp_ns"] > 0 for r in trace))

    def test_missing_configuration_never_runs_target(self):
        env = {k: v for k, v in os.environ.items() if not k.startswith("FATE_")}
        p = subprocess.run([sys.executable, str(SCRIPT), "/bin/true"], env=env, capture_output=True)
        self.assertNotEqual(p.returncode, 0)

    def test_missing_candidate_cannot_fall_back_to_reference(self):
        with tempfile.TemporaryDirectory() as td:
            env = dict(os.environ, FATE_REFERENCE_FFMPEG="/bin/true",
                       FATE_CANDIDATE=td + "/missing", FATE_EXEC_TRACE=td + "/trace")
            p = subprocess.run([sys.executable, str(SCRIPT), "/bin/true"], env=env, capture_output=True)
            self.assertNotEqual(p.returncode, 0)
