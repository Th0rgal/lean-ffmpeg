"""Mutation controls for the compatibility classifier and execution harness."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).parents[1] / "scripts" / "historical_compat.py"


class HistoricalCompatHarnessTests(unittest.TestCase):
    def run_case(self, ref_code, cand_code, probe=None):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            for name, code in (("ref", ref_code), ("cand", cand_code)):
                path = root / name
                path.write_text(f"#!{sys.executable}\nimport sys\nfrom pathlib import Path\n{code}\n")
                path.chmod(0o755)
            mf, out = root / "m.json", root / "r.json"
            case = {"id": "control", "args": ["{OUT}"]}
            if probe is not None:
                case["probe"] = [sys.executable, "-c", probe, "{OUT}"]
            mf.write_text(json.dumps({"cases": [case]}))
            p = subprocess.run([sys.executable, str(SCRIPT), "--manifest", str(mf), "--output", str(out),
                                "--reference", str(root / "ref"), "--candidate", str(root / "cand")],
                               capture_output=True, text=True)
            return p.returncode, json.loads(out.read_text())

    def check(self, ref, cand, expected, exit_code=1):
        code, report = self.run_case(ref, cand)
        self.assertEqual(code, exit_code)
        self.assertEqual(report["counts"], {expected: 1})
        self.assertEqual(report["case_count"], 1)
        self.assertEqual(report["pass_count"], int(exit_code == 0))
        self.assertFalse(report["both_fail_is_pass"])

    def test_matching_output_positive_control(self):
        self.check("Path(sys.argv[1]).write_bytes(b'valid')", "Path(sys.argv[1]).write_bytes(b'valid')", "MATCH", 0)

    def test_both_fail_mutant(self):
        self.check("sys.exit(1)", "sys.exit(1)", "BOTH_FAIL")

    def test_candidate_failure_mutant(self):
        self.check("Path(sys.argv[1]).write_bytes(b'valid')", "sys.exit(1)", "CANDIDATE_FAIL")

    def test_output_difference_mutant(self):
        self.check("Path(sys.argv[1]).write_bytes(b'valid')", "Path(sys.argv[1]).write_bytes(b'wrong')", "OUTPUT_DIFF")

    def test_missing_output_mutant(self):
        self.check("pass", "pass", "OUTPUT_MISSING")

    def test_empty_output_mutant(self):
        self.check("Path(sys.argv[1]).touch()", "Path(sys.argv[1]).touch()", "OUTPUT_EMPTY")

    def test_constant_probe_does_not_pass_corrupt_output(self):
        code, report = self.run_case("Path(sys.argv[1]).write_bytes(b'valid-media')",
                                     "Path(sys.argv[1]).write_bytes(b'arbitrary-corrupt-payload')",
                                     "print('same arbitrary signature')")
        self.assertEqual(code, 1)
        self.assertEqual(report["counts"], {"SIGNATURE_MATCH_UNVERIFIED": 1})
        self.assertEqual(report["pass_count"], 0)
        probes = report["records"][0]["probes"]
        self.assertEqual(probes["reference"]["stdout"], "same arbitrary signature\n")
        self.assertIn("-c", probes["reference_argv"])

    def test_identical_bytes_do_not_override_failing_requested_probe(self):
        code, report = self.run_case("Path(sys.argv[1]).write_bytes(b'valid')",
                                     "Path(sys.argv[1]).write_bytes(b'valid')",
                                     "import sys; sys.exit(1)")
        self.assertEqual(code, 1)
        self.assertEqual(report["counts"], {"PROBE_MISMATCH_OR_FAILURE": 1})
        self.assertEqual(report["pass_count"], 0)


if __name__ == "__main__":
    unittest.main()
