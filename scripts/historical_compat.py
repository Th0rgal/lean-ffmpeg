#!/usr/bin/env python3
"""Run a pinned, explicit FFmpeg compatibility matrix.

The old 119/120 and 79-case inputs are not present in this checkout.  This
harness deliberately requires a case manifest instead of silently rebuilding a
denominator from whatever media happens to be installed.  A case is passing
only when the reference and candidate both succeed and their requested
comparisons pass byte-for-byte; BOTH_FAIL is retained as a failure. Matching
metadata signatures are retained as unverified evidence, never a quality pass.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
import shutil
from pathlib import Path


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(argv: list[str], cwd: Path, timeout: float) -> dict:
    try:
        p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout, env={**os.environ, "LC_ALL": "C", "LANG": "C"})
    except FileNotFoundError as e:
        return {"status": "unavailable", "exit": None, "stdout": "", "stderr": str(e)}
    except subprocess.TimeoutExpired as e:
        return {"status": "timeout", "exit": None, "stdout": str(e.stdout or ""), "stderr": str(e.stderr or "")}
    return {"status": "pass" if p.returncode == 0 else "fail", "exit": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}


def expand(items: list[str], root: Path, out: Path) -> list[str]:
    result = []
    for item in items:
        result.append(item.replace("{ROOT}", str(root)).replace("{OUT}", str(out)))
    return result


def output_record(path: Path) -> dict:
    return {"exists": path.is_file(), "size": path.stat().st_size if path.is_file() else None,
            "sha256": sha256(path) if path.is_file() else None}


def classify(ref: dict, cand: dict, ref_out: dict, cand_out: dict, probe_equal: bool | None) -> str:
    if ref["status"] == "unavailable" or cand["status"] == "unavailable":
        return "UNAVAILABLE"
    if ref["status"] != "pass" and cand["status"] != "pass":
        return "BOTH_FAIL"
    if ref["status"] != "pass":
        return "REFERENCE_FAIL"
    if cand["status"] != "pass":
        return "CANDIDATE_FAIL"
    if not ref_out["exists"] or not cand_out["exists"]:
        return "OUTPUT_MISSING"
    if not ref_out["size"] or not cand_out["size"]:
        return "OUTPUT_EMPTY"
    if probe_equal is False:
        return "PROBE_MISMATCH_OR_FAILURE"
    if ref_out["sha256"] == cand_out["sha256"]:
        return "MATCH"
    if probe_equal is True:
        return "SIGNATURE_MATCH_UNVERIFIED"
    return "OUTPUT_DIFF"


def one(case: dict, reference: str, candidate: str, root: Path, timeout: float) -> dict:
    inputs = []
    for name in case.get("inputs", []):
        path = (root / name).resolve()
        if not path.is_relative_to(root):
            raise ValueError("input must remain within ROOT")
        inputs.append({"path": name, "resolved": str(path), **output_record(path)})
    if any(not item["exists"] for item in inputs):
        return {"id": case["id"], "inputs": inputs, "classification": "INPUT_UNAVAILABLE"}
    with tempfile.TemporaryDirectory(prefix="ffmpeg-compat-") as td:
        cwd = Path(td)
        out_name = case.get("output", "output.bin")
        if not isinstance(out_name, str) or Path(out_name).name != out_name or out_name in (".", "..", ""):
            raise ValueError("output must be a basename")
        out_ref, out_cand = cwd / "reference" / out_name, cwd / "candidate" / out_name
        (cwd / "reference").mkdir(); (cwd / "candidate").mkdir()
        # Inputs are immutable files under ROOT; commands use {ROOT} explicitly.
        ref_argv = [reference, *expand(case["args"], root, out_ref)]
        cand_argv = [candidate, *expand(case["args"], root, out_cand)]
        ref = run(ref_argv, cwd, timeout)
        cand = run(cand_argv, cwd, timeout)
        ref_info, cand_info = output_record(out_ref), output_record(out_cand)
        probe_equal = None
        probes = None
        if case.get("probe"):
            # A probe command must print a normalized signature. It is run once
            # per output and compared byte-for-byte; probe failures are unknown.
            probe = case["probe"]
            rp_argv, cp_argv = expand(probe, root, out_ref), expand(probe, root, out_cand)
            rp = run(rp_argv, cwd, timeout)
            cp = run(cp_argv, cwd, timeout)
            probe_equal = (rp["status"] == cp["status"] == "pass"
                           and bool(rp["stdout"].strip()) and rp["stdout"] == cp["stdout"])
            probes = {"reference": rp, "candidate": cp,
                      "reference_argv": rp_argv, "candidate_argv": cp_argv}
        return {"id": case["id"], "category": case.get("category", "unspecified"),
                "inputs": inputs,
                "reference": ref, "candidate": cand, "reference_output": ref_info,
                "candidate_output": cand_info, "probe_equal": probe_equal, "probes": probes,
                "reference_argv": ref_argv, "candidate_argv": cand_argv,
                "classification": classify(ref, cand, ref_info, cand_info, probe_equal)}


def executable_record(name: str) -> dict:
    path = shutil.which(name)
    return {"requested": name, "resolved": str(Path(path).resolve()) if path else None,
            "sha256": sha256(Path(path)) if path else None}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--reference", default="ffmpeg")
    ap.add_argument("--candidate", default="lffmpeg")
    ap.add_argument("--root", default=".")
    ap.add_argument("--output", required=True)
    ap.add_argument("--timeout", type=float, default=60.0)
    args = ap.parse_args()
    manifest = json.loads(Path(args.manifest).read_text())
    cases = manifest.get("cases") if isinstance(manifest, dict) else None
    if not isinstance(cases, list) or not cases:
        raise SystemExit("manifest must contain a non-empty cases list")
    ids = [c.get("id") for c in cases]
    if any(not i for i in ids) or len(set(ids)) != len(ids):
        raise SystemExit("case ids must be non-empty and unique")
    root = Path(args.root).resolve()
    for case in cases:
        if not isinstance(case.get("args"), list) or not all(isinstance(a, str) for a in case["args"]):
            raise SystemExit("every case requires a string args array")
        if not isinstance(case.get("inputs", []), list) or not all(isinstance(a, str) for a in case.get("inputs", [])):
            raise SystemExit("inputs must be a string array of paths relative to ROOT")
        if "probe" in case and (not isinstance(case["probe"], list) or not case["probe"]
                                or not all(isinstance(a, str) for a in case["probe"])):
            raise SystemExit("probe must be a non-empty string command array")
    records = [one(c, args.reference, args.candidate, root, args.timeout) for c in cases]
    counts = {}
    for r in records:
        counts[r["classification"]] = counts.get(r["classification"], 0) + 1
    report = {"manifest": str(Path(args.manifest).resolve()), "case_count": len(records),
              "counts": counts, "records": records,
              "pass_count": counts.get("MATCH", 0),
              "both_fail_is_pass": False,
              "manifest_sha256": sha256(Path(args.manifest)),
              "reference": executable_record(args.reference),
              "candidate": executable_record(args.candidate)}
    Path(args.output).write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0 if report["pass_count"] == report["case_count"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
