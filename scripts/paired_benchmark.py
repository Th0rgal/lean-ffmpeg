#!/usr/bin/env python3
"""Quality-gated paired reference/candidate benchmark harness.

The manifest is the denominator. Every case is run with identical arguments,
at least two warmups per executable, and at least five alternating AB/BA pairs.
Missing media, command failures, decode failures, probe mismatches, and noisy
timings are blockers. Lossy cases are deliberately unsupported.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import time
import threading
import platform
import re
from pathlib import Path
from typing import Any


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def executable_pin(name: str) -> dict[str, Any]:
    resolved = shutil.which(name) if not Path(name).is_absolute() else name
    if not resolved or not Path(resolved).is_file():
        raise ValueError(f"executable unavailable: {name}")
    path = Path(resolved).resolve()
    return {"requested": name, "resolved": str(path), "sha256": sha256_file(path)}


def validate_manifest(manifest: Any, root: Path, warmups: int, trials: int) -> list[dict[str, Any]]:
    if not isinstance(manifest, dict) or manifest.get("complete") is not True:
        raise ValueError("manifest must set complete=true; partial denominators are rejected")
    if warmups < 2 or trials < 5:
        raise ValueError("require warmups >= 2 and paired trials >= 5")
    cases = manifest.get("cases")
    if not isinstance(cases, list) or not cases:
        raise ValueError("manifest requires a non-empty cases list")
    ids: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or not isinstance(case.get("id"), str) or not case["id"]:
            raise ValueError("each case needs a unique id")
        if case["id"] in ids:
            raise ValueError(f"duplicate case id: {case['id']}")
        ids.add(case["id"])
        if case.get("mode") not in ("exact", "lossless"):
            raise ValueError(f"case {case['id']}: lossy/unknown modes are unsupported")
        if case.get("input_format") not in ("nut", "wav"):
            raise ValueError(f"case {case['id']}: input_format must be nut or wav")
        if not isinstance(case.get("input"), str) or not case["input"]:
            raise ValueError(f"case {case['id']}: input is required")
        input_path = (root / case["input"]).resolve()
        if root != input_path and root not in input_path.parents:
            raise ValueError(f"case {case['id']}: input escapes root")
        if not input_path.is_file():
            raise ValueError(f"case {case['id']}: input unavailable: {case['input']}")
        if input_path.suffix.lower() != "." + case["input_format"]:
            raise ValueError(f"case {case['id']}: input extension must match input_format")
        expected = case.get("input_sha256")
        if not isinstance(expected, str) or not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("input_sha256 must pin every input in the manifest")
        if sha256_file(input_path) != expected:
            raise ValueError(f"case {case['id']}: input hash mismatch")
        if case.get("delegation_backend") not in ("delegated_ffmpeg", "native_unverified", "reference_control"):
            raise ValueError("delegation_backend must be delegated_ffmpeg, native_unverified, or reference_control")
        if case.get("output_suffix") not in (".nut", ".mkv", ".avi", ".mov", ".mp4", ".wav"):
            raise ValueError("unsupported output_suffix for bounded benchmark schema")
        validate_args(case.get("args"), case["input_format"])
    return cases


def validate_args(args, input_format):
    """Bounded self-contained nut/wav schema; no playlists or implicit codecs."""
    if input_format not in ("nut", "wav"):
        raise ValueError("input_format must be nut or wav")
    if not isinstance(args, list) or not args or not all(isinstance(x, str) for x in args):
        raise ValueError("args must be a non-empty string list")
    if args.count("-i") != 1 or args.count("{INPUT}") != 1 or args.count("{OUTPUT}") != 1 or args[-1] != "{OUTPUT}":
        raise ValueError("require exactly one -i {INPUT} and final {OUTPUT}")
    if "-f" in args:
        raise ValueError("input/output format flags are harness-controlled")
    try:
        copy_index = args.index("-c")
        if args[copy_index + 1] != "copy" or args.count("-c") != 1:
            raise ValueError("require one global -c copy")
    except (ValueError, IndexError):
        raise ValueError("require one global -c copy")
    input_index = args.index("-i")
    if copy_index < input_index:
        raise ValueError("global -c copy must follow input")
    lossless = {"copy", "rawvideo", "ffv1", "huffyuv", "pcm_u8", "pcm_s16le", "pcm_s24le", "pcm_s32le", "pcm_f32le", "pcm_f64le"}
    i = 0
    while i < len(args) - 1:
        flag = args[i]
        if flag in ("-an", "-vn"):
            i += 1; continue
        if i + 1 >= len(args) - 1:
            raise ValueError(f"missing value for {flag}")
        value = args[i + 1]
        if flag in ("-c:v", "-c:a") and i < copy_index:
            raise ValueError("global -c copy must precede per-stream overrides")
        if flag in ("-c:v", "-c:a") and value not in lossless:
            raise ValueError("per-stream codec must be lossless")
        if flag == "-c" and value != "copy":
            raise ValueError("global codec must be copy")
        valid = flag in ("-i", "-c", "-c:v", "-c:a", "-map", "-pix_fmt", "-ss", "-t", "-frames:v", "-vf")
        if flag == "-i": valid = value == "{INPUT}"
        elif flag == "-c": valid = value == "copy"
        elif flag in ("-c:v", "-c:a"): valid = value in lossless
        elif flag == "-map": valid = value in {"0", "0:v:0", "0:a:0"}
        elif flag == "-pix_fmt": valid = value in {"yuv420p", "yuv420p10le", "yuv420p16le", "yuv444p", "gray", "rgb24"}
        elif flag == "-vf": valid = bool(re.fullmatch(r"scale=[1-9][0-9]*:[1-9][0-9]*", value))
        elif flag in ("-ss", "-t"): valid = bool(re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", value)) and float(value) > 0
        elif flag == "-frames:v": valid = bool(re.fullmatch(r"[1-9][0-9]*", value))
        if not valid: raise ValueError(f"unsupported/unpinned argument: {flag} {value}")
        i += 2


def trial_order(trials: int) -> list[tuple[str, int]]:
    if trials < 5:
        raise ValueError("at least five paired trials are required")
    return [("reference", i) if i % 2 == 0 else ("candidate", i) for i in range(trials)]


def bounded_run(argv: list[str], cwd: Path, env: dict[str, str], timeout: float) -> dict[str, Any]:
    # File-backed logs bound memory and keep output capture out of timed work.
    with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        started = time.perf_counter_ns()
        try:
            process = subprocess.Popen(argv, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        except OSError as error:
            return {"status": "error", "elapsed_s": (time.perf_counter_ns() - started) / 1e9,
                    "returncode": None, "stdout": b"", "stderr": str(error).encode()}
        timed_out = threading.Event()
        def expire():
            timed_out.set()
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        timer = threading.Timer(timeout, expire)
        timer.start()
        try:
            process.wait()  # blocking wait avoids timeout polling quantizing timings
        finally:
            timer.cancel()
        status = "timeout" if timed_out.is_set() else ("ok" if process.returncode == 0 else "error")
        elapsed = (time.perf_counter_ns() - started) / 1e9
        stdout.seek(0); stderr.seek(0)
        out, err = stdout.read((1 << 20) + 1), stderr.read((1 << 20) + 1)
        if len(out) > (1 << 20) or len(err) > (1 << 20):
            status = "output_limit"
        return {"status": status, "elapsed_s": elapsed, "returncode": process.returncode,
                "stdout": out[:1 << 20], "stderr": err[:1 << 20]}


def output_info(path: Path) -> dict[str, Any]:
    if not path.is_file():
        return {"exists": False, "size": None, "sha256": None}
    return {"exists": True, "size": path.stat().st_size, "sha256": sha256_file(path)}


def normalized_probe(ffprobe: str, output: Path, cwd: Path, env: dict[str, str], timeout: float) -> dict[str, Any]:
    result = bounded_run([ffprobe, "-v", "error", "-count_frames", "-show_format", "-show_streams", "-of", "json", str(output)], cwd, env, timeout)
    if result["status"] != "ok":
        return {"status": "error", "stderr": result["stderr"].decode("utf-8", "replace")}
    try:
        doc = json.loads(result["stdout"])
    except json.JSONDecodeError as error:
        return {"status": "error", "stderr": f"invalid ffprobe JSON: {error}"}
    streams = []
    for stream in doc.get("streams", []):
        streams.append({k: stream.get(k) for k in ("index", "codec_type", "codec_name", "width", "height", "pix_fmt", "sample_rate", "channels", "duration", "nb_frames", "nb_read_frames", "sample_fmt", "time_base")})
    return {"status": "ok", "signature": {"format": {k: doc.get("format", {}).get(k) for k in ("format_name", "duration")}, "streams": streams}}


def decoded_digest(decoder: str, output: Path, probe: dict, cwd: Path, env: dict[str, str], timeout: float) -> dict[str, Any]:
    if probe.get("status") != "ok":
        return {"status": "error", "reason": "probe unavailable"}
    streams = probe["signature"]["streams"]
    try:
        duration = float(probe["signature"]["format"]["duration"])
        if not math.isfinite(duration) or duration <= 0 or not streams:
            raise ValueError("missing positive duration or streams")
    except (ValueError, TypeError, KeyError):
        return {"status": "error", "reason": "duration/streams unavailable"}
    digests = []
    audio_formats = {"u8": ("pcm_u8", "u8"), "s16": ("pcm_s16le", "s16le"),
                     "s32": ("pcm_s32le", "s32le"), "s64": ("pcm_s64le", "s64le"),
                     "flt": ("pcm_f32le", "f32le"), "dbl": ("pcm_f64le", "f64le")}
    for stream in streams:
        try:
            if int(stream["nb_read_frames"]) <= 0:
                raise ValueError()
        except (KeyError, TypeError, ValueError):
            return {"status": "error", "reason": "decoded frame count unavailable"}
        index = stream["index"]
        if stream["codec_type"] == "video" and stream.get("pix_fmt") and stream.get("width") and stream.get("height"):
            options = ["-c:v", "rawvideo", "-pix_fmt", stream["pix_fmt"], "-f", "rawvideo"]
        elif stream["codec_type"] == "audio" and stream.get("channels") and stream.get("sample_rate"):
            sample_format = (stream.get("sample_fmt") or "").removesuffix("p")
            if sample_format not in audio_formats:
                return {"status": "error", "reason": "unsupported audio sample format"}
            codec, muxer = audio_formats[sample_format]
            options = ["-c:a", codec, "-f", muxer]
        else:
            return {"status": "error", "reason": "unsupported stream type or missing properties"}
        raw = cwd / f"decoded-{index}.raw"
        result = bounded_run([decoder, "-nostdin", "-y", "-v", "error", "-threads", env["OMP_NUM_THREADS"],
                              "-i", str(output), "-map", f"0:{index}", *options,
                              "-threads", env["OMP_NUM_THREADS"], str(raw)], cwd, env, timeout)
        if result["status"] != "ok" or not raw.is_file() or raw.stat().st_size == 0:
            return {"status": "error", "reason": "decode failed or empty", "stderr": result["stderr"].decode("utf-8", "replace")}
        digests.append({"index": index, "bytes": raw.stat().st_size, "sha256": sha256_file(raw)})
        raw.unlink()
    return {"status": "ok", "streams": digests}


def quality_check(reference: dict[str, Any], candidate: dict[str, Any], mode: str) -> dict[str, Any]:
    if reference.get("status") != "ok" or candidate.get("status") != "ok":
        return {"ok": False, "reason": "command_failure"}
    if not reference["output"].get("exists") or not candidate["output"].get("exists"):
        return {"ok": False, "reason": "missing_output"}
    if not reference["output"].get("size") or not candidate["output"].get("size"):
        return {"ok": False, "reason": "empty_output"}
    if reference["decoded"].get("status") != "ok" or candidate["decoded"].get("status") != "ok":
        return {"ok": False, "reason": "decoded_quality_unavailable"}
    if not reference["decoded"].get("streams") or not candidate["decoded"].get("streams"):
        return {"ok": False, "reason": "decoded_quality_unavailable"}
    if reference["decoded"].get("streams") != candidate["decoded"].get("streams"):
        return {"ok": False, "reason": "decoded_digest_mismatch"}
    if reference["probe"].get("status") != "ok" or candidate["probe"].get("status") != "ok":
        return {"ok": False, "reason": "ffprobe_unavailable"}
    if reference["probe"]["signature"] != candidate["probe"]["signature"]:
        return {"ok": False, "reason": "ffprobe_signature_mismatch"}
    if mode == "exact" and reference["output"]["sha256"] != candidate["output"]["sha256"]:
        return {"ok": False, "reason": "exact_output_digest_mismatch"}
    return {"ok": True, "reason": "decoded_and_probe_equal"}


def stats(values: list[float]) -> dict[str, float]:
    if len(values) < 5:
        raise ValueError("at least five timed samples required")
    if any(not math.isfinite(x) or x <= 0 for x in values):
        raise ValueError("timings must be finite positive seconds")
    mean = statistics.fmean(values)
    cv = statistics.stdev(values) / mean if mean else math.inf
    return {"n": len(values), "median_s": statistics.median(values), "mean_s": mean, "cv": cv}


def run_case(case: dict[str, Any], root: Path, reference: str, candidate: str, ffprobe: str, decoder: str,
             env: dict[str, str], warmups: int, trials: int, timeout: float) -> dict[str, Any]:
    input_path = (root / case["input"]).resolve()
    input_pin = {"path": str(input_path), "sha256": sha256_file(input_path), "expected_sha256": case["input_sha256"], "size": input_path.stat().st_size}
    if input_pin["sha256"] != case["input_sha256"]:
        raise ValueError("input changed after manifest validation")
    warmup_records: list[dict[str, Any]] = []
    timed: dict[str, list[float]] = {"reference": [], "candidate": []}
    quality_records: list[dict[str, Any]] = []
    trial_records = []

    def execute(binary: str, work: Path) -> dict[str, Any]:
        output = work / ("output" + case["output_suffix"])
        args = [x.replace("{INPUT}", str(input_path)).replace("{OUTPUT}", str(output)) for x in case["args"]]
        input_pos = args.index("-i")
        args[input_pos:input_pos] = ["-f", case["input_format"]]
        threads = env["OMP_NUM_THREADS"]
        argv = [binary, "-nostdin", "-y", "-threads", threads,
                "-filter_threads", threads, "-filter_complex_threads", threads,
                *args[:-1], "-threads", threads, args[-1]]
        result = bounded_run(argv, work, env, timeout)
        result["argv"] = argv
        result["stdout"] = result["stdout"].decode("utf-8", "replace")
        result["stderr"] = result["stderr"].decode("utf-8", "replace")
        return result

    def inspect(result, work):
        output = work / ("output" + case["output_suffix"])
        info = output_info(output)
        probe = normalized_probe(ffprobe, output, work, env, timeout) if info["exists"] else {"status": "error", "reason": "missing_output"}
        decoded = decoded_digest(decoder, output, probe, work, env, timeout) if info["exists"] else {"status": "error", "reason": "missing_output"}
        result.update(output=info, probe=probe, decoded=decoded)

    for i in range(warmups):
        with tempfile.TemporaryDirectory(prefix=f"paired-warmup-{case['id']}-") as td:
            # Separate directories ensure no output or cache is shared between executables.
            work_ref, work_cand = Path(td) / "reference", Path(td) / "candidate"
            work_ref.mkdir(); work_cand.mkdir()
            ref = execute(reference, work_ref)
            cand = execute(candidate, work_cand)
            inspect(ref, work_ref); inspect(cand, work_cand)
            warmup_records.append({"index": i, "reference": ref, "candidate": cand})
            quality_records.append(quality_check(ref, cand, case["mode"]))

    for label, index in trial_order(trials):
        with tempfile.TemporaryDirectory(prefix=f"paired-trial-{case['id']}-") as td:
            work_ref, work_cand = Path(td) / "reference", Path(td) / "candidate"
            work_ref.mkdir(); work_cand.mkdir()
            if label == "reference":
                ref = execute(reference, work_ref); cand = execute(candidate, work_cand)
            else:
                cand = execute(candidate, work_cand); ref = execute(reference, work_ref)
            inspect(ref, work_ref); inspect(cand, work_cand)
            trial_records.append({"pair": index, "first": label, "reference": ref, "candidate": cand})
            timed["reference"].append(ref["elapsed_s"]); timed["candidate"].append(cand["elapsed_s"])
            quality_records.append(quality_check(ref, cand, case["mode"]))
    ref_stats, cand_stats = stats(timed["reference"]), stats(timed["candidate"])
    cv = max(ref_stats["cv"], cand_stats["cv"])
    threshold = max(0.01, 2 * cv)
    speedup = 1.0 - cand_stats["median_s"] / ref_stats["median_s"] if ref_stats["median_s"] else -math.inf
    quality_ok = all(item["ok"] for item in quality_records)
    per_case_regression = cand_stats["median_s"] > ref_stats["median_s"] * (1 + threshold)
    input_unchanged = input_path.is_file() and sha256_file(input_path) == case["input_sha256"]
    eligible = quality_ok and input_unchanged and cv <= 0.03 and not per_case_regression
    return {"id": case["id"], "mode": case["mode"], "delegation_backend": case["delegation_backend"],
            "input": input_pin, "warmups": warmup_records, "trial_order": trial_order(trials),
            "trials": trial_records, "raw_times_s": timed, "reference_stats": ref_stats, "candidate_stats": cand_stats,
            "cv": cv, "acceptance_threshold": threshold, "median_speedup": speedup,
            "quality": quality_records, "per_case_material_regression": per_case_regression,
            "input_unchanged": input_unchanged, "gain_above_noise": speedup >= threshold, "passes_case_gates": eligible}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--reference", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--ffprobe", required=True)
    parser.add_argument("--decoder", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--warmups", type=int, default=2)
    parser.add_argument("--trials", type=int, default=5)
    parser.add_argument("--threads", type=int, required=True)
    parser.add_argument("--cpu-list", required=True)
    parser.add_argument("--timeout", type=float, default=120.0)
    args = parser.parse_args()
    if args.threads < 1:
        raise SystemExit("threads must be positive")
    root = args.root.resolve()
    manifest_bytes = args.manifest.read_bytes()
    manifest_hash = hashlib.sha256(manifest_bytes).hexdigest()
    manifest = json.loads(manifest_bytes)
    cases = validate_manifest(manifest, root, args.warmups, args.trials)
    ref_pin, cand_pin, probe_pin, dec_pin = (executable_pin(x) for x in (args.reference, args.candidate, args.ffprobe, args.decoder))
    env = dict(os.environ, LC_ALL="C", LANG="C", OMP_NUM_THREADS=str(args.threads), OPENBLAS_NUM_THREADS=str(args.threads), MKL_NUM_THREADS=str(args.threads), RAYON_NUM_THREADS=str(args.threads), LEANAV_FFMPEG_BIN=ref_pin["resolved"], LEANAV_FFPROBE_BIN=probe_pin["resolved"])
    affinity_enforced = False
    if sys.platform.startswith("linux"):
        cpus = {int(x) for x in args.cpu_list.split(",")}
        if not cpus or not cpus.issubset(os.sched_getaffinity(0)):
            raise SystemExit("requested CPU affinity is unavailable")
        os.sched_setaffinity(0, cpus)
        if os.sched_getaffinity(0) != cpus:
            raise SystemExit("CPU affinity enforcement failed")
        affinity_enforced = True
    reports = []
    for case in cases:
        reports.append(run_case(case, root, ref_pin["resolved"], cand_pin["resolved"], probe_pin["resolved"], dec_pin["resolved"],
                                env, args.warmups, args.trials, args.timeout))
    pins_unchanged = all(sha256_file(Path(pin["resolved"])) == pin["sha256"] for pin in (ref_pin, cand_pin, probe_pin, dec_pin))
    overall_gain = 1 - math.exp(statistics.fmean(math.log(r["candidate_stats"]["median_s"] / r["reference_stats"]["median_s"]) for r in reports))
    threshold = max(0.01, 2 * max(r["cv"] for r in reports))
    manifest_unchanged = args.manifest.is_file() and sha256_file(args.manifest) == manifest_hash
    timing_valid = affinity_enforced and manifest_unchanged and pins_unchanged and all(r["passes_case_gates"] for r in reports)
    report = {"schema": "maxwell.ffmpeg.paired-benchmark.v1", "manifest": str(args.manifest.resolve()),
              "manifest_sha256": manifest_hash, "manifest_unchanged": manifest_unchanged, "reference": ref_pin, "candidate": cand_pin,
              "ffprobe": probe_pin, "decoder": dec_pin, "threads": args.threads, "cpu_list": args.cpu_list,
              "warmups_per_executable": args.warmups, "paired_trials": args.trials,
              "lossy_supported": False, "hardware": platform.uname()._asdict(),
              "execution_scope": "CPU CLI; native/delegated status declared per case, not verified by this harness; no standalone/GPU claim",
              "affinity_enforced": affinity_enforced, "cases": reports,
              "geometric_mean_speedup": overall_gain, "acceptance_threshold": threshold,
              "executable_pins_unchanged": pins_unchanged,
              "optimization_accepted": False,
              "external_gates_required": ["oracle/profile certificate", "frozen tools", "proof/quality checks", "independent review", "cross-hardware evidence"],
              "timing_valid": timing_valid,
              "measured_gain_above_noise": timing_valid and overall_gain >= threshold,
              "independent_implementation_speedup_eligible": False,
              "benchmark_gates_passed": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0 if report["timing_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
