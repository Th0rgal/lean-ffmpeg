#!/usr/bin/env python3
import argparse
import hashlib
import json
import os
import resource
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

DEFAULT_TIMEOUT = 30.0
DEFAULT_OUTPUT_LIMIT = 1024 * 1024
ENVIRONMENT_POLICY = {
    "preserved": ["PATH", "LC_ALL", "LANG", "LD_LIBRARY_PATH"],
    "locale": "C",
    "ld_library_path": "preserve only when explicitly set",
}


def resource_limits(cpu_seconds=None, address_space_bytes=None):
    def apply_limits():
        if cpu_seconds is not None:
            resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
        if address_space_bytes is not None:
            resource.setrlimit(resource.RLIMIT_AS, (address_space_bytes, address_space_bytes))
    return apply_limits


def sanitized_environment():
    environment = {
        "PATH": os.environ.get("PATH", ""),
        "LC_ALL": "C",
        "LANG": "C",
    }
    if os.environ.get("LD_LIBRARY_PATH"):
        environment["LD_LIBRARY_PATH"] = os.environ["LD_LIBRARY_PATH"]
    return environment


def fixture_output_path(case_dir, output):
    if output is None:
        return case_dir / "output.bin"
    if not isinstance(output, str) or not output:
        raise ValueError("fixture output must be a non-empty relative path")
    candidate = Path(output)
    if candidate.is_absolute() or candidate.anchor:
        raise ValueError("fixture output must be a relative path")
    resolved = (case_dir / candidate).resolve()
    case_root = case_dir.resolve()
    if resolved != case_root and case_root not in resolved.parents:
        raise ValueError("fixture output must stay within its case directory")
    return resolved


def kill_process_group(process):
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def executable_info(executable):
    requested = str(executable)
    resolved = shutil.which(requested) if not os.path.isabs(requested) else requested
    path = Path(resolved).resolve() if resolved and Path(resolved).exists() else None
    return {
        "requested": requested,
        "resolved": str(path) if path else None,
        "sha256": sha256_file(path) if path and path.is_file() else None,
    }


def bounded_run(argv, cwd, timeout, output_limit, cpu_seconds=None, address_space_bytes=None):
    try:
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=sanitized_environment(),
            start_new_session=True,
            preexec_fn=resource_limits(cpu_seconds, address_space_bytes),
        )
    except OSError as error:
        return {"status": "failed", "exit_status": None, "stdout": "", "stderr": str(error)}

    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ, "stdout")
    selector.register(process.stderr, selectors.EVENT_READ, "stderr")
    captured = {"stdout": bytearray(), "stderr": bytearray()}
    limited = False
    deadline = time.monotonic() + timeout
    while selector.get_map():
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            kill_process_group(process)
            process.stdout.close()
            process.stderr.close()
            selector.close()
            return {
                "status": "timeout",
                "exit_status": None,
                "stdout": bytes(captured["stdout"]).decode("utf-8", "replace"),
                "stderr": bytes(captured["stderr"]).decode("utf-8", "replace"),
            }
        for key, _ in selector.select(remaining):
            chunk = key.fileobj.read(65536)
            if not chunk:
                selector.unregister(key.fileobj)
                key.fileobj.close()
                continue
            stream = key.data
            available = output_limit - len(captured[stream])
            if available > 0:
                captured[stream].extend(chunk[:available])
            if len(chunk) > max(available, 0):
                limited = True
                kill_process_group(process)
                selector.close()
                process.stdout.close()
                process.stderr.close()
                return {
                    "status": "output_limit",
                    "exit_status": process.returncode,
                    "stdout": bytes(captured["stdout"]).decode("utf-8", "replace"),
                    "stderr": bytes(captured["stderr"]).decode("utf-8", "replace"),
                }
    process.wait()
    process.stdout.close()
    process.stderr.close()
    selector.close()
    return {
        "status": "output_limit" if limited else ("success" if process.returncode == 0 else "failed"),
        "exit_status": process.returncode,
        "stdout": bytes(captured["stdout"]).decode("utf-8", "replace"),
        "stderr": bytes(captured["stderr"]).decode("utf-8", "replace"),
    }


def output_info(path):
    if not path.exists() or not path.is_file():
        return {"path": str(path), "exists": False, "size": None, "sha256": None}
    return {"path": str(path), "exists": True, "size": path.stat().st_size, "sha256": sha256_file(path)}


def bounded_binary_run(argv, cwd, timeout, output_limit, cpu_seconds=None, address_space_bytes=None):
    try:
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=sanitized_environment(),
            start_new_session=True,
            preexec_fn=resource_limits(cpu_seconds, address_space_bytes),
        )
    except OSError as error:
        return {"status": "unavailable", "exit_status": None, "data": b"", "stderr": str(error)}

    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ, "stdout")
    selector.register(process.stderr, selectors.EVENT_READ, "stderr")
    data = bytearray()
    stderr = bytearray()
    deadline = time.monotonic() + timeout
    while selector.get_map():
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            kill_process_group(process)
            selector.close()
            return {"status": "timeout", "exit_status": None, "data": bytes(data), "stderr": bytes(stderr).decode("utf-8", "replace")}
        for key, _ in selector.select(remaining):
            chunk = key.fileobj.read(65536)
            if not chunk:
                selector.unregister(key.fileobj)
                key.fileobj.close()
                continue
            if key.data == "stdout":
                available = output_limit - len(data)
                if available > 0:
                    data.extend(chunk[:available])
                if len(chunk) > max(available, 0):
                    kill_process_group(process)
                    selector.close()
                    return {"status": "output_limit", "exit_status": process.returncode, "data": bytes(data), "stderr": bytes(stderr).decode("utf-8", "replace")}
            else:
                available = output_limit - len(stderr)
                if available > 0:
                    stderr.extend(chunk[:available])
    process.wait()
    selector.close()
    return {
        "status": "success" if process.returncode == 0 else "failed",
        "exit_status": process.returncode,
        "data": bytes(data),
        "stderr": bytes(stderr).decode("utf-8", "replace"),
    }


def fixture_input_path(fixture_path, input_path):
    if not isinstance(input_path, str) or not input_path:
        raise ValueError("fixture input must be a non-empty relative path")
    candidate = Path(input_path)
    if candidate.is_absolute() or candidate.anchor:
        raise ValueError("fixture input must be a relative path")
    resolved = (fixture_path.parent / candidate).resolve()
    fixture_root = fixture_path.parent.resolve()
    if resolved != fixture_root and fixture_root not in resolved.parents:
        raise ValueError("fixture input must stay within the fixture directory")
    if not resolved.is_file():
        raise ValueError("fixture input does not exist: {}".format(input_path))
    return resolved


def load_fixture(path):
    with path.open("r", encoding="utf-8") as stream:
        fixture = json.load(stream)
    cases = fixture.get("cases", []) if isinstance(fixture, dict) else fixture
    if not isinstance(cases, list) or not cases:
        raise ValueError("fixture must contain a non-empty cases list")
    normalized = []
    for index, case in enumerate(cases):
        if not isinstance(case, dict) or not isinstance(case.get("args"), list):
            raise ValueError("each fixture case must contain an args list")
        inputs = case.get("inputs", case.get("input", []))
        if isinstance(inputs, str):
            inputs = [inputs]
        if not isinstance(inputs, list):
            raise ValueError("fixture inputs must be a path or list of paths")
        optional = bool(case.get("optional", False))
        if optional and any(not (path.parent / str(input_name)).is_file() for input_name in inputs):
            continue
        probe_packets = case.get("probe_packets", False)
        probe_frames = case.get("probe_frames", False)
        probe_decoded_video = case.get("probe_decoded_video", False)
        probe_decoded_audio = case.get("probe_decoded_audio", False)
        if not all(isinstance(value, bool) for value in (probe_packets, probe_frames, probe_decoded_video, probe_decoded_audio)):
            raise ValueError("fixture probe flags must be boolean")
        tool_args = {}
        for label in ("reference", "candidate"):
            override = case.get("{}_args".format(label))
            if override is not None:
                if not isinstance(override, list):
                    raise ValueError("fixture {}_args must be a list".format(label))
                tool_args[label] = [str(value) for value in override]
        normalized.append({
            "name": str(case.get("name", "case-{}".format(index))),
            "args": [str(value) for value in case["args"]],
            "tool_args": tool_args,
            "inputs": [str(value) for value in inputs],
            "optional": bool(case.get("optional", False)),
            "output": case.get("output"),
            "probe_packets": probe_packets,
            "probe_frames": probe_frames,
            "probe_decoded_video": probe_decoded_video,
            "probe_decoded_audio": probe_decoded_audio,
        })
    return normalized


def prepare_inputs(fixture_path, invocation_dir, inputs):
    replacements = {}
    for input_name in inputs:
        source = fixture_input_path(fixture_path, input_name)
        target = invocation_dir / source.name
        if target.exists() and target.resolve() != source:
            raise ValueError("fixture inputs must have unique file names")
        shutil.copy2(source, target)
        replacements[input_name] = str(target)
    return replacements


def rewrite_input_args(args, replacements):
    return [replacements.get(argument, argument) for argument in args]


def parse_rational(value):
    if value is None or value == "N/A":
        return None
    if isinstance(value, int):
        return {"numerator": value, "denominator": 1}
    text = str(value).strip()
    if not text:
        return None
    try:
        rational = Fraction(text)
    except (ValueError, ZeroDivisionError):
        return None
    return {"numerator": rational.numerator, "denominator": rational.denominator}


def parse_number(value):
    if value is None or value == "N/A":
        return None
    try:
        return float(value)
    except (TypeError, ValueError):
        return None


def parse_integer(value):
    if value is None or value == "N/A":
        return None
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def normalized_probe(document):
    if not isinstance(document, dict):
        return None
    format_data = document.get("format") or {}
    streams = []
    for stream in document.get("streams") or []:
        streams.append({
            "index": parse_integer(stream.get("index")),
            "codec_type": stream.get("codec_type"),
            "duration": parse_number(stream.get("duration")),
            "duration_ts": parse_integer(stream.get("duration_ts")),
            "sample_rate": parse_integer(stream.get("sample_rate")),
            "channels": parse_integer(stream.get("channels")),
            "r_frame_rate": parse_rational(stream.get("r_frame_rate")),
            "avg_frame_rate": parse_rational(stream.get("avg_frame_rate")),
            "time_base": parse_rational(stream.get("time_base")),
            "start_time": parse_number(stream.get("start_time")),
            "nb_frames": parse_integer(stream.get("nb_frames")),
            "color_space": stream.get("color_space"),
            "color_range": stream.get("color_range"),
            "color_primaries": stream.get("color_primaries"),
            "color_transfer": stream.get("color_transfer"),
            "color_matrix": stream.get("color_matrix"),
            "chroma_location": stream.get("chroma_location"),
            "pix_fmt": stream.get("pix_fmt"),
            "width": parse_integer(stream.get("width")),
            "height": parse_integer(stream.get("height")),
        })
    return {
        "format": {
            "duration": parse_number(format_data.get("duration")),
            "start_time": parse_number(format_data.get("start_time")),
        },
        "streams": streams,
    }


def _comparison_field(reference, candidate, tolerance=None):
    if reference is None or candidate is None:
        return {"status": "missing", "reference": reference, "candidate": candidate}
    if tolerance is None:
        passed = reference == candidate
    else:
        passed = abs(reference - candidate) <= tolerance
    return {
        "status": "pass" if passed else "fail",
        "reference": reference,
        "candidate": candidate,
        **({"tolerance": tolerance} if tolerance is not None else {}),
    }


def compare_timing_probes(reference, candidate, duration_tolerance=0.001):
    if reference is None or candidate is None:
        return {
            "status": "unavailable",
            "fields": {},
            "diagnostics": {"start_time": [], "color": []},
        }

    fields = {}
    failures = []
    reference_format = reference.get("format") or {}
    candidate_format = candidate.get("format") or {}
    duration = _comparison_field(
        reference_format.get("duration"), candidate_format.get("duration"), duration_tolerance
    )
    fields["format.duration"] = duration
    if duration["status"] == "fail":
        failures.append("format.duration")

    reference_streams = reference.get("streams") or []
    candidate_streams = candidate.get("streams") or []
    candidate_by_key = {
        (stream.get("index"), stream.get("codec_type")): stream for stream in candidate_streams
    }
    timing_names = ("duration", "r_frame_rate", "avg_frame_rate", "nb_frames", "time_base")
    diagnostics = {"start_time": [], "color": []}
    format_start_time = _comparison_field(
        reference_format.get("start_time"), candidate_format.get("start_time")
    )
    if format_start_time["status"] == "fail":
        diagnostics["start_time"].append({"field": "format.start_time", **format_start_time})
    color_names = (
        "color_space",
        "color_range",
        "color_primaries",
        "color_transfer",
        "color_matrix",
        "chroma_location",
        "pix_fmt",
    )
    for reference_stream in reference_streams:
        key = (reference_stream.get("index"), reference_stream.get("codec_type"))
        candidate_stream = candidate_by_key.get(key)
        stream_name = "stream[{}:{}]".format(key[0], key[1])
        for name in timing_names:
            field = _comparison_field(
                reference_stream.get(name),
                candidate_stream.get(name) if candidate_stream else None,
                duration_tolerance if name == "duration" else None,
            )
            fields["{}.{}".format(stream_name, name)] = field
            if field["status"] == "fail":
                failures.append("{}.{}".format(stream_name, name))
        start_time = _comparison_field(
            reference_stream.get("start_time"),
            candidate_stream.get("start_time") if candidate_stream else None,
        )
        if start_time["status"] == "fail":
            diagnostics["start_time"].append({"field": stream_name, **start_time})
        for name in color_names:
            color = _comparison_field(
                reference_stream.get(name),
                candidate_stream.get(name) if candidate_stream else None,
            )
            if color["status"] != "pass":
                diagnostics["color"].append({"field": "{}.{}".format(stream_name, name), **color})

    return {
        "status": "fail" if failures else "pass",
        "fields": fields,
        "failures": failures,
        "diagnostics": diagnostics,
    }


def normalized_timestamp_summary(document, item_type=None):
    if not isinstance(document, dict):
        return None
    if "packets_and_frames" in document:
        items = document.get("packets_and_frames") or []
    elif item_type == "packet":
        items = document.get("packets") or []
    elif item_type == "frame":
        items = document.get("frames") or []
    else:
        items = document.get("packets") or document.get("frames") or []
    timestamps = []
    for item in items:
        if not isinstance(item, dict) or (item_type and item.get("type") != item_type):
            continue
        values = {
            "pts_time": parse_number(item.get("pts_time", item.get("best_effort_timestamp_time"))),
            "dts_time": parse_number(item.get("dts_time")),
            "duration_time": parse_number(item.get("duration_time", item.get("pkt_duration_time"))),
        }
        if any(value is not None for value in values.values()):
            timestamps.append(values)
    return {
        "count": len(timestamps),
        "first_pts_time": timestamps[0]["pts_time"] if timestamps else None,
        "last_pts_time": timestamps[-1]["pts_time"] if timestamps else None,
        "first_dts_time": timestamps[0]["dts_time"] if timestamps else None,
        "last_dts_time": timestamps[-1]["dts_time"] if timestamps else None,
        "duration_time": sum(
            value["duration_time"] for value in timestamps if value["duration_time"] is not None
        ) if timestamps else None,
    }


def probe_output(ffprobe, output, cwd, timeout, output_limit):
    if not ffprobe:
        return {"status": "unavailable", "reason": "no --ffprobe supplied"}
    if not output["exists"]:
        return {"status": "unavailable", "reason": "output does not exist"}
    result = bounded_run(
        [ffprobe, "-v", "error", "-show_format", "-show_streams", "-of", "json", output["path"]],
        cwd,
        timeout,
        output_limit,
    )
    record = {
        "status": result["status"],
        "exit_status": result["exit_status"],
        "stdout": result["stdout"],
        "stderr": result["stderr"],
    }
    if result["status"] == "success":
        try:
            raw = json.loads(result["stdout"])
        except json.JSONDecodeError:
            record["normalized"] = None
        else:
            record["raw"] = raw
            record["normalized"] = normalized_probe(raw)
    return record


def probe_timestamps(ffprobe, output, cwd, timeout, output_limit, probe_packets, probe_frames=False):
    if not probe_packets and not probe_frames:
        return {"status": "disabled"}
    if not ffprobe:
        return {"status": "unavailable", "reason": "no --ffprobe supplied"}
    if not output["exists"]:
        return {"status": "unavailable", "reason": "output does not exist"}
    show_flags = []
    if probe_packets:
        show_flags.append("-show_packets")
    if probe_frames:
        show_flags.append("-show_frames")
    result = bounded_run(
        [ffprobe, "-v", "error", *show_flags, "-of", "json", output["path"]],
        cwd,
        timeout,
        output_limit,
    )
    record = {
        "status": result["status"],
        "exit_status": result["exit_status"],
        "stdout": result["stdout"],
        "stderr": result["stderr"],
    }
    if result["status"] == "success":
        try:
            raw = json.loads(result["stdout"])
        except json.JSONDecodeError:
            record["normalized"] = None
        else:
            record["normalized"] = {
                "packets": normalized_timestamp_summary(raw, "packet") if probe_packets else None,
                "frames": normalized_timestamp_summary(raw, "frame") if probe_frames else None,
            }
    return record


def decoded_probe(ffmpeg, output, normalized, cwd, timeout, output_limit, media_type, enabled, output_status="success", cpu_seconds=None, address_space_bytes=None):
    if not enabled:
        return {"status": "disabled"}
    if output_status != "success":
        return {"status": "unavailable", "reason": "command did not succeed"}
    if not ffmpeg:
        return {"status": "unavailable", "reason": "no ffmpeg supplied"}
    if not output["exists"]:
        return {"status": "unavailable", "reason": "output does not exist"}
    streams = [stream for stream in (normalized or {}).get("streams", []) if stream.get("codec_type") == media_type]
    if not streams:
        return {"status": "unavailable", "reason": "no {} stream".format(media_type)}
    stream = streams[0]
    if media_type == "video":
        width, height = stream.get("width"), stream.get("height")
        if not width or not height:
            return {"status": "unavailable", "reason": "video dimensions unavailable"}
        pixel_format = "yuv420p"
        bytes_per_frame = width * height * 3 // 2
        argv = [ffmpeg, "-v", "error", "-i", output["path"], "-map", "0:v:0", "-f", "rawvideo", "-pix_fmt", pixel_format, "pipe:1"]
    else:
        channels = stream.get("channels")
        if not channels:
            return {"status": "unavailable", "reason": "audio channel count unavailable"}
        bytes_per_sample = channels * 2
        argv = [ffmpeg, "-v", "error", "-i", output["path"], "-map", "0:a:0", "-f", "s16le", "-acodec", "pcm_s16le", "pipe:1"]
    result = bounded_binary_run(argv, cwd, timeout, output_limit, cpu_seconds, address_space_bytes)
    record = {
        "status": result["status"],
        "exit_status": result["exit_status"],
        "byte_count": len(result["data"]),
        "sha256": hashlib.sha256(result["data"]).hexdigest(),
        "stderr": result["stderr"],
        "_data": result["data"],
    }
    if result["status"] == "success":
        record["sample_count" if media_type == "audio" else "frame_count"] = len(result["data"]) // (bytes_per_sample if media_type == "audio" else bytes_per_frame)
    return record


def compare_decoded_buffers(reference, candidate):
    if reference.get("status") != "success" or candidate.get("status") != "success":
        return {"status": "unavailable"}
    reference_data = reference.get("_data", b"")
    candidate_data = candidate.get("_data", b"")
    comparison = {
        "status": "diagnostic",
        "byte_count_equal": len(reference_data) == len(candidate_data),
        "max_absolute_byte_difference": None,
    }
    if len(reference_data) == len(candidate_data):
        comparison["max_absolute_byte_difference"] = max(
            (abs(reference_byte - candidate_byte) for reference_byte, candidate_byte in zip(reference_data, candidate_data)),
            default=0,
        )
    return comparison


def run_fixture(
    reference,
    candidate,
    ffprobe,
    fixture_path,
    output_dir,
    timeout=DEFAULT_TIMEOUT,
    output_limit=DEFAULT_OUTPUT_LIMIT,
    cpu_seconds=None,
    address_space_bytes=None,
):
    cases = load_fixture(fixture_path)
    output_dir.mkdir(parents=True, exist_ok=True)
    records = []
    with tempfile.TemporaryDirectory(prefix="differential-") as temp_dir:
        root = Path(temp_dir)
        for case in cases:
            case_dir = root / case["name"]
            case_dir.mkdir()
            for label, executable in (("reference", reference), ("candidate", candidate)):
                invocation_dir = case_dir / label
                invocation_dir.mkdir()
                replacements = prepare_inputs(fixture_path, invocation_dir, case["inputs"])
                case_output_path = fixture_output_path(invocation_dir, case["output"])
                case_args = case["tool_args"].get(label, case["args"])
                argv = [executable] + rewrite_input_args(case_args, replacements)
                result = bounded_run(argv, invocation_dir, timeout, output_limit, cpu_seconds, address_space_bytes)
                output = output_info(case_output_path)
                record = {
                    "name": case["name"],
                    "tool": label,
                    "command": argv,
                    "executable": executable_info(executable),
                    "exit_status": result["exit_status"],
                    "status": result["status"],
                    "stdout": result["stdout"],
                    "stderr": result["stderr"],
                    "output": output,
                    "probe": probe_output(ffprobe, output, invocation_dir, timeout, output_limit),
                    "timestamp_probe": probe_timestamps(
                        ffprobe,
                        output,
                        invocation_dir,
                        timeout,
                        output_limit,
                        case["probe_packets"],
                        case["probe_frames"],
                    ),
                }
                normalized = record["probe"].get("normalized")
                record["decoded_video_probe"] = decoded_probe(
                    reference,
                    output,
                    normalized,
                    invocation_dir,
                    timeout,
                    output_limit,
                    "video",
                    case["probe_decoded_video"],
                    result["status"],
                    cpu_seconds,
                    address_space_bytes,
                )
                record["decoded_audio_probe"] = decoded_probe(
                    reference,
                    output,
                    normalized,
                    invocation_dir,
                    timeout,
                    output_limit,
                    "audio",
                    case["probe_decoded_audio"],
                    result["status"],
                    cpu_seconds,
                    address_space_bytes,
                )
                records.append(record)
    comparisons = []
    for case in cases:
        case_records = [record for record in records if record["name"] == case["name"]]
        probes = {
            record["tool"]: record["probe"].get("normalized")
            for record in case_records
            if record["probe"].get("status") == "success"
        }
        comparison = compare_timing_probes(probes.get("reference"), probes.get("candidate"))
        decoded = {}
        for media_type, key in (("video", "decoded_video_probe"), ("audio", "decoded_audio_probe")):
            decoded[media_type] = compare_decoded_buffers(
                next((record[key] for record in case_records if record["tool"] == "reference"), {"status": "unavailable"}),
                next((record[key] for record in case_records if record["tool"] == "candidate"), {"status": "unavailable"}),
            )
        comparisons.append({"name": case["name"], "comparison": comparison, "decoded": decoded})
    public_records = []
    for record in records:
        public_record = dict(record)
        public_record["decoded_video_probe"] = {key: value for key, value in record["decoded_video_probe"].items() if key != "_data"}
        public_record["decoded_audio_probe"] = {key: value for key, value in record["decoded_audio_probe"].items() if key != "_data"}
        public_records.append(public_record)
    document = {
        "schema_version": "1.0",
        "capture_only": True,
        "media_equivalence_claim": False,
        "fixture": str(fixture_path.resolve()),
        "limits": {"timeout_seconds": timeout, "output_bytes": output_limit, "cpu_seconds": cpu_seconds, "address_space_bytes": address_space_bytes},
        "environment_policy": ENVIRONMENT_POLICY,
        "records": public_records,
        "comparisons": comparisons,
    }
    destination = output_dir / "results.json"
    destination.write_text(json.dumps(document, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return destination


def build_parser():
    parser = argparse.ArgumentParser(description="Capture bounded reference/candidate command results.")
    parser.add_argument("--reference-ffmpeg", required=True)
    parser.add_argument("--candidate", required=True)
    parser.add_argument("--fixture", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--ffprobe")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--output-limit", type=int, default=DEFAULT_OUTPUT_LIMIT)
    parser.add_argument("--cpu-seconds", type=int)
    parser.add_argument("--address-space-bytes", type=int)
    return parser


def main(argv=None):
    args = build_parser().parse_args(argv)
    if args.timeout <= 0 or args.output_limit <= 0:
        raise SystemExit("--timeout and --output-limit must be positive")
    if args.cpu_seconds is not None and args.cpu_seconds <= 0:
        raise SystemExit("--cpu-seconds must be positive")
    if args.address_space_bytes is not None and args.address_space_bytes <= 0:
        raise SystemExit("--address-space-bytes must be positive")
    try:
        destination = run_fixture(
            args.reference_ffmpeg,
            args.candidate,
            args.ffprobe,
            args.fixture,
            args.output_dir,
            args.timeout,
            args.output_limit,
            args.cpu_seconds,
            args.address_space_bytes,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
