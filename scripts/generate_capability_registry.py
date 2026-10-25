#!/usr/bin/env python3
"""Generate a provenance-aware FFmpeg capability inventory."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from pathlib import Path
from typing import Any

SCHEMA_VERSION = "1.1"
COMMAND_TIMEOUT_SECONDS = 15
MAX_OUTPUT_BYTES = 1024 * 1024
OUTPUT_POLICY = f"stdout/stderr capped at {MAX_OUTPUT_BYTES} bytes each"
LOCALE = "C"
DOMAINS = (
    "codecs",
    "encoders",
    "decoders",
    "formats",
    "demuxers",
    "muxers",
    "filters",
    "protocols",
    "bsfs",
    "pix_fmts",
    "sample_fmts",
    "layouts",
    "hwaccels",
    "devices",
    "dispositions",
    "colors",
)


def _sha256(path: Path) -> str | None:
    try:
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        return digest.hexdigest()
    except (OSError, ValueError):
        return None


def resolve_executable(value: str) -> dict[str, Any]:
    requested = os.path.abspath(value)
    resolved = shutil.which(value) or (requested if os.access(requested, os.X_OK) else None)
    result: dict[str, Any] = {
        "requested": value,
        "resolved": os.path.realpath(resolved) if resolved else None,
        "exists": bool(resolved),
        "sha256": None,
        "hash_path": None,
        "kind": None,
    }
    if not resolved:
        return result
    path = Path(os.path.realpath(resolved))
    result["hash_path"] = str(path)
    result["sha256"] = _sha256(path)
    try:
        with path.open("rb") as handle:
            data = handle.read(4)
    except OSError:
        data = b""
    if data.startswith(b"\x7fELF") or data.startswith(b"\xcf\xfa\xed\xfe") or data.startswith(b"\xfe\xed\xfa\xcf") or data.startswith(b"MZ"):
        result["kind"] = "binary"
    elif data.startswith(b"#!"):
        result["kind"] = "wrapper"
    else:
        result["kind"] = "unknown"
    return result


def _command_environment() -> dict[str, str]:
    return {"PATH": os.environ.get("PATH", os.defpath), "LANG": LOCALE, "LC_ALL": LOCALE, "LC_CTYPE": LOCALE}


def _bounded_reader(stream: Any, limit: int, chunks: list[bytes], truncated: list[bool]) -> None:
    remaining = limit
    while True:
        chunk = stream.read(min(65536, remaining + 1))
        if not chunk:
            break
        if len(chunk) > remaining:
            chunks.append(chunk[:remaining])
            truncated[0] = True
            break
        chunks.append(chunk)
        remaining -= len(chunk)
        if remaining == 0:
            extra = stream.read(1)
            if extra:
                truncated[0] = True
            break


def run(argv: list[str]) -> dict[str, Any]:
    record: dict[str, Any] = {"argv": argv, "ok": False, "returncode": None, "stdout": "", "stderr": "", "error": None, "output_truncated": False}
    process: subprocess.Popen[bytes] | None = None
    with tempfile.TemporaryDirectory(prefix="ffmpeg-capabilities-") as cwd:
        try:
            process = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd, env=_command_environment(), start_new_session=True)
            stdout_chunks: list[bytes] = []
            stderr_chunks: list[bytes] = []
            stdout_truncated = [False]
            stderr_truncated = [False]
            stdout_thread = threading.Thread(target=_bounded_reader, args=(process.stdout, MAX_OUTPUT_BYTES, stdout_chunks, stdout_truncated), daemon=True)
            stderr_thread = threading.Thread(target=_bounded_reader, args=(process.stderr, MAX_OUTPUT_BYTES, stderr_chunks, stderr_truncated), daemon=True)
            stdout_thread.start()
            stderr_thread.start()
            try:
                process.wait(timeout=COMMAND_TIMEOUT_SECONDS)
            except subprocess.TimeoutExpired:
                if hasattr(os, "killpg"):
                    os.killpg(process.pid, signal.SIGKILL)
                else:
                    process.kill()
                process.wait()
                record["error"] = "TimeoutExpired"
            stdout_thread.join()
            stderr_thread.join()
            record["stdout"] = b"".join(stdout_chunks).decode("utf-8", errors="replace")
            record["stderr"] = b"".join(stderr_chunks).decode("utf-8", errors="replace")
            record["output_truncated"] = stdout_truncated[0] or stderr_truncated[0]
            record["returncode"] = process.returncode
            record["ok"] = record["error"] is None and process.returncode == 0
            if process.returncode != 0 and record["error"] is None:
                record["error"] = "nonzero_exit"
        except OSError as exc:
            record["error"] = type(exc).__name__
    if record["error"] == "TimeoutExpired":
        record["stderr"] = "command timed out"
    return record


def _description(text: str) -> str:
    return " ".join(text.strip().split())


_FLAGGED_DOMAINS = {"codecs", "encoders", "decoders", "formats", "demuxers", "muxers", "filters", "devices", "pix_fmts"}
_UNFLAGGED_DOMAINS = {"protocols", "bsfs", "dispositions", "sample_fmts", "hwaccels", "layouts", "colors"}
_DOMAIN_HEADERS = {
    "codecs": "Codecs:", "encoders": "Encoders:", "decoders": "Decoders:", "formats": "File formats:",
    "demuxers": "File formats:", "muxers": "File formats:", "filters": "Filters:", "protocols": "Supported file protocols:",
    "bsfs": "Bitstream filters:", "devices": "Devices:", "dispositions": "Dispositions:", "pix_fmts": "Pixel formats:",
    "sample_fmts": "Sample formats:", "hwaccels": "Hardware acceleration methods:", "layouts": "Standard channel layouts:", "colors": "Color names:",
}


def _listing_lines(text: str, domain: str) -> list[str]:
    header = _DOMAIN_HEADERS.get(domain)
    aliases = {header} if header else set()
    if domain == "formats":
        aliases.add("Formats:")
    lines = text.splitlines()
    known_headers = set(_DOMAIN_HEADERS.values()) | {"Formats:"}
    if any(line.strip() in known_headers - aliases for line in lines):
        return []
    if aliases:
        header_index = next((index for index, line in enumerate(lines) if line.strip() in aliases), None)
        if header_index is not None:
            lines = lines[header_index + 1:]
    return lines


def parse_listing(text: str, domain: str) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    seen: set[str] = set()
    for raw in _listing_lines(text, domain):
        line = raw.strip("\r")
        if not line.strip() or line.strip().startswith(("--", "Legend:", "File formats", "Codecs:", "Encoders:", "Decoders:", "Filters:", "Supported file protocols:", "Bitstream filters:", "Devices:", "Dispositions:", "Pixel formats:", "Sample formats:", "Hardware acceleration methods:", "Standard channel layouts:", "Color names:")):
            continue
        if domain in _FLAGGED_DOMAINS:
            match = re.match(r"^\s*([A-Z. ]{2,8})\s+([A-Za-z0-9_.+:-]+)(?:\s+(.*?))?\s*$", line)
            if not match:
                continue
            flags, name, description = match.groups()
            flags = flags.replace(" ", "")
        elif domain in _UNFLAGGED_DOMAINS:
            match = re.match(r"^\s*([A-Za-z0-9_.+:-]+)(?:\s+(.*?))?\s*$", line)
            if not match:
                continue
            flags, name, description = "", match.group(1), match.group(2)
            if domain == "sample_fmts" and not re.fullmatch(r"(?:u8|s16|s32|s64|flt|dbl|u24|s24)", name):
                continue
            if domain == "protocols" and name not in {"file", "pipe", "http", "https", "tcp", "udp", "rtmp", "rtsp", "crypto", "concat", "data", "fd", "ftp", "gopher", "hls", "httpproxy", "icecast", "ipfs", "ipns", "md5", "mmsh", "mmst", "prompeg", "sctp", "srt", "subfile", "telnet", "tls", "udp", "unix", "amqp", "async", "bluray", "cache", "concatf", "http+unix", "libsrt", "rist", "sftp", "zmq"}:
                continue
        else:
            continue
        if name in seen or name.lower() in {"name", "format", "codec", "filter", "protocol", "device", "pixel", "sample", "version", "configuration", "input", "output", "built", "with"}:
            continue
        seen.add(name)
        entry: dict[str, Any] = {"name": name, "inventory_only": True}
        if flags:
            entry["flags"] = flags
        if description:
            entry["description"] = _description(description)
        entries.append(entry)
    return entries


def command_inventory(executable: str, domain: str) -> dict[str, Any]:
    option = domain if domain in {"pix_fmts", "sample_fmts"} else domain.replace("_", "-")
    result = run([executable, f"-{option}"])
    listing = parse_listing(result["stdout"] + result["stderr"], domain) if result["ok"] else []
    status = "complete" if result["ok"] and listing else "empty" if result["ok"] else "failed"
    return {"status": status, "complete": status == "complete", "entries": listing, "command": {key: value for key, value in result.items() if key not in {"stdout", "stderr"}}, "stderr": result["stderr"] if result["stderr"] else None}


def validate_inventory_boundaries(registry: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    declared = registry.get("declared_ffmpeg_capabilities")
    if not isinstance(declared, dict):
        return ["declared_ffmpeg_capabilities is not an object"]
    if set(declared) != set(DOMAINS):
        errors.append("declared domains do not match DOMAINS")
    for domain in DOMAINS:
        record = declared.get(domain)
        if not isinstance(record, dict):
            errors.append(f"{domain} is not an inventory record")
            continue
        status = record.get("status")
        entries = record.get("entries")
        if status not in {"complete", "empty", "failed"}:
            errors.append(f"{domain} has invalid status")
        if record.get("complete") != (status == "complete"):
            errors.append(f"{domain} complete flag disagrees with status")
        if not isinstance(entries, list):
            errors.append(f"{domain} entries are not a list")
            continue
        names = [entry.get("name") for entry in entries if isinstance(entry, dict)]
        if len(names) != len(entries) or any(not isinstance(name, str) or not name for name in names):
            errors.append(f"{domain} contains malformed entries")
        if len(set(names)) != len(names):
            errors.append(f"{domain} contains duplicate entries")
        if any(entry.get("inventory_only") is not True for entry in entries if isinstance(entry, dict)):
            errors.append(f"{domain} contains entries without inventory_only")
        if status != "complete" and entries:
            errors.append(f"{domain} has entries despite incomplete status")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ffmpeg", required=True)
    parser.add_argument("--ffprobe", required=True)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)

    ffmpeg = resolve_executable(args.ffmpeg)
    ffprobe = resolve_executable(args.ffprobe)
    ffmpeg_version = run([args.ffmpeg, "-version"])
    ffmpeg_buildconf = run([args.ffmpeg, "-buildconf"])
    ffprobe_version = run([args.ffprobe, "-version"])
    ffprobe_buildconf = run([args.ffprobe, "-buildconf"])
    domains = {domain: command_inventory(args.ffmpeg, domain) for domain in DOMAINS}
    failed = [name for name, record in {"ffmpeg_version": ffmpeg_version, "ffmpeg_buildconf": ffmpeg_buildconf, "ffprobe_version": ffprobe_version, "ffprobe_buildconf": ffprobe_buildconf}.items() if not record["ok"]]
    failed.extend(f"ffmpeg_{domain}" for domain, record in domains.items() if record["status"] not in {"complete", "empty"})
    registry = {
        "schema_version": SCHEMA_VERSION,
        "generated_by": "scripts/generate_capability_registry.py",
        "provenance": {
            "platform": {"system": platform.system(), "release": platform.release(), "machine": platform.machine(), "python": platform.python_version()},
            "generator_source_sha256": _sha256(Path(__file__).resolve()),
            "cwd_policy": "isolated temporary directory per subprocess",
            "locale": LOCALE,
            "timeout_seconds": COMMAND_TIMEOUT_SECONDS,
            "output_policy": OUTPUT_POLICY,
            "ffmpeg": ffmpeg,
            "ffprobe": ffprobe,
            "commands": {"ffmpeg_version": {key: value for key, value in ffmpeg_version.items() if key not in {"stdout", "stderr"}}, "ffmpeg_buildconf": {key: value for key, value in ffmpeg_buildconf.items() if key not in {"stdout", "stderr"}}, "ffprobe_version": {key: value for key, value in ffprobe_version.items() if key not in {"stdout", "stderr"}}, "ffprobe_buildconf": {key: value for key, value in ffprobe_buildconf.items() if key not in {"stdout", "stderr"}}},
            "version_output": {"ffmpeg": ffmpeg_version["stdout"], "ffprobe": ffprobe_version["stdout"]},
            "buildconf_output": {"ffmpeg": ffmpeg_buildconf["stdout"], "ffprobe": ffprobe_buildconf["stdout"]},
        },
        "declared_ffmpeg_capabilities": domains,
        "tested_lean_ffmpeg_capabilities": {"status": "untested", "entries": [], "evidence": []},
        "generation": {"status": "ok" if not failed else "failed", "failed_commands": failed},
    }
    boundary_errors = validate_inventory_boundaries(registry)
    if boundary_errors:
        failed.extend(f"inventory_boundary:{error}" for error in boundary_errors)
        registry["generation"] = {"status": "failed", "failed_commands": failed}
    registry["inventory_boundary"] = {"status": "pass" if not boundary_errors else "fail", "errors": boundary_errors}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(registry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
