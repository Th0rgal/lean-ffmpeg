#!/usr/bin/env python3
"""FATE TARGET_EXEC adapter: replace exactly the pinned ffmpeg executable.

Other upstream helpers run unchanged and are traced as reference-only. Their
passing results do not establish candidate library/API coverage.
"""
import json
import os
from pathlib import Path
import sys
import time


def main():
    required = ("FATE_REFERENCE_FFMPEG", "FATE_CANDIDATE", "FATE_EXEC_TRACE")
    if len(sys.argv) < 2 or any(not os.environ.get(k) for k in required):
        sys.exit("FATE adapter requires a target and explicit reference/candidate/trace paths")
    requested = Path(sys.argv[1]).resolve()
    reference = Path(os.environ[required[0]]).resolve(strict=True)
    candidate = Path(os.environ[required[1]]).resolve(strict=True)
    if reference == candidate:
        sys.exit("FATE reference and candidate must be distinct")
    replaced = requested == reference
    actual = candidate if replaced else requested
    record = {"requested": str(requested), "executed": str(actual),
              "candidate_exercised": replaced, "argv": sys.argv[2:],
              "test": os.environ.get("FATE_CASE_NAME"), "pid": os.getpid(),
              "cwd": os.getcwd(), "timestamp_ns": time.time_ns()}
    # One append per invocation; parallel FATE runs retain complete trace lines.
    fd = os.open(os.environ[required[2]], os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        payload = (json.dumps(record) + "\n").encode()
        if os.write(fd, payload) != len(payload):
            raise OSError("short trace write")
    finally:
        os.close(fd)
    env = dict(os.environ, LEANAV_FFMPEG_BIN=str(reference))
    os.execve(actual, [str(actual), *sys.argv[2:]], env)


if __name__ == "__main__":
    main()
