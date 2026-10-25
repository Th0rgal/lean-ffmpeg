#!/usr/bin/env python3
import argparse
import os
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
DEFAULT_FFMPEG = Path("/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg")
DEFAULT_OUTPUT = Path(__file__).resolve().parent / "input-av.mp4"


def run_ffmpeg(ffmpeg, environment, arguments):
    subprocess.run([str(ffmpeg), "-hide_banner", "-v", "error", "-y", *arguments], env=environment, check=True)


def supports(ffmpeg, environment, listing, value):
    result = subprocess.run(
        [str(ffmpeg), "-hide_banner", listing],
        env=environment,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    return value in result.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ffmpeg", type=Path, default=DEFAULT_FFMPEG)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    if str(args.ffmpeg).endswith("ffmpeg-runtime-full/bin/ffmpeg"):
        library_paths = [
            Path("/tmp/opencode/ffmpeg-runtime-full/lib"),
            Path("/tmp/opencode/ffmpeg-runtime-full/root/usr/lib/x86_64-linux-gnu"),
            Path("/tmp/opencode/ffmpeg-runtime-full/root/usr/lib"),
        ]
    else:
        library_paths = [
            ROOT / ".tools" / "ffmpeg-pkg" / "usr" / "lib" / "x86_64-linux-gnu",
            ROOT / ".tools" / "ffmpeg-pkg" / "lib" / "x86_64-linux-gnu",
            Path("/usr/lib/x86_64-linux-gnu"),
        ]
    environment["LD_LIBRARY_PATH"] = os.pathsep.join(
        [str(path) for path in library_paths] + [environment.get("LD_LIBRARY_PATH", "")]
    ).rstrip(os.pathsep)
    command = [
        str(args.ffmpeg),
        "-hide_banner",
        "-v",
        "error",
        "-y",
        "-f",
        "lavfi",
        "-i",
        "testsrc=size=32x32:rate=25:duration=2",
        "-f",
        "lavfi",
        "-i",
        "sine=frequency=440:sample_rate=48000:duration=2",
        "-map",
        "0:v:0",
        "-map",
        "1:a:0",
        "-c:v",
        "libx264",
        "-preset",
        "ultrafast",
        "-pix_fmt",
        "yuv420p",
        "-c:a",
        "aac",
        "-b:a",
        "64k",
        "-ac",
        "1",
        "-threads",
        "1",
        "-map_metadata",
        "-1",
        "-movflags",
        "+faststart",
        str(args.output),
    ]
    subprocess.run(command, env=environment, check=True)

    fixture_dir = args.output.parent
    vfr_output = fixture_dir / "input-vfr.mp4"
    run_ffmpeg(args.ffmpeg, environment, [
        "-f", "lavfi",
        "-i", "testsrc=size=32x32:rate=30:duration=1",
        "-vf", "select='not(eq(mod(n,3),2))'",
        "-fps_mode", "vfr",
        "-c:v", "libx264",
        "-preset", "ultrafast",
        "-bf", "2",
        "-g", "30",
        "-pix_fmt", "yuv420p",
        "-threads", "1",
        "-map_metadata", "-1",
        "-movflags", "+faststart",
        str(vfr_output),
    ])

    if supports(args.ffmpeg, environment, "-encoders", "libx264") and supports(
        args.ffmpeg, environment, "-pix_fmts", "yuv444p10le"
    ):
        run_ffmpeg(args.ffmpeg, environment, [
            "-f", "lavfi",
            "-i", "testsrc=size=32x32:rate=25:duration=1",
            "-c:v", "libx264",
            "-preset", "ultrafast",
            "-profile:v", "high444",
            "-pix_fmt", "yuv444p10le",
            "-threads", "1",
            "-map_metadata", "-1",
            "-movflags", "+faststart",
            str(fixture_dir / "input-yuv444.mp4"),
        ])


if __name__ == "__main__":
    main()
