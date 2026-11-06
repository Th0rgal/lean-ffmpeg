#!/usr/bin/env python3
"""Build lean-ffmpeg without invoking the lake executable."""
import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_SYS = ROOT.parent / "lean-sys"
BUILD = ROOT / ".lake" / "build"
LEAN_SYS_BUILD = LEAN_SYS / ".lake" / "build"
IMPORT_RE = re.compile(r"^\s*(?:public\s+|meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)")


def run(cmd, cwd=None, env=None):
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, env=env, check=True)


def toolchain_prefix():
    return Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())


def cpu_flags(kind):
    if platform.machine() in {"aarch64", "arm64"}:
        return []
    try:
        text = Path("/proc/cpuinfo").read_text()
    except OSError:
        text = ""
    flags = set(text.split())
    if "avx2" in flags:
        base = ["-mavx2", "-mfma", "-mpopcnt", "-mf16c"]
        return base + (["-mpclmul"] if kind == "lnir" else [])
    out = ["-msse4.2"] + (["-mpclmul"] if kind == "lnir" else [])
    for token, option in (("avx", "-mavx"), ("popcnt", "-mpopcnt"), ("f16c", "-mf16c")):
        if token in flags:
            out.append(option)
    return out


def compile_object(compiler, source, output, flags):
    output.parent.mkdir(parents=True, exist_ok=True)
    run([compiler, "-c", "-o", str(output), str(source), *flags])


def archive(output, objects):
    output.parent.mkdir(parents=True, exist_ok=True)
    archiver = shutil.which("llvm-ar") or shutil.which("ar")
    if archiver is None:
        raise RuntimeError("llvm-ar or ar is required")
    run([archiver, "rcs", str(output), *[str(item) for item in objects]])


def build_externals(prefix):
    include = ["-I", str(prefix / "include"), "-I", str(ROOT / "c")]
    common = ["-O3", "-fPIC", "-Wno-deprecated-declarations"]
    compile_object("cc", ROOT / "c" / "leanav_simd_kernels.c",
                   BUILD / "c" / "leanav_simd_kernels.o",
                   include + common + cpu_flags("simd"))
    ll_name = "leanav_lnir_arm64.ll" if platform.machine() in {"aarch64", "arm64"} else "leanav_lnir_x86_64.ll"
    clang = prefix / "bin" / "clang"
    if not clang.is_file():
        clang = Path(shutil.which("clang") or "clang")
    compile_object(str(clang), ROOT / "c" / ll_name,
                   BUILD / "c" / "leanav_lnir_kernels.o",
                   ["-O3", "-fPIC", "-Wno-override-module", *cpu_flags("lnir")])
    archive(BUILD / "lib" / "libleanav_dsp.a",
            [BUILD / "c" / "leanav_simd_kernels.o", BUILD / "c" / "leanav_lnir_kernels.o"])
    compile_object("cc", ROOT / "c" / "leanav_simd_kernels.c",
                   BUILD / "c" / "leanav_zero_exec_stub.o",
                   include + ["-DLEANAV_ZERO_EXEC_STUB_ONLY", "-O3", "-fPIC"])
    shim = LEAN_SYS / "c" / "lean_sys_shim.c"
    if shim.is_file():
        compile_object("cc", shim, LEAN_SYS_BUILD / "c" / "lean_sys_shim.o",
                       ["-I", str(prefix / "include"), "-O3", "-fPIC"])
        archive(LEAN_SYS_BUILD / "lib" / "liblean_sys_shim.a",
                [LEAN_SYS_BUILD / "c" / "lean_sys_shim.o"])


def module_objects(base, exclude=()):
    return sorted(
        path for path in (base / ".lake" / "build" / "ir").rglob("*.c.o.export")
        if path.name not in exclude
    )


def file_sha256(path):
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def compile_modules(jobs):
    sources = sorted((ROOT / ".lake" / "build" / "ir").rglob("*.c"))
    sources += sorted((LEAN_SYS / ".lake" / "build" / "ir").rglob("*.c"))
    sources = [source for source in sources if source.suffix == ".c"]
    if not sources:
        raise RuntimeError("turbo-lean did not emit LeanAV or LeanSys C sources")
    pending = []
    for source in sources:
        output = source.with_name(source.name + ".o.export")
        stamp = source.with_name(source.name + ".o.sha256")
        digest = file_sha256(source)
        if output.is_file() and stamp.is_file() and stamp.read_text().strip() == digest:
            continue
        pending.append((source, output, stamp, digest))
    # Compile largest C files first so long-pole translation units never trail at the end
    pending.sort(key=lambda item: item[0].stat().st_size, reverse=True)
    active = []
    failures = []
    while pending or active:
        while pending and len(active) < jobs:
            source, output, stamp, digest = pending.pop(0)
            unlink_outputs(output, stamp)
            cmd = ["leanc", "-c", "-o", str(output), str(source), "-O3", "-DNDEBUG", "-DLEAN_EXPORTING"]
            print("+", " ".join(cmd), flush=True)
            active.append((source, stamp, digest, subprocess.Popen(cmd)))
        still_running = []
        progressed = False
        for source, stamp, digest, proc in active:
            rc = proc.poll()
            if rc is None:
                still_running.append((source, stamp, digest, proc))
            else:
                progressed = True
                if rc != 0:
                    failures.append(source)
                else:
                    stamp.write_text(digest + "\n")
        active = still_running
        if active and not progressed:
            time.sleep(0.02)
    if failures:
        raise RuntimeError("module compilation failed: " + ", ".join(map(str, failures)))


def unlink_outputs(*paths):
    for path in paths:
        try:
            path.unlink()
        except FileNotFoundError:
            pass


def link_executable():
    objects = module_objects(ROOT) + module_objects(LEAN_SYS, {"Core.c.o.export"})
    objects.insert(0, BUILD / "c" / "leanav_zero_exec_stub.o")
    shim = LEAN_SYS_BUILD / "lib" / "liblean_sys_shim.a"
    if shim.is_file():
        objects.append(shim)
    objects.append(BUILD / "lib" / "libleanav_dsp.a")
    output = BUILD / "bin" / "lffmpeg"
    output.parent.mkdir(parents=True, exist_ok=True)
    args = ["leanc", "-o", str(output), *[str(item) for item in objects]]
    if platform.system() == "Darwin":
        args.append("-Wl,-dead_strip")
    else:
        args.append("-lpthread")
    response = BUILD / "bin" / "lffmpeg.rsp"
    response.write_text("".join(f"{arg}\n" for arg in args[2:]))
    run(args)
    output.chmod(0o755)


def native_turbo_lean_bin():
    override = os.environ.get("TURBO_LEAN_EXE")
    candidates = [Path(override)] if override else []
    which = shutil.which("turbo-lean")
    if which:
        candidates.append(Path(which))
    for path in candidates:
        try:
            if path.is_file() and b"turbo_spec_verify_module_artifact_set" in path.read_bytes():
                return str(path)
        except OSError:
            continue
    return None


def discover_package_modules(pkg_root, pkg_name, top_file, src_dir):
    files = [pkg_root / top_file, *sorted((pkg_root / src_dir).rglob("*.lean"))]
    nodes = {}
    for src in files:
        if not src.is_file():
            continue
        rel = src.relative_to(pkg_root).with_suffix("")
        mod = ".".join(rel.parts)
        imports = []
        in_block = False
        for line in src.read_text().splitlines():
            if in_block:
                if "-/" in line:
                    in_block = False
                continue
            stripped = line.strip()
            if not stripped or stripped.startswith("--"):
                continue
            if stripped.startswith("/-"):
                if "-/" not in stripped[2:]:
                    in_block = True
                continue
            match = IMPORT_RE.match(line)
            if match:
                imports.append(match.group(1).replace("«", "").replace("»", ""))
            else:
                break
        nodes[mod] = {
            "module": mod,
            "pkg_root": pkg_root,
            "pkg_name": pkg_name,
            "src": src,
            "rel": rel,
            "imports": imports,
        }
    return nodes


def build_lean_modules_direct(packages, prefix, jobs, env):
    all_nodes = {}
    for pkg_root, pkg_name, top_file, src_dir in packages:
        manifest = pkg_root / ".lake" / "build" / ".turbo_verified_sources.json"
        if manifest.exists():
            manifest.unlink()
        all_nodes.update(discover_package_modules(pkg_root, pkg_name, top_file, src_dir))
    deps = {mod: {imp for imp in info["imports"] if imp in all_nodes} for mod, info in all_nodes.items()}
    done = set()
    failed = set()
    active = []
    failures = []
    ld_key = "DYLD_LIBRARY_PATH" if platform.system() == "Darwin" else "LD_LIBRARY_PATH"
    lean_env = dict(env)
    lean_env[ld_key] = os.pathsep.join(
        [str(prefix / "lib" / "lean"), str(prefix / "lib"), *filter(None, [lean_env.get(ld_key)])]
    )
    lean_env.setdefault("LEAN_STACK_SIZE_KB", "262144")
    with tempfile.TemporaryDirectory(prefix="leanav-setup-") as setup_root:
        setup_dir = Path(setup_root)
        while len(done) + len(failed) < len(all_nodes) or active:
            ready = sorted(
                mod for mod, req in deps.items()
                if mod not in done and mod not in failed and all(mod != item[0] for item in active) and req <= done
            )
            if not ready and not active and not failed:
                raise RuntimeError("cyclic or unresolved Lean module graph")
            while ready and len(active) < jobs and not failed:
                mod = ready.pop(0)
                info = all_nodes[mod]
                pkg_build = info["pkg_root"] / ".lake" / "build"
                olean = pkg_build / "lib" / "lean" / info["rel"].with_suffix(".olean")
                ilean = pkg_build / "lib" / "lean" / info["rel"].with_suffix(".ilean")
                c_out = pkg_build / "ir" / info["rel"].with_suffix(".c")
                stamp = pkg_build / "lib" / "lean" / info["rel"].with_suffix(".olean.sha256")
                olean.parent.mkdir(parents=True, exist_ok=True)
                c_out.parent.mkdir(parents=True, exist_ok=True)
                dep_sig = hashlib.sha256()
                dep_sig.update(file_sha256(info["src"]).encode())
                for d in sorted(deps[mod]):
                    d_olean = all_nodes[d]["pkg_root"] / ".lake" / "build" / "lib" / "lean" / all_nodes[d]["rel"].with_suffix(".olean")
                    dep_sig.update(file_sha256(d_olean).encode())
                digest = dep_sig.hexdigest()
                if olean.is_file() and ilean.is_file() and c_out.is_file() and stamp.is_file() and stamp.read_text().strip() == digest:
                    done.add(mod)
                    continue
                unlink_outputs(
                    olean,
                    ilean,
                    c_out,
                    stamp,
                    olean.with_suffix(".olean.server"),
                    olean.with_suffix(".olean.private"),
                )
                setup = setup_dir / f"{mod}.setup.json"
                setup.write_text(json.dumps({
                    "name": mod,
                    "package": info["pkg_name"],
                    "isModule": False,
                    "options": {},
                    "importArts": {},
                    "dynlibs": [],
                    "plugins": [],
                }))
                cmd = [
                    "lean",
                    str(info["src"]),
                    "-R",
                    str(info["pkg_root"]),
                    "-o",
                    str(olean),
                    "-i",
                    str(ilean),
                    "--setup",
                    str(setup),
                    "-c",
                    str(c_out),
                ]
                print("+", " ".join(cmd), flush=True)
                active.append((mod, stamp, digest, subprocess.Popen(cmd, cwd=info["pkg_root"], env=lean_env)))
            if active:
                still_running = []
                progressed = False
                for mod, stamp, digest, proc in active:
                    rc = proc.poll()
                    if rc is None:
                        still_running.append((mod, stamp, digest, proc))
                    else:
                        progressed = True
                        if rc != 0:
                            failed.add(mod)
                            failures.append(mod)
                        else:
                            stamp.write_text(digest + "\n")
                            done.add(mod)
                active = still_running
                if failed and not active:
                    break
                if active and not progressed:
                    time.sleep(0.02)
    if failures:
        raise RuntimeError("Lean compilation failed: " + ", ".join(failures))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    parser.add_argument("--skip-lean", action="store_true")
    parser.add_argument("--direct-lean", action="store_true")
    args = parser.parse_args()
    jobs = max(1, args.jobs)
    prefix = toolchain_prefix()
    build_externals(prefix)
    if not args.skip_lean:
        env = os.environ.copy()
        env["LEAN_PATH"] = os.pathsep.join([
            str(BUILD / "lib" / "lean"),
            str(LEAN_SYS_BUILD / "lib" / "lean"),
        ])
        env.setdefault("TURBO_LEAN_JOBS", str(jobs))
        env.setdefault("TURBO_LEAN_MODULE_TIMEOUT_SECS", "900")
        env.setdefault("TURBO_LEAN_NO_DAEMON", "1")
        env["TURBO_LEAN_EMIT_C"] = "1"
        if LEAN_SYS.is_dir():
            build_lean_modules_direct([(LEAN_SYS, "lean-sys", "LeanSys.lean", "LeanSys")], prefix, jobs, env)
        turbo = None if args.direct_lean else native_turbo_lean_bin()
        if turbo is not None:
            run([turbo, "--json", "build", "LeanAV:c", "lffmpeg:c"], cwd=ROOT, env=env)
        else:
            build_lean_modules_direct([(ROOT, "lean-ffmpeg", "LeanAV.lean", "LeanAV")], prefix, jobs, env)
    compile_modules(jobs)
    link_executable()
    print(json.dumps({"status": "built", "output": str(BUILD / "bin" / "lffmpeg")}))


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as exc:
        print(f"command failed ({exc.returncode}): {exc.cmd}", file=sys.stderr)
        sys.exit(exc.returncode or 1)
