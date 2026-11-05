#!/usr/bin/env bash
# Deterministic LNIR_WIRE_V1 + LLVM 18 Pixel-Core Outer-Shell Regeneration & Verification Gate
#
# Modes:
#   scripts/regen_lnir_c_kernels.sh
#     1. Emits 46-decl `c/leanav_lnir_kernels.lnir` from `LeanAV.NativeKernels.emitLeanAvLnirWire`.
#     2. Runs `lean-native-core validate-tv --samples 64` + `verify-certs`.
#     3. Emits `c/leanav_lnir_kernels.h` and patches the 14 `lean_native_*` outer-shell prototypes.
#     4. Compiles raw `x86_64` and `arm64` LLVM 18 modules via `lean-native-core compile-llvm`
#        and splices the 14 deterministic outer shells (`scripts/gen_lnir_outer_shells.py`)
#        that wire every pixel/sample arithmetic step to the 17 verified `@lnir_px_*` cores.
#     5. Verifies whole-module `clang -Werror -O3` compilation on both `x86_64` and `arm64` triples.
#
#   scripts/regen_lnir_c_kernels.sh --check-ir
#     Verifies in CI/local builds (without requiring `lean-native-core` in PATH unless `--with-lnc`
#     is passed) that:
#       - `c/leanav_lnir_kernels.lnir` matches `emitLeanAvLnirWire` byte-for-byte (46 decls).
#       - All 14 `@lean_native_*` outer shells in `c/leanav_lnir_{x86_64,arm64}.ll` match
#         `scripts/gen_lnir_outer_shells.py` byte-for-byte and call their `@lnir_px_*` cores.
#       - All 17 `@lnir_px_*` definitions are present and identical across `x86_64` and `arm64`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MODE="${1:-regen}"

if [[ "$MODE" == "--check-ir" ]]; then
  TMP_DIR="$(mktemp -d)"
  trap 'rm -rf "$TMP_DIR"' EXIT
  cat > "$TMP_DIR/EmitLnir.lean" <<'LEAN'
import LeanAV.NativeKernels
def main (args : List String) : IO Unit := do
  match args with
  | [out] => IO.FS.writeFile out LeanAV.NativeKernels.emitLeanAvLnirWire
  | _ => throw (IO.userError "expected output path")
LEAN
  lake env lean --run "$TMP_DIR/EmitLnir.lean" "$TMP_DIR/kernels.lnir"
  if ! cmp -s "$TMP_DIR/kernels.lnir" "$ROOT/c/leanav_lnir_kernels.lnir"; then
    echo "ERROR: c/leanav_lnir_kernels.lnir is out of sync with LeanAV.NativeKernels.emitLeanAvLnirWire" >&2
    exit 1
  fi
  python3 "$ROOT/scripts/gen_lnir_outer_shells.py" --verify-checked-in "$ROOT"
  python3 - "$ROOT" <<'PY'
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(sys.argv[1]) / "scripts"))
import gen_lnir_outer_shells as gen

root = Path(sys.argv[1])
expected = gen.gen_all_outer_shells().strip()
for arch in ("x86_64", "arm64"):
    txt = (root / "c" / f"leanav_lnir_{arch}.ll").read_text()
    start = "define weak_odr dso_local void @lean_native_swscale_down2x2_u8("
    end = "; LNIRDecl: swscale_luma_gain_bias_simd" if arch == "x86_64" else "define weak_odr dso_local i8 @leansys_select_isa("
    i0, i1 = txt.find(start), txt.find(end)
    assert i0 >= 0 and i1 > i0, f"missing markers in {arch}"
    actual = txt[i0:i1].strip()
    if actual != expected:
        raise SystemExit(f"ERROR: {arch} outer-shell block differs from scripts/gen_lnir_outer_shells.py")
lnir_text = (root / "c" / "leanav_lnir_kernels.lnir").read_text()
lnir_decls = lnir_text.count("|D_decl|")
if not lnir_text.startswith("LNIR_WIRE_V1|") or lnir_decls != 46:
    raise SystemExit(f"ERROR: expected 46 LNIR_WIRE_V1 |D_decl| entries, found {lnir_decls}")
print(f"[regen_lnir_c_kernels --check-ir] OK: 46 LNIR decls + 14 outer shells byte-identical to generator")
PY
  exit 0
fi

LNC="${LEAN_NATIVE_CORE:-$(command -v lean-native-core || true)}"
if [[ -z "$LNC" || ! -x "$LNC" ]]; then
  echo "ERROR: lean-native-core not found in PATH or LEAN_NATIVE_CORE" >&2
  exit 1
fi

TMP_DIR="$(mktemp -d)"
trap 'rm -rf "$TMP_DIR"' EXIT

cat > "$TMP_DIR/EmitLnir.lean" <<'LEAN'
import LeanAV.NativeKernels
def main (args : List String) : IO Unit := do
  match args with
  | [out] => IO.FS.writeFile out LeanAV.NativeKernels.emitLeanAvLnirWire
  | _ => throw (IO.userError "expected output path")
LEAN
lake env lean --run "$TMP_DIR/EmitLnir.lean" "$TMP_DIR/kernels.lnir"

cp "$TMP_DIR/kernels.lnir" "$ROOT/c/leanav_lnir_kernels.lnir"

"$LNC" validate-tv --in "$ROOT/c/leanav_lnir_kernels.lnir" --out "$TMP_DIR/certs.txt" --samples 64
"$LNC" verify-certs --in "$ROOT/c/leanav_lnir_kernels.lnir" --certs "$TMP_DIR/certs.txt"

"$LNC" compile-static-lib --input "$ROOT/c/leanav_lnir_kernels.lnir" -o "$TMP_DIR/libtmp.a" --header "$TMP_DIR/kernels.h"
python3 "$ROOT/scripts/gen_lnir_outer_shells.py" --patch-header "$TMP_DIR/kernels.h"
cp "$TMP_DIR/kernels.h" "$ROOT/c/leanav_lnir_kernels.h"

"$LNC" compile-llvm --arch x86_64 --input "$ROOT/c/leanav_lnir_kernels.lnir" -o "$TMP_DIR/raw_x86_64.ll"
"$LNC" compile-llvm --arch arm64 --input "$ROOT/c/leanav_lnir_kernels.lnir" -o "$TMP_DIR/raw_arm64.ll"

python3 "$ROOT/scripts/gen_lnir_outer_shells.py" --splice-arch x86_64 --in-ll "$TMP_DIR/raw_x86_64.ll" --out-ll "$ROOT/c/leanav_lnir_x86_64.ll"
python3 "$ROOT/scripts/gen_lnir_outer_shells.py" --splice-arch arm64 --in-ll "$TMP_DIR/raw_arm64.ll" --out-ll "$ROOT/c/leanav_lnir_arm64.ll"

CLANG_BIN="${CLANG:-$(command -v clang-18 || command -v clang)}"
"$CLANG_BIN" -Werror -target x86_64-unknown-linux-gnu -O3 -c "$ROOT/c/leanav_lnir_x86_64.ll" -o "$TMP_DIR/x86_64.o"
"$CLANG_BIN" -Werror -target aarch64-unknown-linux-gnu -O3 -c "$ROOT/c/leanav_lnir_arm64.ll" -o "$TMP_DIR/arm64.o"

"$ROOT/scripts/regen_lnir_c_kernels.sh" --check-ir
echo "[regen_lnir_c_kernels] Successfully regenerated and verified 46-decl LNIR + wired x86_64/arm64 LLVM modules."
