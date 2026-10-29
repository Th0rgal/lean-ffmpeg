import Lake
open Lake DSL
open System (FilePath)

package «lean-ffmpeg» where
  version := v!"0.2.0"

require «lean-sys» from "../lean-sys"

extern_lib libleanav_dsp pkg := do
  let simdOFile := pkg.buildDir / "c" / "leanav_simd_kernels.o"
  let simdSrcJob ← inputTextFile <| pkg.dir / "c" / "leanav_simd_kernels.c"
  let leanIncludeDir ← getLeanIncludeDir
  let cDir := pkg.dir / "c"
  let incFlags : Array String := #["-I", leanIncludeDir.toString, "-I", cDir.toString]
  let cpuInfo : FilePath := "/proc/cpuinfo"
  let (hasAvx2, hasAvx, hasPopcnt, hasF16c) : Bool × Bool × Bool × Bool ← if ← cpuInfo.pathExists then
    let txt ← IO.FS.readFile cpuInfo
    let hasFlag (f : String) : Bool := decide ((txt.splitOn f).length > 1)
    pure (hasFlag "avx2", hasFlag " avx ", hasFlag "popcnt", hasFlag "f16c")
  else
    pure (false, false, false, false)
  let isArm64 := System.Platform.isOSX || System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64"
  let mut optFlags : Array String := #["-O3", "-fPIC", "-Wno-deprecated-declarations"]
  if !isArm64 then
    if hasAvx2 then
      optFlags := optFlags ++ #["-mavx2", "-mfma", "-mpopcnt", "-mf16c"]
    else
      optFlags := optFlags ++ #["-msse4.2"]
      if hasAvx then optFlags := optFlags.push "-mavx"
      if hasPopcnt then optFlags := optFlags.push "-mpopcnt"
      if hasF16c then optFlags := optFlags.push "-mf16c"
  let simdO ← buildO simdOFile simdSrcJob incFlags optFlags "cc"
  let lnirOFile := pkg.buildDir / "c" / "leanav_lnir_kernels.o"
  let llName := if isArm64 then "leanav_lnir_arm64.ll" else "leanav_lnir_x86_64.ll"
  let lnirSrcJob ← inputTextFile <| pkg.dir / "c" / llName
  let mut lnirOptFlags : Array String := #["-O3", "-fPIC", "-Wno-override-module"]
  if !isArm64 then
    if hasAvx2 then
      lnirOptFlags := lnirOptFlags ++ #["-mavx2", "-mfma", "-mpclmul", "-mpopcnt", "-mf16c"]
    else
      lnirOptFlags := lnirOptFlags ++ #["-msse4.2", "-mpclmul"]
      if hasAvx then lnirOptFlags := lnirOptFlags.push "-mavx"
      if hasPopcnt then lnirOptFlags := lnirOptFlags.push "-mpopcnt"
      if hasF16c then lnirOptFlags := lnirOptFlags.push "-mf16c"
  let bundledClang := (← getLeanSysroot) / "bin" / "clang"
  let clangBin ← if ← bundledClang.pathExists then pure bundledClang.toString else pure "clang"
  let lnirO ← buildO lnirOFile lnirSrcJob #[] lnirOptFlags clangBin
  let name := nameToStaticLib "leanav_dsp"
  buildStaticLib (pkg.staticLibDir / name) #[simdO, lnirO]

@[default_target]
lean_lib «LeanAV» where
  roots := #[`LeanAV]
  precompileModules := false

@[default_target]
lean_exe «lffmpeg» where
  root := `LeanAV.Main
  supportInterpreter := false
  moreLinkArgs := if System.Platform.isOSX then #[] else #["-lpthread"]
