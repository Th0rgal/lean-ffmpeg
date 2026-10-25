import Lake
open Lake DSL
open System (FilePath)

package «lean-ffmpeg» where
  version := v!"0.2.0"

require «lean-sys» from "../lean-sys"

def hasBrewLibav : Bool :=
  run_io do
    let incOk ← ("/opt/homebrew/include/libavformat/avformat.h" : FilePath).pathExists
    let libOk ← ("/opt/homebrew/lib/libavformat.dylib" : FilePath).pathExists
    return incOk && libOk

def hasLinuxLibavX86 : Bool :=
  run_io do
    let inc1 ← ("/usr/include/x86_64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists
    let inc2 ← ("/usr/include/libavformat/avformat.h" : FilePath).pathExists
    let libOk ← ("/usr/lib/x86_64-linux-gnu/libavformat.so" : FilePath).pathExists
    return (inc1 || inc2) && libOk

def hasLinuxLibavArm64 : Bool :=
  run_io do
    let inc1 ← ("/usr/include/aarch64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists
    let inc2 ← ("/usr/include/libavformat/avformat.h" : FilePath).pathExists
    let libOk ← ("/usr/lib/aarch64-linux-gnu/libavformat.so" : FilePath).pathExists
    return (inc1 || inc2) && libOk

def hasCpuAvx2 : Bool :=
  run_io do
    let cpuInfo : FilePath := "/proc/cpuinfo"
    if !(← cpuInfo.pathExists) then
      return false
    let txt ← IO.FS.readFile cpuInfo
    return (txt.splitOn "avx2").length > 1

target leanav_simd_kernels_o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanav_simd_kernels.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "leanav_simd_kernels.c"
  let leanIncludeDir ← getLeanIncludeDir
  let cDir := pkg.dir / "c"
  let mut incFlags : Array String := #["-I", leanIncludeDir.toString, "-I", cDir.toString]
  if hasBrewLibav then
    incFlags := incFlags ++ #["-I", "/opt/homebrew/include", "-DLEANAV_ENABLE_LIBAV=1"]
  else if hasLinuxLibavX86 || hasLinuxLibavArm64 then
    incFlags := incFlags ++ #["-DLEANAV_ENABLE_LIBAV=1"]
  let mut optFlags : Array String := #["-O3", "-fPIC", "-Wno-deprecated-declarations"]
  if !System.Platform.isOSX then
    if hasCpuAvx2 then
      optFlags := optFlags ++ #["-mavx2", "-mfma"]
    else
      optFlags := optFlags ++ #["-msse4.2"]
  buildO oFile srcJob incFlags optFlags "cc"

target leanav_lnir_kernels_o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanav_lnir_kernels.o"
  let llName := if System.Platform.isOSX then "leanav_lnir_arm64.ll" else "leanav_lnir_x86_64.ll"
  let srcJob ← inputTextFile <| pkg.dir / "c" / llName
  let mut optFlags : Array String := #["-O3", "-fPIC", "-Wno-override-module"]
  if !System.Platform.isOSX then
    if hasCpuAvx2 then
      optFlags := optFlags ++ #["-mavx2", "-mfma"]
    else
      optFlags := optFlags ++ #["-msse4.2"]
  buildO oFile srcJob #[] optFlags "clang"

extern_lib libleanav_dsp pkg := do
  let simdO ← leanav_simd_kernels_o.fetch
  let lnirO ← leanav_lnir_kernels_o.fetch
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
  moreLinkArgs :=
    if System.Platform.isOSX && hasBrewLibav then
      #["-L/opt/homebrew/lib", "-Wl,-rpath,/opt/homebrew/lib", "-lavformat", "-lavcodec", "-lswresample", "-lavutil"]
    else if !System.Platform.isOSX && (hasLinuxLibavX86 || hasLinuxLibavArm64) then
      #["-lavformat", "-lavcodec", "-lswresample", "-lavutil", "-lpthread"]
    else if System.Platform.isOSX then
      #[]
    else
      #["-lpthread"]
