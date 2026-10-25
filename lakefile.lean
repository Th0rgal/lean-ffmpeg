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
  let brewIncOk ← ("/opt/homebrew/include/libavformat/avformat.h" : FilePath).pathExists
  let brewLibOk ← ("/opt/homebrew/lib/libavformat.dylib" : FilePath).pathExists
  let linuxX86Inc ← ("/usr/include/x86_64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists
  let linuxArmInc ← ("/usr/include/aarch64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists
  let linuxGenInc ← ("/usr/include/libavformat/avformat.h" : FilePath).pathExists
  let linuxX86Lib ← ("/usr/lib/x86_64-linux-gnu/libavformat.so" : FilePath).pathExists
  let linuxArmLib ← ("/usr/lib/aarch64-linux-gnu/libavformat.so" : FilePath).pathExists
  let mut incFlags : Array String := #["-I", leanIncludeDir.toString, "-I", cDir.toString]
  if brewIncOk && brewLibOk then
    incFlags := incFlags ++ #["-I", "/opt/homebrew/include", "-DLEANAV_ENABLE_LIBAV=1"]
  else if (linuxX86Inc || linuxGenInc) && linuxX86Lib then
    incFlags := incFlags ++ #["-DLEANAV_ENABLE_LIBAV=1"]
  else if (linuxArmInc || linuxGenInc) && linuxArmLib then
    incFlags := incFlags ++ #["-DLEANAV_ENABLE_LIBAV=1"]
  let cpuInfo : FilePath := "/proc/cpuinfo"
  let hasAvx2 : Bool ← if ← cpuInfo.pathExists then
    let txt ← IO.FS.readFile cpuInfo
    pure (decide ((txt.splitOn "avx2").length > 1))
  else
    pure false
  let mut optFlags : Array String := #["-O3", "-fPIC", "-Wno-deprecated-declarations"]
  if !System.Platform.isOSX then
    if hasAvx2 then
      optFlags := optFlags ++ #["-mavx2", "-mfma"]
    else
      optFlags := optFlags ++ #["-msse4.2"]
  let simdO ← buildO simdOFile simdSrcJob incFlags optFlags "cc"
  let lnirOFile := pkg.buildDir / "c" / "leanav_lnir_kernels.o"
  let llName := if System.Platform.isOSX then "leanav_lnir_arm64.ll" else "leanav_lnir_x86_64.ll"
  let lnirSrcJob ← inputTextFile <| pkg.dir / "c" / llName
  let mut lnirOptFlags : Array String := #["-O3", "-fPIC", "-Wno-override-module"]
  if !System.Platform.isOSX then
    if hasAvx2 then
      lnirOptFlags := lnirOptFlags ++ #["-mavx2", "-mfma"]
    else
      lnirOptFlags := lnirOptFlags ++ #["-msse4.2"]
  let lnirO ← buildO lnirOFile lnirSrcJob #[] lnirOptFlags "clang"
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
  moreLinkArgs := if System.Platform.isOSX then (if (run_io do return (← ("/opt/homebrew/include/libavformat/avformat.h" : FilePath).pathExists) && (← ("/opt/homebrew/lib/libavformat.dylib" : FilePath).pathExists)) then #["-L/opt/homebrew/lib", "-Wl,-rpath,/opt/homebrew/lib", "-lavformat", "-lavcodec", "-lswresample", "-lavutil"] else #[]) else (if (run_io do return ((← ("/usr/include/x86_64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists) || (← ("/usr/include/aarch64-linux-gnu/libavformat/avformat.h" : FilePath).pathExists) || (← ("/usr/include/libavformat/avformat.h" : FilePath).pathExists)) && ((← ("/usr/lib/x86_64-linux-gnu/libavformat.so" : FilePath).pathExists) || (← ("/usr/lib/aarch64-linux-gnu/libavformat.so" : FilePath).pathExists))) then #["-L/usr/lib/x86_64-linux-gnu", "-L/usr/lib/aarch64-linux-gnu", "-lavformat", "-lavcodec", "-lswresample", "-lavutil", "-lpthread"] else #["-lpthread"])
