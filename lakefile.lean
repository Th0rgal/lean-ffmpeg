import Lake
open Lake DSL
open System (FilePath)

package «lean-ffmpeg» where
  version := v!"0.2.0"

require «lean-sys» from "../lean-sys"

target leanav_simd_kernels_o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "leanav_simd_kernels.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "leanav_simd_kernels.c"
  let leanIncludeDir ← getLeanIncludeDir
  let brewInc : FilePath := "/opt/homebrew/include"
  let hasBrewAv ← (brewInc / "libavformat" / "avformat.h").pathExists
  let incFlags :=
    if hasBrewAv then
      #["-I", leanIncludeDir.toString, "-I", brewInc.toString]
    else
      #["-I", leanIncludeDir.toString]
  buildO oFile srcJob incFlags #["-O3", "-fPIC", "-Wno-deprecated-declarations"] "cc"

extern_lib libleanav_dsp pkg := do
  let simdO ← leanav_simd_kernels_o.fetch
  let name := nameToStaticLib "leanav_dsp"
  buildStaticLib (pkg.staticLibDir / name) #[simdO]

@[default_target]
lean_lib «LeanAV» where
  roots := #[`LeanAV]
  precompileModules := false

@[default_target]
lean_exe «lffmpeg» where
  root := `LeanAV.Main
  supportInterpreter := false
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-L/opt/homebrew/lib", "-Wl,-rpath,/opt/homebrew/lib", "-lavformat", "-lavcodec", "-lswresample", "-lavutil"]
    else
      #[]
