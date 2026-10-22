import Lake
open Lake DSL
open System (FilePath)

package «LeanAV» where
  version := v!"0.1.0"

require «lean-sys» from "../lean-sys"

@[default_target]
lean_lib «LeanAV» where
  roots := #[`LeanAV]
  precompileModules := false

@[default_target]
lean_exe «lean-av-core» where
  root := `LeanAV.Main
  supportInterpreter := false
