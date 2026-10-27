import LeanAV.Encoder

open LeanAV.Encoder

def main (args : List String) : IO Unit := do
  let bytes ← IO.FS.readBinFile (args[0]!)
  let result ← probeInputHdrAndFpsIO "unused-input" bytes (args[1]! == "true")
  IO.println s!"{result.1},{result.2.1},{result.2.2}"
