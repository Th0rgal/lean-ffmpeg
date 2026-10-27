/- Pure production PlanIR checks. Staged only; not executed during preparation.
   Later gate: lake env lean --run scripts/check_mpeg_options.lean
   No media files, process invocation, or timing. -/
import LeanAV.PlanIR

open LeanAV.PlanIR

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def baseArgs : List String := ["-i", "input.mp4", "-c:v", "h264"]
private def pairs : List (String × String) :=
  [("-mpv_flags", "+qp_rd"), ("-intra_vlc", "0"),
   ("-mpv_flags", "-qp_rd+mv0"), ("-data_partitioning", "1"),
   ("-intra_vlc", "1"), ("-mpv_flags", "0"), ("-data_partitioning", "0")]
private def optionArgs : List String := pairs.flatMap (fun (flag, value) => [flag, value])

private def mpegPairs : List String → List (String × String)
  | flag :: value :: rest =>
    if isMpegDelegatedValueFlag flag then (flag, value) :: mpegPairs rest
    else mpegPairs (value :: rest)
  | _ => []

def main : IO Unit := do
  let atoms := ["skip_rd", "strict_gop", "qp_rd", "cbp_rd", "naq", "mv0"]
  for atom in atoms do
    for value in [atom, "+" ++ atom, "-" ++ atom] do
      check ("atom: " ++ value) (isValidMpvFlags value)
  for value in ["0", "+qp_rd+mv0", "skip_rd-strict_gop+naq", "-cbp_rd+qp_rd-mv0"] do
    check ("combination: " ++ value) (isValidMpvFlags value)
  for value in ["", "unknown", "1", "32", "0x20", "00", "+0", "-0", "0+mv0",
                "mv0+0", "all", "none", "+", "-", "++mv0", "--mv0", "+-mv0",
                "mv0+-naq", "mv0+", "mv0-", "mv0|naq", "mv0,naq", "mv0=1",
                " mv0", "mv0 ", "mv0\t", "mv0\n", "$(touch marker)", "mv0;true",
                "mv0\x00"] do
    check ("invalid mpv: " ++ value) (!isValidMpvFlags value)
  for flag in ["-intra_vlc", "-data_partitioning"] do
    for value in ["0", "1"] do
      check ("boolean: " ++ flag) (isValidExtendedFlagValue flag value)
    for value in ["", "true", "false", "2", "-1", "01", "+1", "1.0", "1 ", "1\x00"] do
      check ("invalid boolean: " ++ flag) (!isValidExtendedFlagValue flag value)
  let args := baseArgs ++ optionArgs ++ ["output.mp4"]
  let (_, ext, plan) := parseArgsWithPlanIR args
  check "parse errors" plan.errors.isEmpty
  check "ordered ext" (ext.mpegOptions == pairs)
  check "ordered plan" (plan.mpegOptions == pairs)
  check "delegation marker" ext.hasExtraDelegatedFlags
  check "delegated tier" (plan.backend.tier == .delegatedFaithful)
  let rendered := renderPlanIRArgv plan true
  check "rendered MPEG pair order" (mpegPairs rendered == pairs)
  check "exact canonical argv"
    (rendered == ["-nostdin", "-n", "-v", "info", "-i", "input.mp4", "-c:v", "libx264"] ++
      optionArgs ++ ["output.mp4"])
  check "canonical round trip" ((parseArgsToPlanIR (planIRToCliArgs plan)).mpegOptions == pairs)
  check "no-passthrough builder" ((buildDelegatedFfmpegArgv plan).toList == rendered)
  check "original-argv builder"
    ((buildDelegatedFfmpegArgv plan ext.passthroughArgs).toList == ["-nostdin", "-n"] ++ args)
  let native := parseArgsToPlanIR (baseArgs ++ ["output.mp4"])
  check "native absent" (native.backend.tier == .translatedPartial && native.mpegOptions.isEmpty)
  for flag in ["-mpv_flags", "-intra_vlc", "-data_partitioning"] do
    let missing := parseArgsToPlanIR (baseArgs ++ ["output.mp4", flag])
    check "missing fails closed" (!missing.errors.isEmpty && missing.backend.tier == .unsupported)
    let empty := parseArgsToPlanIR (baseArgs ++ [flag, "", "output.mp4"])
    check "empty fails closed" (!empty.errors.isEmpty && empty.backend.tier == .unsupported)
  check "empty argv rejected" (!verifyExecArgvHygiene [])
  check "empty token rejected" (!verifyExecArgvHygiene ["-i", ""])
  check "NUL rejected" (!verifyExecArgvHygiene ["-i", "input\x00.mp4"])
  check "builder empty token gate" ((buildDelegatedFfmpegArgv plan ["-i", ""]).isEmpty)
  check "builder NUL gate" ((buildDelegatedFfmpegArgv plan ["-i", "bad\x00.mp4"]).isEmpty)
  IO.println "MPEG PlanIR checks passed"
