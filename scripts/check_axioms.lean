import Lean
import LeanAV

open Lean Elab Command

private def allowed (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

private def check (decl : Name) : CoreM Bool := do
  let axs ← collectAxioms decl
  let bad := axs.toList.filter (fun a => !allowed a)
  if bad.isEmpty then
    return true
  logError m!"{decl}: disallowed axioms {bad}"
  return false

elab "check_leanav_axioms" : command => do
  let env ← getEnv
  let mut ok := true
  let mut checked : Nat := 0
  for (name, cinfo) in env.constants.toList do
    if (`LeanAV).isPrefixOf name then
      -- Check all theorems (and non-opaque definitions) under LeanAV
      match cinfo with
      | .thmInfo _ =>
        checked := checked + 1
        if !(← liftCoreM (check name)) then ok := false
      | .axiomInfo _ =>
        logError m!"{name}: explicit axiom declaration is disallowed"
        ok := false
      | _ =>
        let axs ← liftCoreM (collectAxioms name)
        let bad := axs.toList.filter (fun a => !allowed a)
        if !bad.isEmpty then
          logError m!"{name}: disallowed axioms {bad}"
          ok := false
        checked := checked + 1
  if checked == 0 then
    throwError "axiom audit failed: 0 LeanAV declarations checked"
  if !ok then
    throwError "axiom audit failed"
  logInfo m!"[check_axioms] Verified {checked} LeanAV declarations (0 sorryAx, 0 custom axioms)."

check_leanav_axioms
