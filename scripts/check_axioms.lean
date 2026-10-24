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
  for (name, _) in env.constants.toList do
    if name.isPrefixOf `LeanAV then
      if !(← liftCoreM (check name)) then ok := false
  if !ok then
    throwError "axiom audit failed"

check_leanav_axioms
