import SuperZeta
import Lean.Util.CollectAxioms

/-! Audit every theorem and axiom declared by our imported modules. Using the
kernel environment checks transitive dependencies, including private lemmas. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless `SuperZeta |>.isPrefixOf (env.header.moduleNames[idx.toNat]!) do continue
    match info with
    | .axiomInfo _ => throwError "Project axiom: {name}"
    | .thmInfo _ =>
      for dep in ← Lean.collectAxioms name do
        unless allowed.contains dep do throwError "{name} depends on {dep}"
      checked := checked + 1
    | _ => pure ()
  if checked == 0 then throwError "No project theorems were audited"
  logInfo m!"Checked {checked} theorem declarations against the foundational axiom list."
