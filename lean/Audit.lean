import SuperZeta
import Lean.Util.CollectAxioms

/-! Audit every theorem and axiom declared by our imported modules. Using the
kernel environment checks transitive dependencies, including private lemmas. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut dependencies : CollectAxioms.State := {}
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless `SuperZeta |>.isPrefixOf (env.header.moduleNames[idx.toNat]!) do continue
    match info with
    | .axiomInfo _ => throwError "Project axiom: {name}"
    | .thmInfo _ =>
      -- The kernel environment is fixed during the audit. Reuse dependencies
      -- that have already been traversed and accepted for an earlier theorem.
      let (_, next) := ((CollectAxioms.collect name).run env).run dependencies
      for dep in next.axioms do
        unless allowed.contains dep do throwError "{name} depends on {dep}"
      dependencies := next
      checked := checked + 1
    | _ => pure ()
  if checked == 0 then throwError "No project theorems were audited"
  logInfo m!"Checked {checked} theorem declarations against the foundational axiom list."
