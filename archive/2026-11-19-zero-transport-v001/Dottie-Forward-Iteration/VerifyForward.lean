import ForwardCertificate
import Lean.Util.CollectAxioms

/-! Kernel declaration and transitive axiom audit, including private proofs. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`FlankReferences, `ReferenceReset, `ForwardCertificate]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut dependencies : CollectAxioms.State := {}
  let mut found := #[0,0,0]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    let some n := modules.idxOf? modName | continue
    match info with
    | .axiomInfo _ => throwError "Undischarged axiom: {name}"
    | .thmInfo _ =>
      let (_, next) := ((CollectAxioms.collect name).run env).run dependencies
      for a in next.axioms do
        unless allowed.contains a do throwError "{name} depends on {a}"
      dependencies := next
      found := found.modify n (·+1)
    | _ => pure ()
  for (m,n) in modules.zip found do
    if n == 0 then throwError "Missing proofs in {m}"
    logInfo m!"{m}: {n} kernel-checked theorem declarations"

open DottieOriented
#print axioms ForwardCertificate.endpoint_partition
#print axioms ForwardCertificate.dyadic_both_anchors_nonriemann
#print axioms ForwardCertificate.zeta_ne_zero_on_imaginary_axis
