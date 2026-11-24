import DottieStructuralPairBlocks
open Lean Elab Command QuarticModel

syntax (name := timeScoreCheck) "#time_score " str " in " command : command

elab_rules : command
  | `(#time_score $label:str in $command:command) => do
    let start ← IO.monoNanosNow
    elabCommand command
    let elapsed := (← IO.monoNanosNow) - start
    logInfo m!"{label.getString}: {elapsed.toFloat / 1000000} ms"

set_option Elab.async false
set_option maxHeartbeats 30000000

namespace DottieStructuralProfile

#time_score "old_signs" in
theorem old_signs : dottiePairRowBlock (fun _ => 1) 10999 5120 256 =
    (26 : ℤ) := by decide +kernel
#print axioms old_signs

#time_score "structural_signs" in
theorem structural_signs : dottiePairRowBlockWithSign dottieStructuralRowSign (fun _ => 1) 10999 5120 256 =
    (26 : ℤ) := by decide +kernel
#print axioms structural_signs

#time_score "lookup_signs" in
theorem lookup_signs : dottiePairRowBlockWithSign dottieLookupRowSign (fun _ => 1) 10999 5120 256 =
    (26 : ℤ) := by decide +kernel
#print axioms lookup_signs

#time_score "old_score" in
theorem old_score : dottiePairRowBlock dottieQuickWeightTicks 10999 5120 256 =
    (4090118592412427998957558059046639506996421340519676158472401734661472 : ℤ) := by decide +kernel
#print axioms old_score

#time_score "matched_score" in
theorem matched_score : dottiePairRowBlockWithSign dottieRowSign dottieQuickWeightTicks 10999 5120 256 =
    (4090118592412427998957558059046639506996421340519676158472401734661472 : ℤ) := by decide +kernel
#print axioms matched_score

#time_score "structural_score" in
theorem structural_score : dottiePairRowBlockWithSign dottieStructuralRowSign dottieQuickWeightTicks 10999 5120 256 =
    (4090118592412427998957558059046639506996421340519676158472401734661472 : ℤ) := by decide +kernel
#print axioms structural_score

#time_score "lookup_score" in
theorem lookup_score : dottiePairRowBlockWithSign dottieLookupRowSign dottieQuickWeightTicks 10999 5120 256 =
    (4090118592412427998957558059046639506996421340519676158472401734661472 : ℤ) := by decide +kernel
#print axioms lookup_score


end DottieStructuralProfile
