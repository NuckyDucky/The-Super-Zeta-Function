import DottieProductionField
import ArchivedQuarticSignedPatchCover
import DottieHeightVerification
import Lean.Util.CollectAxioms

-- The actual Dottie ring, with its remaining premises in the theorem type.
#check @QuarticModel.dottieProductionRightNonzero_of_tight_signed
#check @SuperZeta.StirlingCorrection.dottie_band_selects_marked_returns
#check @QuarticModel.archivedQuarticZeta_isDedekind

-- The fixed quartic over the whole strip.
#check @QuarticModel.archivedQuarticRH_iff_upper_right
#check @StripCover.rightBox_exhaustion
#print StripCover.BoxMargins
#print StripCover.HasSignedPatchBounds
#check @QuarticModel.archivedQuarticRH_of_signedPatchBounds

-- The Dedekind target and the same-input implication for any number field.
#print ArtinPrimitiveRootsConjecture.IsDedekindZeta
#print ArtinPrimitiveRootsConjecture.DedekindZetaRH
universe u
#check (∀ (K : Type u) [Field K] [NumberField K], ArtinPrimitiveRootsConjecture.DedekindZetaRH K)
#check @FieldTarget.dedekindZetaRH_of_same_input_signed_gap

open Lean Elab Command in
run_cmd do
  let targets := #[
    `QuarticModel.dottieProductionRightNonzero_of_tight_signed,
    `SuperZeta.StirlingCorrection.dottie_band_selects_marked_returns,
    `QuarticModel.archivedQuarticZeta_isDedekind,
    `QuarticModel.archivedQuarticRH_iff_upper_right,
    `StripCover.rightBox_exhaustion,
    `QuarticModel.archivedQuarticRH_of_signedPatchBounds,
    `FieldTarget.dedekindZetaRH_of_same_input_signed_gap]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do
      throwError "Missing theorem {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on {axiomName}"
  logInfo m!"Transitive axiom check passed for all {targets.size} declarations."

#print axioms QuarticModel.dottieProductionRightNonzero_of_tight_signed
#print axioms QuarticModel.archivedQuarticRH_iff_upper_right
#print axioms QuarticModel.archivedQuarticRH_of_signedPatchBounds
#print axioms FieldTarget.dedekindZetaRH_of_same_input_signed_gap
