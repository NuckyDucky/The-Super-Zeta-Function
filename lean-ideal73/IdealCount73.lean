import OriginalQuarticBranch
import PrimeDecomposition73
import PrimePowerIdealCount
import FieldCoefficientTransfer
import DerivativeRectangle
import StripCover
import Lean.Util.CollectAxioms

/-! Audit the concrete field, its defining quartic and the actual Dedekind coefficient. -/
open Lean Elab Command in
run_cmd do
  let targets := #[`OriginalQuarticBranch.quartic_vanishes,
    `OriginalQuarticBranch.branch_generates, `QuarticModel.minpoly_theta,
    `QuarticAt73.good_reduction, `QuarticAt73.ideal_count,
    `QuarticAt73.residue_pair, `QuarticAt73.signed_residues,
    `PrimeDecomposition73.prime_ideals, `PrimeDecomposition73.distinct,
    `PrimeDecomposition73.unramified, `PrimeDecomposition73.degrees, `PrimeDecomposition73.norms,
    `PrimeDecomposition73.reduction_of_i, `PrimeDecomposition73.gaussian_marks,
    `PrimePowerIdealCount.count_even, `PrimePowerIdealCount.count_odd,
    `FieldTarget.continuation_eq_off_one, `FieldTarget.dedekindZetaRH_iff_three_factors,
    `FieldTarget.dedekindZetaRH_iff_third_factor,
    `FieldCoefficientTransfer.idealCounts_series,
    `FieldCoefficientTransfer.isDedekind_of_primePowerCounts,
    `FieldCoefficientTransfer.quarticRH_iff_gaussian, `StripCover.rightBox_exhaustion,
    `StripCover.fieldRH_iff_thirdFactorBoxMargins, `StripCover.fieldRH_of_patchBounds,
    `GaussianRectangle.real_on_line_of_reflection, `GaussianRectangle.zero_on_line,
    `GaussianRectangle.unique_simple_on_line, `GaussianRectangle.zero_on_line_of_remainder,
    `GaussianRectangle.off_line_zero_forces_remainder_slope]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do throwError "Missing theorem: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError "{name} depends on {axiomName}"
  logInfo m!"Checked {targets.size} ideal, field-transfer, and rectangle theorems against the foundational axiom list."
