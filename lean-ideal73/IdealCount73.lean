import OriginalQuarticBranch
import PrimeDecomposition73
import PrimePowerIdealCount
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
    `PrimePowerIdealCount.count_even, `PrimePowerIdealCount.count_odd]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for name in targets do
    unless (env.find? name).any (·.isTheorem) do throwError "Missing theorem: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError "{name} depends on {axiomName}"
  logInfo m!"Checked {targets.size} field and ideal theorems against the foundational axiom list."
