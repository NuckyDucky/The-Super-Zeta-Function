import QuarticCrossAnalysis
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let analytic := #[
    `SuperZeta.DedekindPhase.from_log_sheet,
    `SuperZeta.Quartet.determinant_root_iff,
    `SuperZeta.UnitSpectrum.root_hasSum, `SuperZeta.UnitSpectrum.equality_iff_riemann_zero,
    `SuperZeta.QuarticTurn.actual_sum_after_turn, `SuperZeta.QuarticTurn.same_input,
    `SuperZeta.QuarticTurn.gaussian_zero_set_after_j,
    `QuarticFiniteFourier.quarticCharacter_primitive, `QuarticConductorSign.root_number,
    `QuarticConductorSign.amplitude, `QuarticConductorSign.reflection,
    `SuperZeta.QuarticSignedOrders.full_eq_completed,
    `SuperZeta.QuarticOrderedTurns.recover_from_orders,
    `SuperZeta.QuarticSignedOrders.full_zero_iff_moments,
    `SuperZeta.QuarticStageAxes.launch_exists, `SuperZeta.QuarticStageAxes.generator_coordinates,
    `SuperZeta.QuarticStageAxes.opposite_marks_73, `SuperZeta.QuarticStageAxes.theta_eq,
    `SuperZeta.QuarticStageAxes.theta_reflection, `SuperZeta.QuarticStageAxes.kernel_eq,
    `SuperZeta.QuarticStageAxes.stage_eq_completed, `SuperZeta.QuarticStageAxes.stage_eq_full,
    `SuperZeta.QuarticStageAxes.launch_invariance, `SuperZeta.QuarticStageAxes.axes_at_address,
    `SuperZeta.QuarticStageAxes.both_tests_at_address, `SuperZeta.QuarticStageAxes.reflected_stage,
    `SuperZeta.QuarticStageAxes.axes_at_mirror_addresses, `SuperZeta.QuarticStageAxes.axis_length_at_address,
    `SuperZeta.QuarticStageAxes.orders_differ_iff_axis_survives,
    `SuperZeta.QuarticStageAxes.excludes_right_and_mirror,
    `SuperZeta.QuarticHeightAssembly.spectral_matches_at_heights,
    `SuperZeta.QuarticHeightAssembly.height_error_of_recovery,
    `SuperZeta.QuarticHeightAssembly.spectral_matches_on_line_of_cofinal_counts,
    `SuperZeta.QuarticHeightAssembly.field_zero_cases,
    `SuperZeta.QuarticHeightAssembly.off_line_field_zero_iff,
    `SuperZeta.QuarticHeightAssembly.reflected_gaussian_disk_at_height,
    `SuperZeta.QuarticHeightAssembly.fixed_rings_of_right_localization,
    `SuperZeta.QuarticCrossAnalysis.ij_difference,
    `SuperZeta.QuarticCrossAnalysis.ij_ne_ji_iff,
    `SuperZeta.QuarticCrossAnalysis.ij_at_address,
    `SuperZeta.QuarticCrossAnalysis.outer_circle_cross_analysis]
  let numerical := #[`QuarticKernel.actual_checked_shells, `QuarticKernel.actual_cells_pass,
    `QuarticKernel.actual_quartic_certificate, `QuarticKernel.verified_quartic_zero_on_line,
    `SuperZeta.QuarticStageAxes.low_stage_axis, `SuperZeta.QuarticStageAxes.low_k_ne_zero,
    `SuperZeta.QuarticStageAxes.low_stage_zero_on_line, `SuperZeta.QuarticStageAxes.verified_stage_chain,
    `SuperZeta.QuarticHeightAssembly.completion_eq, `SuperZeta.QuarticHeightAssembly.completion_zero_iff,
    `SuperZeta.QuarticHeightAssembly.off_line_field_zero_height,
    `SuperZeta.QuarticHeightAssembly.off_line_field_zero_at_address,
    `SuperZeta.QuarticHeightAssembly.field_strip_rh_of_ring_localization]
  let foundation := #[`propext, `Classical.choice, `Quot.sound]
  for (names, allowed) in [(analytic, foundation), (numerical, foundation)] do
    let mut visited : CollectAxioms.State := {}
    for name in names do
      let some (.thmInfo _) := (← getEnv).find? name | throwError "Missing theorem {name}"
      let (_, deps) := ((CollectAxioms.collect name).run (← getEnv)).run visited
      for dep in deps.axioms do
        unless allowed.contains dep do throwError "{name} uses {dep}"
      visited := deps
  logInfo m!"Passed transitive axiom checks for {analytic.size} analytic and {numerical.size} numerical theorems."

#print axioms QuarticKernel.actual_quartic_certificate
#print axioms SuperZeta.QuarticStageAxes.verified_stage_chain
#print axioms SuperZeta.QuarticHeightAssembly.field_strip_rh_of_ring_localization
#print axioms SuperZeta.QuarticCrossAnalysis.outer_circle_cross_analysis
