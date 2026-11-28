import Height29IntegerTrace.Seeds

namespace FieldTarget

set_option exponentiation.threshold 512

set_option maxHeartbeats 0 in
theorem height29_phase_step_checked :
    height29ArchivedPhaseStep = gaussPhaseSeed (10 ^ 30) := by
  decide +kernel

private def seedIndex (group : Fin 6) (slot : Fin 4) : Fin 24 := ⟨4 * group.val + slot.val, by omega⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_0 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 0 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 0 j)).1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_1 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 1 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 1 j)).1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_2 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 2 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 2 j)).1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_3 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 3 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 3 j)).1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_4 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 4 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 4 j)).1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private theorem seed_group_5 :
    ∀ j : Fin 4, height29ArchivedInitialPhase (seedIndex 5 j) =
      gaussPhaseSeed (gauss24Pair (seedIndex 5 j)).1 := by
  decide +kernel

theorem height29_initial_phases_checked (i : Fin 24) :
    height29ArchivedInitialPhase i = gaussPhaseSeed (gauss24Pair i).1 := by
  have h (group : Fin 6) (slot : Fin 4) :
      height29ArchivedInitialPhase (seedIndex group slot) =
        gaussPhaseSeed (gauss24Pair (seedIndex group slot)).1 := by
    fin_cases group
    · exact seed_group_0 slot
    · exact seed_group_1 slot
    · exact seed_group_2 slot
    · exact seed_group_3 slot
    · exact seed_group_4 slot
    · exact seed_group_5 slot
  let group : Fin 6 := ⟨i.val / 4, by omega⟩
  let slot : Fin 4 := ⟨i.val % 4, by omega⟩
  have hIndex : seedIndex group slot = i := by
    apply Fin.ext
    dsimp only [seedIndex, group, slot]
    omega
  simpa only [hIndex] using h group slot

#print axioms height29_phase_step_checked
#print axioms height29_initial_phases_checked

end FieldTarget
