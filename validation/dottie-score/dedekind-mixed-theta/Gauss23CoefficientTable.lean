import Gauss23UnitPhaseTable

/-! Connect compact integer coefficient tables to the analytic reading. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

def gauss23TableWeight (table : Array (Array (Box × Box))) (j : Fin 16) (i : Fin 24) : Box × Box :=
  (table.getD j.val #[]).getD i.val (constant 0, constant 0)

theorem gauss23_tableValue_contains (m : ℕ) (weights : Fin 16 → Fin 24 → Box × Box)
    (value : ℕ → ComplexBox)
    (hWeights : ∀ j i, weights j i = gauss23IntegerWeightBox (gauss23CachedUnitPhase j i) m j i)
    (hValue : ∀ k : Fin 37, value k.val = gauss23SharedValueCoefficient weights k.val)
    (k : ℕ) (hk : k ≤ 36) :
    ComplexBox.Contains (value k) (gauss23CenteredCoeff false (m : ℝ) k) := by
  rw [hValue ⟨k, by omega⟩]
  apply gauss23_sharedValueCoefficient_contains weights (m : ℝ)
  intro j i
  rw [hWeights j i]
  exact gauss23_integerWeightBox_contains m j i (gauss23_cachedUnitPhase_contains j i)

#print axioms gauss23_tableValue_contains

end FieldTarget
