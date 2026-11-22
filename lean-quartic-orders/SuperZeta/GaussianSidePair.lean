import SuperZeta.GaussianSideSign

/-! Comparison of two reflected inputs at one height in the completed Gaussian
integral. The reflection identity requires a real kernel. The quantitative
separation uses the quartic certificate in its stated rectangle. -/

open MeasureTheory
open scoped ComplexConjugate

namespace SuperZeta.GaussianSidePair

open PinchRadius GaussianSideSign

/-- Reflecting the horizontal displacement conjugates the completed value. -/
theorem halfMellin_reflect (K : ℝ → ℝ) (a t : ℝ) :
    halfMellin K ⟨-a,t⟩ = conj (halfMellin K ⟨a,t⟩) := by
  have he : (⟨-a,t⟩ : ℂ) = -(conj (⟨a,t⟩ : ℂ)) := by
    apply Complex.ext <;> simp
  rw [he, halfMellin_even]
  unfold halfMellin
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, ← Complex.cosh_conj]

/-- Use the same completion on the two sides at the same height. -/
theorem reflected_reading {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    Λ (point (-a) t) = conj (Λ (point a t)) := by
  rw [cert.representation (-a) t (by rwa [abs_neg]) ht, cert.representation a t ha ht]
  exact halfMellin_reflect K a t

/-- The real parts cancel exactly. The signed difference in the imaginary
coordinate is twice the horizontal displacement times the height and slope. -/
theorem pair_difference {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    Λ (point a t) - Λ (point (-a) t) =
      ((2 * (a*t) * GaussianSideIntegral.slope K a t : ℝ) : ℂ) * Complex.I := by
  rw [reflected_reading cert ha ht, Complex.sub_conj, (quantitative_reading cert ha ht).1]
  push_cast
  ring

/-- Two proposed zeros would give distance zero. The certified arithmetic
slope yields a strictly positive lower bound at any off-axis input here. -/
theorem pair_distance_lower {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) (hat : a*t ≠ 0) :
    36000 * |a*t| < ‖Λ (point a t) - Λ (point (-a) t)‖ := by
  have hq := slope_floor cert ha ht
  have hq0 : 0 < GaussianSideIntegral.slope K a t := by linarith
  rw [pair_difference cert ha ht, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul (2*(a*t)) _, abs_mul 2 (a*t), abs_of_pos hq0,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  calc
    _ = 2 * |a*t| * 18000 := by ring
    _ < _ := mul_lt_mul_of_pos_left hq (mul_pos (by norm_num) (abs_pos.mpr hat))

end SuperZeta.GaussianSidePair

#print axioms SuperZeta.GaussianSidePair.halfMellin_reflect
#print axioms SuperZeta.GaussianSidePair.reflected_reading
#print axioms SuperZeta.GaussianSidePair.pair_difference
#print axioms SuperZeta.GaussianSidePair.pair_distance_lower
