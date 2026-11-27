import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Taylor expansion in the output variable about an arbitrary complex center.
The two amplitudes already contain the phases at that center. -/

namespace FieldTarget

open MeasureTheory Set
open scoped Interval

noncomputable section

def centeredFoldedMellin (A B : ℝ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..L, A u * Complex.exp ((u : ℂ) * z) +
    B u * Complex.exp (-((u : ℂ) * z))

def centeredFoldedMellinCoeff (A B : ℝ → ℂ) (L : ℝ) (k : ℕ) : ℂ :=
  ∫ u in (0 : ℝ)..L,
    (A u + (-1 : ℂ) ^ k * B u) * (u : ℂ) ^ k / (k.factorial : ℂ)

private def expTruncation (n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range n, z ^ j / (j.factorial : ℂ)

private theorem expTruncation_bound {n : ℕ} {z : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) (hcut : R / (n + 1 : ℕ) ≤ 1 / 2) :
    ‖Complex.exp z - expTruncation n z‖ ≤ 2 * R ^ n / (n.factorial : ℝ) := by
  have h := Complex.exp_bound' ((div_le_div_of_nonneg_right hz (by positivity)).trans hcut)
  refine h.trans ?_
  rw [mul_comm (2 : ℝ), ← div_mul_eq_mul_div]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz n) (by positivity))
    (by norm_num)

/-- The Taylor error depends on the distance from the center. `M` bounds the
sum of the two amplitude norms. The same result applies after differentiating
by moving the additional factors `u` and `-u` into the amplitudes. -/
theorem centeredFoldedMellin_error_le {A B : ℝ → ℂ} {L r M : ℝ}
    (hA : Continuous A) (hB : Continuous B) (hL : 0 ≤ L)
    (hM : ∀ u ∈ Icc 0 L, ‖A u‖ + ‖B u‖ ≤ M)
    (n : ℕ) (hcut : L * r / (n + 1 : ℕ) ≤ 1 / 2)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖centeredFoldedMellin A B L z -
        ∑ k ∈ Finset.range n, centeredFoldedMellinCoeff A B L k * z ^ k‖ ≤
      L * M * (2 * (L * r) ^ n / (n.factorial : ℝ)) := by
  let f (u : ℝ) := A u * Complex.exp ((u : ℂ) * z) + B u * Complex.exp (-((u : ℂ) * z))
  let g (u : ℝ) := A u * expTruncation n ((u : ℂ) * z) + B u * expTruncation n (-((u : ℂ) * z))
  let a (k : ℕ) (u : ℝ) := (A u + (-1 : ℂ) ^ k * B u) * (u : ℂ) ^ k / (k.factorial : ℂ)
  let E := 2 * (L * r) ^ n / (n.factorial : ℝ)
  have hg (u : ℝ) : g u = ∑ k ∈ Finset.range n, a k u * z ^ k := by
    unfold g expTruncation a
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [show -((u : ℂ) * z) = (-1 : ℂ) * ((u : ℂ) * z) by ring,
      mul_pow, mul_pow]
    ring
  have hc (k : ℕ) : Continuous (fun u : ℝ ↦ a k u * z ^ k) := by
    dsimp [a]
    fun_prop
  have hgInt : (∫ u in (0 : ℝ)..L, g u) =
      ∑ k ∈ Finset.range n, centeredFoldedMellinCoeff A B L k * z ^ k := by
    simp_rw [hg]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_mul_const]
      rfl
    · intro k _
      exact (hc k).intervalIntegrable _ _
  have hfi : IntervalIntegrable f volume 0 L :=
    (show Continuous f by dsimp [f]; fun_prop).intervalIntegrable _ _
  have hgi : IntervalIntegrable g volume 0 L := by
    have he : g = fun u ↦ ∑ k ∈ Finset.range n, a k u * z ^ k := funext hg
    rw [he]
    exact (continuous_finsetSum _ (fun k _ ↦ hc k)).intervalIntegrable _ _
  change ‖(∫ u in (0 : ℝ)..L, f u) - _‖ ≤ L * M * E
  rw [← hgInt, ← intervalIntegral.integral_sub hfi hgi]
  have hr : 0 ≤ r := (norm_nonneg _).trans hz
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hBound (u : ℝ) (hu : u ∈ Ioc 0 L) : ‖f u - g u‖ ≤ M * E := by
    have hPos : ‖(u : ℂ) * z‖ ≤ L * r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1.le]
      exact mul_le_mul hu.2 hz (norm_nonneg _) hL
    have hNeg : ‖-((u : ℂ) * z)‖ ≤ L * r := by rwa [norm_neg]
    have hf : f u - g u =
        A u * (Complex.exp ((u : ℂ) * z) - expTruncation n ((u : ℂ) * z)) +
        B u * (Complex.exp (-((u : ℂ) * z)) - expTruncation n (-((u : ℂ) * z))) := by
      dsimp only [f, g]
      ring
    rw [hf]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc
      _ ≤ ‖A u‖ * E + ‖B u‖ * E := add_le_add
        (mul_le_mul_of_nonneg_left (expTruncation_bound hPos hcut) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (expTruncation_bound hNeg hcut) (norm_nonneg _))
      _ = (‖A u‖ + ‖B u‖) * E := by ring
      _ ≤ M * E := mul_le_mul_of_nonneg_right (hM u ⟨hu.1.le, hu.2⟩) hE
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := L) (f := fun u ↦ f u - g u) (C := M * E)
    (fun u hu ↦ hBound u (by rwa [uIoc_of_le hL] at hu))
  rw [show L * M * E = M * E * L by ring]
  simpa only [sub_zero, abs_of_nonneg hL] using hIntegral

end

#print axioms centeredFoldedMellin_error_le

end FieldTarget
