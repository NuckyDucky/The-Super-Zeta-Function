import ContourTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Integrate against a supplied weight after approximating only the envelope.
For Mellin readings the weight contains the two exact exponential phases. -/

namespace FieldTarget

open MeasureTheory Metric Set
open scoped BigOperators Interval NNReal

noncomputable section

/-- Integrate the first n Taylor terms against the whole weight. -/
def weightedContourTaylorPanel (F : ℂ → ℂ) (W : ℝ → ℂ)
    (c h : ℝ) (R : ℝ≥0) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, contourTaylorCoeff F (c : ℂ) R k *
    (∫ x in c - h..c + h, W x * ((x - c : ℝ) : ℂ) ^ k)

theorem weightedContourTaylorPanel_error_le
    {F : ℂ → ℂ} {W : ℝ → ℂ} {c h M B : ℝ} {R : ℝ≥0} (n : ℕ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hF : Differentiable ℂ F)
    (hM : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) (hW : Continuous W)
    (hB₀ : 0 ≤ B) (hB : ∀ x ∈ Icc (c - h) (c + h), ‖W x‖ ≤ B) :
    ‖(∫ x in c - h..c + h, W x * F (x : ℂ)) -
      weightedContourTaylorPanel F W c h R n‖ ≤
        2 * h * B * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) := by
  let E := M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))
  let p (x : ℝ) := ∑ k ∈ Finset.range n,
    contourTaylorCoeff F (c : ℂ) R k * ((x - c : ℝ) : ℂ) ^ k
  have hp (x : ℝ) (hx : x ∈ Icc (c - h) (c + h)) : ‖F (x : ℂ) - p x‖ ≤ E := by
    have hxnorm : ‖((x - c : ℝ) : ℂ)‖ ≤ h := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    have hb := contourTaylor_tail_le hF.differentiableOn hM hr hxnorm n
    rwa [← Complex.ofReal_add, show c + (x - c) = x by ring] at hb
  have hsplit : (∫ x in c - h..c + h, W x * p x) =
      weightedContourTaylorPanel F W c h R n := by
    unfold weightedContourTaylorPanel p
    simp_rw [Finset.mul_sum, mul_left_comm (W _)]
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul]
    · intro k _
      exact ((hW.mul (by fun_prop)).const_mul _).intervalIntegrable _ _
  have hpc : Continuous p := by unfold p; fun_prop
  have hfc := hF.continuous.comp Complex.continuous_ofReal
  have hFi : IntervalIntegrable (fun x : ℝ ↦ W x * F (x : ℂ)) volume (c - h) (c + h) :=
    (hW.mul hfc).intervalIntegrable _ _
  have hPi : IntervalIntegrable (fun x : ℝ ↦ W x * p x) volume (c - h) (c + h) :=
    (hW.mul hpc).intervalIntegrable _ _
  rw [← hsplit, ← intervalIntegral.integral_sub hFi hPi]
  have hab : c - h ≤ c + h := by linarith only [hh]
  have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := c - h) (b := c + h) (f := fun x : ℝ ↦ W x * F (x : ℂ) - W x * p x)
    (C := B * E) (fun x hx ↦ by
      have hx' : x ∈ Icc (c - h) (c + h) := Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hx)
      rw [← mul_sub, norm_mul]
      exact mul_le_mul (hB x hx') (hp x hx') (norm_nonneg _) hB₀)
  rw [abs_of_nonneg (sub_nonneg.mpr hab), show c + h - (c - h) = 2 * h by ring] at hInt
  exact hInt.trans_eq (by unfold E; ring)

/-- Composite integration on a fixed real grid, for arbitrary continuous weights. -/
def weightedContourTaylorComposite (F : ℂ → ℂ) (W : ℝ → ℂ)
    (a h : ℝ) (R : ℝ≥0) (N n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, weightedContourTaylorPanel F W (a + (2 * (k : ℝ) + 1) * h) h R n

theorem weightedContourTaylorComposite_error_le
    {F : ℂ → ℂ} {W : ℝ → ℂ} {a h M B : ℝ} {R : ℝ≥0} (N n : ℕ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hF : Differentiable ℂ F) (hW : Continuous W)
    (hM : ∀ c ∈ Icc a (a + 2 * (N : ℝ) * h), ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M)
    (hB₀ : 0 ≤ B) (hB : ∀ x ∈ Icc a (a + 2 * (N : ℝ) * h), ‖W x‖ ≤ B) :
    ‖(∫ x in a..(a + 2 * (N : ℝ) * h), W x * F (x : ℂ)) -
      weightedContourTaylorComposite F W a h R N n‖ ≤
        2 * (N : ℝ) * h * B * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) := by
  let b (k : ℕ) := a + 2 * (k : ℝ) * h
  let c (k : ℕ) := a + (2 * (k : ℝ) + 1) * h
  have hbc₁ (k : ℕ) : c k - h = b k := by dsimp only [b, c]; ring
  have hbc₂ (k : ℕ) : c k + h = b (k + 1) := by dsimp only [b, c]; push_cast; ring
  have hb₀ : b 0 = a := by simp [b]
  have hInt := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := b) (n := N)
    (f := fun x : ℝ ↦ W x * F (x : ℂ))
    (fun k _ ↦ (hW.mul (hF.continuous.comp Complex.continuous_ofReal)).intervalIntegrable (b k) (b (k + 1)))
  rw [hb₀] at hInt
  change (∑ k ∈ Finset.range N, ∫ x in b k..b (k + 1), W x * F (x : ℂ)) =
    ∫ x in a..(a + 2 * (N : ℝ) * h), W x * F (x : ℂ) at hInt
  rw [← hInt, weightedContourTaylorComposite, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range N, 2 * h * B * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcast : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
      have hk₀ : (0 : ℝ) ≤ k := by positivity
      have h₁ : a ≤ c k - h := by
        rw [hbc₁]
        change a ≤ a + 2 * (k : ℝ) * h
        exact le_add_of_nonneg_right (by positivity)
      have h₂ : c k + h ≤ a + 2 * (N : ℝ) * h := by
        rw [hbc₂]
        exact add_le_add_right (mul_le_mul_of_nonneg_right (by push_cast; linarith only [hcast]) hh) a
      have hc : c k ∈ Icc a (a + 2 * (N : ℝ) * h) :=
        ⟨by linarith only [h₁, hh], by linarith only [h₂, hh]⟩
      have hPanel := weightedContourTaylorPanel_error_le n hh hr hF (hM _ hc) hW hB₀
        (fun x hx ↦ hB x ⟨h₁.trans hx.1, hx.2.trans h₂⟩)
      rwa [hbc₁, hbc₂] at hPanel
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end

#print axioms weightedContourTaylorPanel_error_le
#print axioms weightedContourTaylorComposite_error_le

end FieldTarget
