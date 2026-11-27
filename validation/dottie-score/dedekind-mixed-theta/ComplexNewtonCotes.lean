import ContourTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace FieldTarget

open MeasureTheory Metric Set
open scoped BigOperators Interval NNReal

noncomputable section

/-- The closed nine-point Newton–Cotes weights, before division by 28350. -/
def ninePointWeight (i : Fin 9) : ℤ :=
  [989, 5888, -928, 10496, -4540, 10496, -928, 5888, 989].getD i.val 0

/-- The nine nodes on a panel with center zero and half-width one. -/
def ninePointOffset (i : Fin 9) : ℚ :=
  ((i.val : ℚ) - 4) / 4

/-- The quadrature rule on the real interval from `c - h` to `c + h`. -/
def ninePointRule (f : ℝ → ℂ) (c h : ℝ) : ℂ :=
  ((2 * h / 28350 : ℝ) : ℂ) *
    ∑ i : Fin 9, (ninePointWeight i : ℂ) * f (c + h * (ninePointOffset i : ℝ))

private theorem ninePointOffset_abs_le (i : Fin 9) :
    |(ninePointOffset i : ℝ)| ≤ 1 := by
  have hi : (i.val : ℝ) < 9 := by exact_mod_cast i.isLt
  have hj : i.val ≤ 8 := by omega
  have h8 : (i.val : ℝ) ≤ 8 := by exact_mod_cast hj
  have h0 : 0 ≤ (i.val : ℝ) := by positivity
  unfold ninePointOffset
  push_cast
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The moments needed for exactness. All ten are rational identities. -/
theorem ninePointWeight_moment : ∀ k : Fin 10,
    ∑ i : Fin 9, (ninePointWeight i : ℚ) * ninePointOffset i ^ k.val =
      28350 * (1 - (-1 : ℚ) ^ (k.val + 1)) / (2 * (k.val + 1 : ℚ)) := by
  decide +kernel

theorem ninePointWeight_norm_sum :
    ∑ i : Fin 9, ‖(ninePointWeight i : ℂ)‖ = (41142 : ℝ) := by
  have h : ∑ i : Fin 9, |ninePointWeight i| = (41142 : ℤ) := by decide +kernel
  have h' := congrArg (fun z : ℤ ↦ (z : ℝ)) h
  push_cast at h'
  simpa only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] using h'

private theorem ninePoint_monomial (c h : ℝ) (k : Fin 10) :
    (∫ x in c - h..c + h, ((x - c : ℝ) : ℂ) ^ k.val) =
      ninePointRule (fun x ↦ ((x - c : ℝ) : ℂ) ^ k.val) c h := by
  have hmoment : ∑ i : Fin 9, (ninePointWeight i : ℝ) * (ninePointOffset i : ℝ) ^ k.val =
      28350 * (1 - (-1 : ℝ) ^ (k.val + 1)) / (2 * (k.val + 1 : ℝ)) := by
    exact_mod_cast ninePointWeight_moment k
  have hre :
      (h ^ (k.val + 1) - (-h) ^ (k.val + 1)) / (k.val + 1 : ℝ) =
        (2 * h / 28350) * (h ^ k.val *
          ∑ i : Fin 9, (ninePointWeight i : ℝ) * (ninePointOffset i : ℝ) ^ k.val) := by
    rw [hmoment, ← neg_one_mul h, mul_pow, pow_succ h]
    have hk : (k.val : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hsub : c - h - c = -h := by ring
  have hadd : c + h - c = h := by ring
  have hshift := intervalIntegral.integral_comp_sub_right
    (a := c - h) (b := c + h) (f := fun x : ℝ ↦ (x : ℂ) ^ k.val) c
  rw [hsub, hadd] at hshift
  rw [hshift]
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal, integral_pow, hre, ninePointRule]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_sub_cancel_left, mul_pow]
  ring

/-- The rule integrates every polynomial of degree at most nine exactly. -/
theorem ninePoint_polynomial (a : ℕ → ℂ) (c h : ℝ) :
    (∫ x in c - h..c + h, ∑ k ∈ Finset.range 10, a k * ((x - c : ℝ) : ℂ) ^ k) =
      ninePointRule (fun x ↦ ∑ k ∈ Finset.range 10, a k * ((x - c : ℝ) : ℂ) ^ k) c h := by
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    calc
      _ = ∑ k ∈ Finset.range 10,
          a k * ninePointRule (fun x ↦ ((x - c : ℝ) : ℂ) ^ k) c h := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ninePoint_monomial c h ⟨k, Finset.mem_range.mp hk⟩]
      _ = _ := by
        simp only [ninePointRule, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
  · intro k _
    exact (show Continuous (fun x : ℝ ↦ a k * ((x - c : ℝ) : ℂ) ^ k) from by
      fun_prop).intervalIntegrable _ _

private theorem ninePointRule_sub_norm_le {f g : ℝ → ℂ} {c h E : ℝ} (hh : 0 ≤ h)
    (herr : ∀ x ∈ Icc (c - h) (c + h), ‖f x - g x‖ ≤ E) :
    ‖ninePointRule f c h - ninePointRule g c h‖ ≤ (2 * h * (41142 / 28350)) * E := by
  have hnode (i : Fin 9) : c + h * (ninePointOffset i : ℝ) ∈ Icc (c - h) (c + h) := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp (ninePointOffset_abs_le i)
    have hl := mul_le_mul_of_nonneg_left hlo hh
    have hu := mul_le_mul_of_nonneg_left hhi hh
    exact ⟨by linarith only [hl], by linarith only [hu]⟩
  unfold ninePointRule
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * h / 28350)]
  simp_rw [← mul_sub]
  calc
    _ ≤ (2 * h / 28350) * ∑ i : Fin 9,
        ‖(ninePointWeight i : ℂ) * (f (c + h * (ninePointOffset i : ℝ)) -
          g (c + h * (ninePointOffset i : ℝ)))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (2 * h / 28350) * ∑ i : Fin 9, ‖(ninePointWeight i : ℂ)‖ * E := by
      gcongr with i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (herr _ (hnode i)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ninePointWeight_norm_sum]; ring

/-- A complex contour bound controls the quadrature error on the real panel. -/
theorem ninePointRule_error_le {F : ℂ → ℂ} {c h M : ℝ} {R : ℝ≥0}
    (hh : 0 ≤ h) (hr : h < (R : ℝ))
    (hF : DifferentiableOn ℂ F (closedBall (c : ℂ) R))
    (hM : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) :
    ‖(∫ x in c - h..c + h, F (x : ℂ)) - ninePointRule (fun x ↦ F (x : ℂ)) c h‖ ≤
      2 * h * (1 + 41142 / 28350) * (M * (h / (R : ℝ)) ^ 10 / (1 - h / (R : ℝ))) := by
  let E := M * (h / (R : ℝ)) ^ 10 / (1 - h / (R : ℝ))
  let p := fun x : ℝ ↦ ∑ k ∈ Finset.range 10,
    contourTaylorCoeff F c R k * ((x - c : ℝ) : ℂ) ^ k
  have hp (x : ℝ) (hx : x ∈ Icc (c - h) (c + h)) :
      ‖F (x : ℂ) - p x‖ ≤ E := by
    have hxnorm : ‖((x - c : ℝ) : ℂ)‖ ≤ h := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have ⟨hlo, hhi⟩ := hx
      exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
    have h := contourTaylor_tail_le hF hM hr hxnorm 10
    rwa [← Complex.ofReal_add, show c + (x - c) = x by ring] at h
  have hc : ContinuousOn (fun x : ℝ ↦ F (x : ℂ)) (Icc (c - h) (c + h)) := by
    refine hF.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have ⟨hlo, hhi⟩ := hx
    exact (abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩ : |x - c| ≤ h).trans hr.le
  have hab : c - h ≤ c + h := by linarith only [hh]
  have hfi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  have hpi : IntervalIntegrable p volume (c - h) (c + h) := by
    apply Continuous.intervalIntegrable
    dsimp only [p]
    fun_prop
  have hInt : ‖(∫ x in c - h..c + h, F (x : ℂ)) - ∫ x in c - h..c + h, p x‖ ≤ E * (2 * h) := by
    rw [← intervalIntegral.integral_sub hfi hpi]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c - h) (b := c + h) (f := fun x : ℝ ↦ F (x : ℂ) - p x)
      (fun x hx ↦ hp x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hx)))
    rwa [abs_of_nonneg (sub_nonneg.mpr hab), show c + h - (c - h) = 2 * h by ring] at hbnd
  have hRule := ninePointRule_sub_norm_le hh hp
  have hExact : (∫ x in c - h..c + h, p x) = ninePointRule p c h :=
    ninePoint_polynomial (contourTaylorCoeff F c R) c h
  calc
    _ ≤ ‖(∫ x in c - h..c + h, F (x : ℂ)) - ∫ x in c - h..c + h, p x‖ +
        ‖(∫ x in c - h..c + h, p x) - ninePointRule (fun x ↦ F (x : ℂ)) c h‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ E * (2 * h) + (2 * h * (41142 / 28350)) * E := by
      refine add_le_add hInt ?_
      rw [hExact, norm_sub_rev]
      exact hRule
    _ = _ := by dsimp only [E]; ring

/-- The composite rule uses `N` adjacent panels, each of width `2 * h`. -/
def ninePointComposite (f : ℝ → ℂ) (a h : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.range N, ninePointRule f (a + (2 * (k : ℝ) + 1) * h) h

/-- The composite error bound holds with the same contour allowance on each panel. -/
theorem ninePointComposite_error_le {F : ℂ → ℂ} {a h M : ℝ} {R : ℝ≥0} (N : ℕ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hF : Differentiable ℂ F)
    (hM : ∀ c ∈ Icc a (a + 2 * (N : ℝ) * h), ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) :
    ‖(∫ x in a..(a + 2 * (N : ℝ) * h), F (x : ℂ)) -
        ninePointComposite (fun x ↦ F (x : ℂ)) a h N‖ ≤
      (2 * (N : ℝ) * h) * (1 + 41142 / 28350) *
        (M * (h / (R : ℝ)) ^ 10 / (1 - h / (R : ℝ))) := by
  let b := fun k : ℕ ↦ a + 2 * (k : ℝ) * h
  let c := fun k : ℕ ↦ a + (2 * (k : ℝ) + 1) * h
  have hbc₁ (k : ℕ) : b k = c k - h := by dsimp only [b, c]; ring
  have hbc₂ (k : ℕ) : b (k + 1) = c k + h := by dsimp only [b, c]; push_cast; ring
  have hbn : b 0 = a := by simp [b]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := b) (n := N)
    (f := fun x : ℝ ↦ F (x : ℂ))
    (fun k _ ↦ (hF.continuous.comp Complex.continuous_ofReal).intervalIntegrable (b k) (b (k + 1)))
  rw [hbn] at hsplit
  change (∑ k ∈ Finset.range N, ∫ x in b k..b (k + 1), F (x : ℂ)) =
    ∫ x in a..(a + 2 * (N : ℝ) * h), F (x : ℂ) at hsplit
  rw [← hsplit, ninePointComposite, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ k ∈ Finset.range N, 2 * h * (1 + 41142 / 28350) *
        (M * (h / (R : ℝ)) ^ 10 / (1 - h / (R : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hlt : k < N := Finset.mem_range.mp hk
      have hcast : (k : ℝ) + 1 ≤ N := by exact_mod_cast hlt
      have hn : (0 : ℝ) ≤ k := by positivity
      have hcenter : c k ∈ Icc a (a + 2 * (N : ℝ) * h) := by
        refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
        change a + (2 * (k : ℝ) + 1) * h ≤ a + 2 * (N : ℝ) * h
        exact add_le_add_right (mul_le_mul_of_nonneg_right (by linarith only [hcast]) hh) a
      change ‖(∫ x in b k..b (k + 1), F (x : ℂ)) - ninePointRule (fun x ↦ F (x : ℂ)) (c k) h‖ ≤ _
      rw [hbc₁, hbc₂]
      exact ninePointRule_error_le hh hr hF.differentiableOn (hM _ hcenter)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

#print axioms ninePointWeight_moment
#print axioms ninePointWeight_norm_sum
#print axioms ninePoint_polynomial
#print axioms ninePointRule_error_le
#print axioms ninePointComposite_error_le

end

end FieldTarget

