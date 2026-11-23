import QuarticGrid
import QuarticCertificateState

open MeasureTheory Set

namespace QuarticGrid

private theorem exp_power_lower (n : ℕ) : (2.71828:ℝ)^n ≤ Real.exp n := by
  calc
    _ ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

theorem last_cells_bound {x : ℝ} (hx : x ∈ Icc (279/16 : ℝ) 18) :
    0 ≤ QuarticKernel.kernel x ∧ QuarticKernel.kernel x ≤ 1/1000000 := by
  constructor
  · exact (QuarticKernel.kernel_pos_after_13
      ((by norm_num : (13:ℝ) ≤ 279/16).trans hx.1)).le
  let u := Real.exp x / QuarticKernel.scale
  have h0 : (91/4:ℝ) < Real.exp (279/16) / QuarticKernel.scale := by
    have hE := exp_power_lower 17
    have hT := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 7/16) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at hE hT
    have hP := mul_le_mul hE hT (by norm_num) (Real.exp_pos 17).le
    apply (lt_div_iff₀ QuarticKernel.scale_pos).2
    rw [show (279/16:ℝ) = 17 + 7/16 by norm_num, Real.exp_add]
    linarith [QuarticKernel.scale_lt]
  have hu : x/2 + 14 < u := by
    have hA := mul_lt_mul_of_pos_right h0 (Real.exp_pos (x-279/16))
    have he : Real.exp (279/16) / QuarticKernel.scale * Real.exp (x-279/16) = u := by
      rw [div_mul_eq_mul_div, ← Real.exp_add, show (279/16:ℝ)+(x-279/16)=x by ring]
    rw [he] at hA
    have hB := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-279/16))
      (by norm_num : (0:ℝ) ≤ 91/4)
    dsimp [u]
    linarith [hx.1]
  have hr : Real.exp (-u) ≤ 1/100 := by
    have h6 := exp_power_lower 6
    norm_num at h6
    have hU : (100:ℝ) ≤ Real.exp u := (by linarith : (100:ℝ) ≤ Real.exp 6).trans
      (Real.exp_le_exp.mpr (by linarith [hx.1]))
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact hU
  have hs : (10/11 : ℝ) ≤ (1-Real.exp (-u))^2 := by
    nlinarith [sq_nonneg (1/100-Real.exp (-u))]
  have ht : QuarticKernel.theta u ≤ (11/10)*Real.exp (-u) := by
    refine (le_abs_self _).trans ((QuarticKernel.theta_abs_le (by linarith [hx.1])).trans ?_)
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg (Real.exp_pos (-u)).le (sub_nonneg.mpr hs)]
  have he : (1100000 : ℝ) ≤ Real.exp 14 := by
    have hp := exp_power_lower 14
    norm_num at hp
    linarith
  have hb : (11/10) * Real.exp (-14) ≤ (1/1000000 : ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  calc
    QuarticKernel.kernel x ≤ Real.exp (x/2) * ((11/10) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = (11/10) * Real.exp (x/2-u) := by rw [Real.exp_sub, Real.exp_neg, div_eq_mul_inv]; ring
    _ ≤ (11/10) * Real.exp (-14) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ _ := hb

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem last_cells_data :
    ∀ j : Fin 36, data[1116+j.val]?.getD (0,0) = (0,1) := by decide

theorem encloses_last_cells (j : ℕ) (hj : j < 1152) (hj' : 1116 ≤ j)
    (x : ℝ) (hx : x ∈ Icc (node j : ℝ) (node (j+1) : ℝ)) :
    (lowerK j : ℝ) ≤ QuarticKernel.kernel x ∧
      QuarticKernel.kernel x ≤ (upperK j : ℝ) := by
  have hd := last_cells_data ⟨j-1116, by omega⟩
  change data[1116+(j-1116)]?.getD (0,0) = (0,1) at hd
  rw [show 1116+(j-1116)=j by omega] at hd
  have hleft : (1116:ℝ) ≤ j := by exact_mod_cast hj'
  have hright : ((j+1:ℕ):ℝ) ≤ 1152 := by exact_mod_cast (show j+1 ≤ 1152 by omega)
  have h1 : (279/16 : ℝ) ≤ x := by
    have hv : (node j : ℝ) ≤ x := hx.1
    simp only [node, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hv
    linarith
  have h2 : x ≤ 18 := by
    have hv : x ≤ (node (j+1):ℝ) := hx.2
    simp only [node, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hv
    linarith
  rw [lowerK, upperK, hd]
  simpa using last_cells_bound ⟨h1,h2⟩

/-- The remaining pointwise enclosures and analytic identification plug directly
into the quartic certificate. The last thirty-six rows follow analytically. -/
theorem assemble_from_grid (Λ : ℂ → ℂ)
    (hΛ : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
      Λ (GaussianSideSign.point a t) = SuperZeta.PinchRadius.halfMellin QuarticKernel.kernel ⟨a,t⟩)
    (hcore : ∀ j < 1116, ∀ x ∈ Icc (node j : ℝ) (node (j+1) : ℝ),
      (lowerK j : ℝ) ≤ QuarticKernel.kernel x ∧ QuarticKernel.kernel x ≤ (upperK j : ℝ)) :
    GaussianSideSign.Certificate Λ QuarticKernel.kernel := by
  have hg : Encloses QuarticKernel.kernel := by
    intro j hj x hx
    by_cases h : j < 1116
    · exact hcore j h x hx
    · exact encloses_last_cells j hj (le_of_not_gt h) x hx
  have hsub : Icc (0 : ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1
  apply QuarticKernel.assemble_from_core Λ hΛ
  · intro x hx
    exact nonneg_of_grid hg x ⟨hx.1, hx.2.trans (by norm_num)⟩
  · exact fun t ht => slope_of_grid hg ht ((QuarticKernel.sinc_mass_integrable t).mono_set hsub)
  · exact curvature_of_grid hg (QuarticKernel.mass_integrable.mono_set hsub)

#print axioms last_cells_bound
#print axioms encloses_last_cells
#print axioms assemble_from_grid

end QuarticGrid
