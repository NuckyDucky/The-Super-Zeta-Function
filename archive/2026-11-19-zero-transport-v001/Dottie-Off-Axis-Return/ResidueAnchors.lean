import SuperZeta.Oriented.LiuConnection


namespace DottieOriented.ResidueAnchors

open Complex HurwitzZeta Set Filter
open scoped Topology

noncomputable section

private theorem scale_grid (m : ℕ) (hm : 0 < m) {w : ℂ} (hw : 1 < w.re) (j : Fin m) :
    (m : ℂ) ^ w * (∑' n : ℕ, 1 / ((j.val + m * n : ℕ) : ℂ) ^ w) =
      hurwitzZeta ((j.val : ℝ) / m : ℝ) w := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : (j.val : ℝ) / m ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_iff₀ hm', one_mul]
      exact_mod_cast j.isLt.le
  rw [← (hasSum_hurwitzZeta_of_one_lt_re hj hw).tsum_eq, ← tsum_mul_left]
  congr 1 with n
  have hb : ((j.val + m * n : ℕ) : ℂ) =
      (((m : ℝ) * (n + j.val / m : ℝ) : ℝ) : ℂ) := by
    push_cast
    have hm'c : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp [hm'c]
    ring
  rw [hb, ofReal_mul, mul_cpow_ofReal_nonneg hm'.le (by positivity)]
  push_cast
  have hz : (m : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast hm.ne'))
  simp [one_div, mul_inv_rev, mul_left_comm, mul_comm, hz]

private theorem residue_grid_series (m : ℕ) (hm : 0 < m) {w : ℂ} (hw : 1 < w.re) :
    (∑ j : Fin m, hurwitzZeta ((j.val : ℝ)/m : ℝ) w) =
      (m : ℂ) ^ w * riemannZeta w := by
  cases m with
  | zero => omega
  | succ k =>
    have h0 := hasSum_hurwitzZeta_of_one_lt_re (left_mem_Icc.mpr zero_le_one : (0 : ℝ) ∈ Icc 0 1) hw
    have hz : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ w) (riemannZeta w) := by
      simpa [hurwitzZeta_zero] using h0
    have h := congrArg (fun a : ℂ => ((k + 1 : ℕ) : ℂ) ^ w * a) (Nat.sumByResidueClasses hz.summable (k + 1))
    rw [hz.tsum_eq] at h
    change ((k + 1 : ℕ) : ℂ) ^ w * riemannZeta w =
      ((k + 1 : ℕ) : ℂ) ^ w * ∑ j : Fin (k + 1), ∑' n : ℕ, 1 / ((j.val + (k + 1) * n : ℕ) : ℂ) ^ w at h
    rw [Finset.mul_sum] at h
    simpa only [scale_grid (k + 1) hm hw] using h.symm

private theorem punctured_preconnected : IsPreconnected ({1}ᶜ : Set ℂ) := by
  let R := {z : ℂ | 1 < z.re}
  let U := {z : ℂ | 0 < z.im}
  let D := {z : ℂ | z.im < 0}
  let L := {z : ℂ | z.re < 1}
  have hRU : IsPreconnected (R ∪ U) :=
    (convex_halfSpace_re_gt 1).isPreconnected.union (2 + I)
      (by norm_num [R]) (by norm_num [U]) (convex_halfSpace_im_gt 0).isPreconnected
  have hRUD : IsPreconnected (R ∪ U ∪ D) :=
    hRU.union (2 - I) (Or.inl (by norm_num [R])) (by norm_num [D])
      (convex_halfSpace_im_lt 0).isPreconnected
  have hall := hRUD.union I (Or.inl (Or.inr (by simp [U]))) (show I ∈ L by simp [L])
    (convex_halfSpace_re_lt 1).isPreconnected
  convert hall using 1
  ext z
  change z ≠ 1 ↔ (((1 < z.re ∨ 0 < z.im) ∨ z.im < 0) ∨ z.re < 1)
  rw [ne_eq, Complex.ext_iff, not_and_or]
  simp only [one_re, one_im, ← ne_eq, ne_iff_lt_or_gt]
  tauto

/-- The full residue-grid sum, continued to the punctured complex plane. -/
theorem residue_grid (m : ℕ) (hm : 0 < m) {w : ℂ} (hw : w ≠ 1) :
    (∑ j : Fin m, hurwitzZeta ((j.val : ℝ)/m : ℝ) w) =
      (m : ℂ) ^ w * riemannZeta w := by
  have htwo : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := fun w => ∑ j : Fin m, hurwitzZeta ((j.val : ℝ)/m : ℝ) w)
    (g := fun w => (m : ℂ)^w * riemannZeta w) ?_ ?_
    punctured_preconnected htwo ?_ hw
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (DifferentiableAt.sum fun i _ => differentiableAt_hurwitzZeta _ hz).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hp : DifferentiableAt ℂ (fun w : ℂ => (m : ℂ)^w) z := by
      exact differentiableAt_id.const_cpow (.inl (by exact_mod_cast hm.ne'))
    exact (hp.mul (differentiableAt_riemannZeta hz)).differentiableWithinAt
  · apply eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : 1 < (2 : ℂ).re))
    exact fun z (hz : 1 < z.re) => residue_grid_series m hm hz

/-- Quarter shifts comprise exactly the odd residue classes modulo four. -/
theorem hurwitz_fourths {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (1/4 : ℝ) w + hurwitzZeta (3/4 : ℝ) w =
      ((4 : ℂ)^w - (2 : ℂ)^w) * riemannZeta w := by
  have h2 := residue_grid 2 (by decide) hw
  have h4 := residue_grid 4 (by decide) hw
  norm_num [Fin.sum_univ_succ, hurwitzZeta_zero] at h2 h4
  linear_combination h4 - h2

/-- The two sixth shifts comprise the invertible residue classes modulo six. -/
theorem hurwitz_sixths {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (1/6 : ℝ) w + hurwitzZeta (5/6 : ℝ) w =
      ((6 : ℂ)^w - (3 : ℂ)^w - (2 : ℂ)^w + 1) * riemannZeta w := by
  have h2 := residue_grid 2 (by decide) hw
  have h6 := residue_grid 6 (by decide) hw
  have h3 := LiuConnection.hurwitz_pair hw
  norm_num [Fin.sum_univ_succ, hurwitzZeta_zero] at h2 h6
  linear_combination h6 - h2 - h3

end
end DottieOriented.ResidueAnchors
