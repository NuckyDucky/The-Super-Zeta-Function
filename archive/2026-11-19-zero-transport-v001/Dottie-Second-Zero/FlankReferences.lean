import SuperZeta.Oriented.LiuConnection
import SuperZeta.Multiplicity

namespace DottieOriented.FlankReferences

open Complex HurwitzZeta Set Filter
open scoped Topology
open DottieOriented.LiuConnection

noncomputable section

private theorem scale_residue {b : ℝ} (hb : b ∈ Icc 0 1) {w : ℂ} (hw : 1 < w.re) (j : Fin 2) :
    (2 : ℂ) ^ w * (∑' n : ℕ, 1 / (((j.val + 2 * n : ℕ) : ℂ) + b) ^ w) =
      hurwitzZeta (((j.val : ℝ) + b) / 2 : ℝ) w := by
  have hj : ((j.val : ℝ) + b) / 2 ∈ Icc (0 : ℝ) 1 := by
    have h₁ : j.val ≤ 1 := by omega
    have h₂ : (j.val : ℝ) ≤ 1 := by exact_mod_cast h₁
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) hb.1) (by norm_num)
    · linarith [hb.2]
  rw [← (hasSum_hurwitzZeta_of_one_lt_re hj hw).tsum_eq, ← tsum_mul_left]
  congr 1 with n
  have hbase : ((j.val + 2 * n : ℕ) : ℂ) + b =
      (((2 : ℝ) * (n + (j.val + b) / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hbase, ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) (add_nonneg (Nat.cast_nonneg _) hj.1)]
  push_cast
  have hn : (2 : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  simp [one_div, mul_inv_rev, mul_left_comm, mul_comm, hn]

private theorem duplicate_initial {b : ℝ} (hb : b ∈ Icc 0 1) {w : ℂ} (hw : 1 < w.re) :
    hurwitzZeta (b/2 : ℝ) w + hurwitzZeta ((1+b)/2 : ℝ) w = (2:ℂ)^w * hurwitzZeta b w := by
  have h₀ := hasSum_hurwitzZeta_of_one_lt_re hb hw
  have split := Nat.sumByResidueClasses h₀.summable 2
  rw [h₀.tsum_eq] at split
  have h := congrArg (fun a : ℂ => (2 : ℂ) ^ w * a) split
  change (2 : ℂ) ^ w * hurwitzZeta b w =
    (2 : ℂ) ^ w * ∑ j : Fin 2, ∑' n : ℕ, 1 / (((j.val + 2 * n : ℕ) : ℂ) + b) ^ w at h
  rw [Finset.mul_sum] at h
  simp_rw [scale_residue hb hw] at h
  rw [Fin.sum_univ_two] at h
  simpa using h.symm

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


theorem duplicate {b : ℝ} (hb : b ∈ Icc 0 1) {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (b/2 : ℝ) w + hurwitzZeta ((1+b)/2 : ℝ) w = (2:ℂ)^w * hurwitzZeta b w := by
  have htwo : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := fun z => hurwitzZeta (b/2 : ℝ) z + hurwitzZeta ((1+b)/2 : ℝ) z)
    (g := fun z => (2:ℂ)^z * hurwitzZeta b z) ?_ ?_ punctured_preconnected htwo ?_ hw
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact ((differentiableAt_hurwitzZeta _ hz).add (differentiableAt_hurwitzZeta _ hz)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hp : DifferentiableAt ℂ (fun t : ℂ => (2 : ℂ) ^ t) z := by fun_prop (disch := norm_num)
    exact (hp.mul (differentiableAt_hurwitzZeta _ hz)).differentiableWithinAt
  · apply eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : 1 < (2 : ℂ).re))
    exact fun z (hz : 1 < z.re) => duplicate_initial hb hz

theorem quarter_pair {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (1/4 : ℝ) w + hurwitzZeta (3/4 : ℝ) w =
      (2:ℂ)^w * ((2:ℂ)^w-1) * riemannZeta w := by
  have a := duplicate (b:=0) (by norm_num) hw
  have b := duplicate (b:=(1/2 : ℝ)) (by norm_num) hw
  norm_num [hurwitzZeta_zero] at a b
  linear_combination b + (2:ℂ)^w*a

theorem sixth_pair {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (1/6 : ℝ) w + hurwitzZeta (5/6 : ℝ) w =
      ((2:ℂ)^w-1) * ((3:ℂ)^w-1) * riemannZeta w := by
  have a := duplicate (b:=(1/3 : ℝ)) (by norm_num) hw
  have b := duplicate (b:=(2/3 : ℝ)) (by norm_num) hw
  have c := DottieOriented.LiuConnection.hurwitz_pair hw
  norm_num at a b
  linear_combination a + b + ((2:ℂ)^w - 1)*c

private def quarterFactor (w : ℂ) : ℂ :=
  (Real.pi:ℂ)^(-w) * ((2:ℂ)^w * ((2:ℂ)^w-1))

private def sixthFactor (w : ℂ) : ℂ :=
  (Real.pi:ℂ)^(-w) * (((2:ℂ)^w-1) * ((3:ℂ)^w-1))

private theorem quarter_reference {w : ℂ} (hw : w ≠ 1) :
    reference (1/4 : ℝ) w = quarterFactor w * riemannZeta w := by
  simp only [reference, quarterFactor, show (1-1/4 : ℝ)=3/4 by norm_num, quarter_pair hw, mul_assoc]

private theorem sixth_reference {w : ℂ} (hw : w ≠ 1) :
    reference (1/6 : ℝ) w = sixthFactor w * riemannZeta w := by
  simp only [reference, sixthFactor, show (1-1/6 : ℝ)=5/6 by norm_num, sixth_pair hw, mul_assoc]

private theorem two_factor_ne_zero {w : ℂ} (hpos : 0 < w.re) : (2:ℂ)^w - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  have hnorm : 1 < ‖(2:ℂ)^w‖ := by
    rw [show ‖(2:ℂ)^w‖ = (2:ℝ)^w.re from norm_natCast_cpow_of_pos (n:=2) (by decide) w]
    exact Real.one_lt_rpow (by norm_num) hpos
  intro eqOne
  simp [eqOne] at hnorm

private theorem q4_unit {w : ℂ} (hpos : 0 < w.re) : quarterFactor w ≠ 0 := by
  apply mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  exact mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (by norm_num))) (two_factor_ne_zero hpos)

private theorem q6_unit {w : ℂ} (hpos : 0 < w.re) : sixthFactor w ≠ 0 := by
  apply mul_ne_zero (cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  exact mul_ne_zero (two_factor_ne_zero hpos) (three_factor_ne_zero hpos)

theorem flank_zero_iff {b : ℝ} (hb : b = 1/4 ∨ b = 1/6) {w : ℂ} (hpos : 0 < w.re) (hw : w ≠ 1) :
    reference b w = 0 ↔ riemannZeta w = 0 := by
  rcases hb with rfl | rfl
  · rw [quarter_reference hw, mul_eq_zero]
    simp [q4_unit hpos]
  · rw [sixth_reference hw, mul_eq_zero]
    simp [q6_unit hpos]

/-- Equality of analytic orders at each point with positive real part away from the pole. -/
theorem flank_zero_order {b : ℝ} (hb : b = 1/4 ∨ b = 1/6) {w : ℂ} (hpos : 0 < w.re) (hw : w ≠ 1) :
    ∃ ha : AnalyticAt ℂ (reference b) w, ha.order = (SuperZeta.Multiplicity.analytic_zeta hw).order := by
  have aux (factor : ℂ → ℂ) (hf : AnalyticAt ℂ factor w) (hn : factor w ≠ 0)
      (hid : ∀ z : ℂ, z ≠ 1 → reference b z = factor z * riemannZeta z) :
      ∃ ha : AnalyticAt ℂ (reference b) w, ha.order = (SuperZeta.Multiplicity.analytic_zeta hw).order := by
    have he : (fun z => factor z * riemannZeta z) =ᶠ[𝓝 w] reference b := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hw] with z hz using (hid z hz).symm
    have ha := hf.mul (SuperZeta.Multiplicity.analytic_zeta hw)
    exact ⟨ha.congr he, by rw [ha.order_congr he, hf.order_mul, hf.order_eq_zero_iff.mpr hn, zero_add]⟩
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rcases hb with rfl | rfl
  · apply aux quarterFactor _ (q4_unit hpos) (fun _ hz => quarter_reference hz)
    unfold quarterFactor
    simp only [cpow_def_of_ne_zero hp, cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
    fun_prop
  · apply aux sixthFactor _ (q6_unit hpos) (fun _ hz => sixth_reference hz)
    unfold sixthFactor
    simp only [cpow_def_of_ne_zero hp, cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0),
      cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
    fun_prop

end
end DottieOriented.FlankReferences
