import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The two third-residue spectra and ordinary zeta

We split the convergent zeta series into residue classes modulo three, then
continue the identity away from its pole. The last result accepts a zero-free
half-plane for ordinary zeta as an explicit hypothesis.
-/

namespace DottieOriented.LiuConnection

open Complex HurwitzZeta Set Filter
open scoped Topology

noncomputable section

/-- The corrected observable in the variable `w = 2s`, at shift `b`. -/
def reference (b : ℝ) (w : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-w) * (hurwitzZeta b w + hurwitzZeta (1 - b : ℝ) w)

private theorem scale_residue {w : ℂ} (hw : 1 < w.re) (j : Fin 3) :
    (3 : ℂ) ^ w * (∑' n : ℕ, 1 / ((j.val + 3 * n : ℕ) : ℂ) ^ w) =
      hurwitzZeta ((j.val : ℝ) / 3 : ℝ) w := by
  have hj : (j.val : ℝ) / 3 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · have h : (j.val : ℝ) ≤ 3 := by exact_mod_cast j.isLt.le
      linarith
  rw [← (hasSum_hurwitzZeta_of_one_lt_re hj hw).tsum_eq, ← tsum_mul_left]
  congr 1 with n
  have hbase : ((j.val + 3 * n : ℕ) : ℂ) =
      (((3 : ℝ) * (n + j.val / 3 : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [hbase, ofReal_mul, mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
  push_cast
  have hz : (3 : ℂ) ^ w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  simp [one_div, mul_inv_rev, mul_left_comm, mul_comm, hz]

private theorem hurwitz_pair_of_one_lt_re {w : ℂ} (hw : 1 < w.re) :
    hurwitzZeta (1 / 3 : ℝ) w + hurwitzZeta (2 / 3 : ℝ) w =
      ((3 : ℂ) ^ w - 1) * riemannZeta w := by
  have h0 := hasSum_hurwitzZeta_of_one_lt_re (left_mem_Icc.mpr zero_le_one : (0 : ℝ) ∈ Icc 0 1) hw
  have hz : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ w) (riemannZeta w) := by
    simpa [hurwitzZeta_zero] using h0
  have split := Nat.sumByResidueClasses hz.summable 3
  rw [hz.tsum_eq] at split
  have h := congrArg (fun a : ℂ => (3 : ℂ) ^ w * a) split
  change (3 : ℂ) ^ w * riemannZeta w =
    (3 : ℂ) ^ w * ∑ j : Fin 3, ∑' n : ℕ, 1 / ((j.val + 3 * n : ℕ) : ℂ) ^ w at h
  rw [Finset.mul_sum] at h
  simp_rw [scale_residue hw] at h
  rw [Fin.sum_univ_three] at h
  norm_num [hurwitzZeta_zero] at h
  linear_combination -h

/-- The punctured complex plane covered by four overlapping convex half-planes. -/
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

/-- The equality of the two third-residue Hurwitz spectra with the zeta factor. -/
theorem hurwitz_pair {w : ℂ} (hw : w ≠ 1) :
    hurwitzZeta (1 / 3 : ℝ) w + hurwitzZeta (2 / 3 : ℝ) w =
      ((3 : ℂ) ^ w - 1) * riemannZeta w := by
  have htwo : 2 ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := fun z => hurwitzZeta (1 / 3 : ℝ) z + hurwitzZeta (2 / 3 : ℝ) z)
    (g := fun z => ((3 : ℂ) ^ z - 1) * riemannZeta z) ?_ ?_ punctured_preconnected htwo ?_ hw
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact ((differentiableAt_hurwitzZeta _ hz).add (differentiableAt_hurwitzZeta _ hz)).differentiableWithinAt
  · refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hp : DifferentiableAt ℂ (fun t : ℂ => (3 : ℂ) ^ t - 1) z := by fun_prop (disch := norm_num)
    exact (hp.mul (differentiableAt_riemannZeta hz)).differentiableWithinAt
  · apply eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : 1 < (2 : ℂ).re))
    exact fun z (hz : 1 < z.re) => hurwitz_pair_of_one_lt_re hz

theorem reference_at_thirds {b : ℝ} (hb : b = 1/3 ∨ b = 2/3) {w : ℂ} (hw : w ≠ 1) :
    reference b w = (Real.pi : ℂ) ^ (-w) * (((3 : ℂ) ^ w - 1) * riemannZeta w) := by
  rcases hb with rfl | rfl
  · rw [reference, show (1 - 1/3 : ℝ) = 2/3 by norm_num, hurwitz_pair hw]
  · rw [reference, show (1 - 2/3 : ℝ) = 1/3 by norm_num, add_comm, hurwitz_pair hw]

theorem three_factor_ne_zero {w : ℂ} (hw : 0 < w.re) : (3 : ℂ) ^ w - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  have hnorm : 1 < ‖(3 : ℂ) ^ w‖ := by
    rw [show ‖(3 : ℂ) ^ w‖ = (3 : ℝ) ^ w.re from norm_natCast_cpow_of_pos (n := 3) (by decide) w]
    exact Real.one_lt_rpow (by norm_num) hw
  intro eqOne
  simp [eqOne] at hnorm

/-- In the open right half-plane away from the pole, zeros coincide pointwise. -/
theorem reference_zero_iff {b : ℝ} (hb : b = 1/3 ∨ b = 2/3) {w : ℂ}
    (hpos : 0 < w.re) (hw : w ≠ 1) : reference b w = 0 ↔ riemannZeta w = 0 := by
  have hpi : (Real.pi : ℂ) ^ (-w) ≠ 0 :=
    cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  rw [reference_at_thirds hb hw]
  simp [hpi, three_factor_ne_zero hpos]

/-- Any externally supplied zero-free boundary transfers to both oriented shifts. -/
theorem transfer_half_plane {B : ℝ} (hB : 0 ≤ B)
    (H : ∀ w : ℂ, B < w.re → w ≠ 1 → riemannZeta w ≠ 0)
    {b : ℝ} (hb : b = 1/3 ∨ b = 2/3) {w : ℂ} (hw : B < w.re) (hp : w ≠ 1) :
    reference b w ≠ 0 :=
  fun h => H w hw hp ((reference_zero_iff hb (lt_of_le_of_lt hB hw) hp).mp h)

/-- In radians the positive native return selects one third, and the negative
native return selects two thirds. -/
theorem native_third_shifts :
    (1/2 - (Real.pi/6)/Real.pi : ℝ) = 1/3 ∧
    (1/2 - (-(Real.pi/6))/Real.pi : ℝ) = 2/3 := by
  constructor <;> field_simp [Real.pi_ne_zero] <;> ring

/-- On the original spectral coordinate `s`, the supplied boundary is halved. -/
theorem transfer_half_plane_on_spectral_scale {B : ℝ} (hB : 0 ≤ B)
    (H : ∀ w : ℂ, B < w.re → w ≠ 1 → riemannZeta w ≠ 0)
    {θ : ℝ} (hθ : θ = Real.pi/6 ∨ θ = -(Real.pi/6)) {s : ℂ}
    (hs : B / 2 < s.re) (hp : 2 * s ≠ 1) : reference (1/2 - θ/Real.pi) (2*s) ≠ 0 := by
  apply transfer_half_plane hB H _ _ hp
  · rcases hθ with rfl | rfl
    · exact Or.inl native_third_shifts.1
    · exact Or.inr native_third_shifts.2
  · rw [two_mul, add_re]
    linarith

end
end DottieOriented.LiuConnection
