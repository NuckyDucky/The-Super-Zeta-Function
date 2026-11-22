import SuperZeta.FieldWeights
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.NormNum.LegendreSymbol
import GaussianSideError

open scoped BigOperators
open Set

namespace QuarticKernel

/-- The chosen generator of a Gaussian ideal has first coordinate positive and
second coordinate nonnegative. A row of a fixed norm contains at most one such
generator. -/
noncomputable def row (n j : ℕ) : ℤ :=
  let a := j + 1
  let b := (n - a * a).sqrt
  if a * a + b * b = n then SuperZeta.FieldWeights.conductorReading a b else 0

noncomputable def coeff (n : ℕ) : ℤ := (Finset.range n.sqrt).sum (row n)

theorem sign_at_73 : SuperZeta.FieldWeights.conductorReading 3 8 = -1 ∧
    SuperZeta.FieldWeights.conductorReading 3 (-8) = 1 := by
  norm_num [SuperZeta.FieldWeights.conductorReading]

theorem row_abs_le_one (n j : ℕ) : |row n j| ≤ 1 := by
  have prime41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have prime457 : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  have prime1414835497 : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩
  have bound (a : ℤ) (p : ℕ) [Fact p.Prime] : |legendreSym p a| ≤ (1 : ℤ) := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    rcases jacobiSym.trichotomy a p with h | h | h <;> rw [h] <;> norm_num
  unfold row
  dsimp only
  split
  · unfold SuperZeta.FieldWeights.conductorReading
    rw [abs_mul, abs_mul]
    calc
      _ ≤ |legendreSym 41 ((j : ℤ) + 1 + ↑(n - (j+1)*(j+1)).sqrt * 32)| * 1 * 1 := by
        push_cast
        gcongr <;> apply bound
      _ ≤ 1 := by simpa using bound ((j : ℤ) + 1 + ↑(n - (j+1)*(j+1)).sqrt * 32) 41
  · norm_num

theorem coeff_zero : coeff 0 = 0 := by simp [coeff]

theorem coeff_one : coeff 1 = 1 := by
  norm_num [coeff, row, SuperZeta.FieldWeights.conductorReading]

theorem coeff_abs_le (n : ℕ) : |(coeff n : ℝ)| ≤ n := by
  have hn : n.sqrt ≤ n := Nat.sqrt_le_self n
  have h : |coeff n| ≤ (n.sqrt : ℤ) := by
    unfold coeff
    calc
      _ ≤ ∑ j ∈ Finset.range n.sqrt, |row n j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n.sqrt, (1 : ℤ) := Finset.sum_le_sum (fun j _ => row_abs_le_one n j)
      _ = _ := by simp
  exact_mod_cast h.trans (Int.ofNat_le.mpr hn)

/-- The norm of the discriminant of the chosen Gaussian quadratic. -/
def conductorNorm : ℕ := 41 * 457 * 1414835497

noncomputable def scale : ℝ := Real.sqrt conductorNorm / Real.pi

theorem scale_pos : 0 < scale := by
  unfold scale conductorNorm
  positivity

theorem scale_lt : scale < 1640000 := by
  have hs : Real.sqrt (conductorNorm : ℝ) < 5148765 := by
    apply (Real.sqrt_lt (by positivity) (by norm_num)).mpr
    norm_num [conductorNorm]
  unfold scale
  apply (div_lt_iff₀ Real.pi_pos).mpr
  linarith [Real.pi_gt_d2]

theorem exponential_left_endpoint : (65600000 : ℝ) < Real.exp 18 := by
  have h₁ : (2.71828 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.71828) h₁ 18
  have he : Real.exp (18 : ℝ) = Real.exp 1 ^ 18 := by norm_num [← Real.exp_nat_mul]
  rw [← he] at hp
  norm_num at hp ⊢
  linarith

noncomputable def theta (u : ℝ) : ℝ :=
  ∑' n : ℕ, (coeff n : ℝ) * (Real.exp (-u))^n

noncomputable def kernel (x : ℝ) : ℝ := Real.exp (x/2) * theta (Real.exp x / scale)

theorem theta_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => (coeff n : ℝ) * (Real.exp (-u))^n) := by
  have hr : ‖Real.exp (-u)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  refine Summable.of_norm_bounded _ (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.exp (-u))^n)]
  exact mul_le_mul_of_nonneg_right (coeff_abs_le n) (by positivity)

theorem theta_abs_le {u : ℝ} (hu : 0 < u) :
    |theta u| ≤ Real.exp (-u) / (1 - Real.exp (-u))^2 := by
  have hr : ‖Real.exp (-u)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hterm (n : ℕ) : |(coeff n : ℝ) * (Real.exp (-u))^n| ≤ n * (Real.exp (-u))^n := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.exp (-u))^n)]
    exact mul_le_mul_of_nonneg_right (coeff_abs_le n) (by positivity)
  unfold theta
  calc
    _ ≤ ∑' n : ℕ, |(coeff n : ℝ) * (Real.exp (-u))^n| := by
      simpa only [← Real.norm_eq_abs] using norm_tsum_le_tsum_norm (theta_summable hu).norm
    _ ≤ ∑' n : ℕ, (n : ℝ) * (Real.exp (-u))^n :=
      Summable.tsum_le_tsum hterm (theta_summable hu).abs hsum.summable
    _ = _ := hsum.tsum_eq

theorem theta_first_term {u : ℝ} (hu : 0 < u) :
    |theta u - Real.exp (-u)| ≤
      Real.exp (-u) / (1 - Real.exp (-u))^2 - Real.exp (-u) := by
  let r := Real.exp (-u)
  let f : ℕ → ℝ := fun n => (coeff n : ℝ) * r^n
  let g : ℕ → ℝ := fun n => (n : ℝ) * r^n
  have hr : ‖r‖ < 1 := by
    change |Real.exp (-u)| < 1
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hs := (theta_summable hu).sum_add_tsum_nat_add 2
  have ht := hg.summable.sum_add_tsum_nat_add 2
  change (∑ n ∈ Finset.range 2, f n) + (∑' n, f (n+2)) = theta u at hs
  change (∑ n ∈ Finset.range 2, g n) + (∑' n, g (n+2)) = (∑' n, g n) at ht
  have hf2 : (∑ n ∈ Finset.range 2, f n) = r := by
    norm_num [Finset.sum_range_succ, f, coeff_zero, coeff_one]
  have hg2 : (∑ n ∈ Finset.range 2, g n) = r := by
    norm_num [Finset.sum_range_succ, g]
  rw [hf2] at hs
  rw [hg2] at ht
  have ht' : HasSum (fun n => g (n+2)) (r / (1-r)^2 - r) := by
    have h := hg.summable.comp_injective (fun a b hab => Nat.add_right_cancel hab :
      Function.Injective (fun n : ℕ => n+2))
    change Summable (fun n => g (n+2)) at h
    have hh : (∑' n, g (n+2)) = r / (1-r)^2 - r := by
      have hh₀ : (∑' n, g n) = r / (1-r)^2 := hg.tsum_eq
      linarith
    rw [← hh]
    exact h.hasSum
  have hnorm (n : ℕ) : ‖f (n+2)‖ ≤ g (n+2) := by
    simp only [f, g, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r^(n+2))]
    exact mul_le_mul_of_nonneg_right (coeff_abs_le (n+2)) (by positivity)
  have hdiff : theta u - r = ∑' n, f (n+2) := by linarith
  rw [show Real.exp (-u) = r from rfl, hdiff]
  simpa only [Real.norm_eq_abs] using tsum_of_norm_bounded ht' hnorm

private theorem exp_neg_lt_quarter {u : ℝ} (hu : 2 ≤ u) : Real.exp (-u) < 1/4 := by
  have he : (4 : ℝ) < Real.exp (2:ℝ) := by
    rw [show Real.exp (2:ℝ) = Real.exp 1 ^ 2 by norm_num [← Real.exp_nat_mul]]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  norm_num
  exact he.trans_le (Real.exp_le_exp.mpr hu)

theorem geometric_majorant {u : ℝ} (hu : 2 ≤ u) :
    Real.exp (-u) / (1-Real.exp (-u))^2 < 2 * Real.exp (-u) := by
  have hr := exp_neg_lt_quarter hu
  have hsq : (1/2 : ℝ) < (1-Real.exp (-u))^2 := by nlinarith [sq_nonneg (1/4-Real.exp (-u))]
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith [mul_pos (Real.exp_pos (-u)) (sub_pos.mpr hsq)]

theorem theta_pos_of_two_le {u : ℝ} (hu : 2 ≤ u) : 0 < theta u := by
  have h := (abs_le.mp (theta_first_term (by linarith : 0 < u))).1
  linarith [geometric_majorant hu]

theorem kernel_continuousOn : ContinuousOn kernel (Ici (0 : ℝ)) := by
  unfold kernel theta
  apply ContinuousOn.mul (by fun_prop)
  let r := Real.exp (-(1 / scale))
  have hr : ‖r‖ < 1 := by
    change |Real.exp (-(1/scale))| < 1
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr scale_pos)
  refine continuousOn_tsum (fun n => by fun_prop)
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable ?_
  intro n x hx
  have hx0 : 0 ≤ x := hx
  have harg : 1 / scale ≤ Real.exp x / scale :=
    div_le_div_of_nonneg_right (Real.one_le_exp_iff.mpr hx0) scale_pos.le
  have hpower : Real.exp (-(Real.exp x / scale))^n ≤ r^n := by
    apply pow_le_pow_left₀ (Real.exp_pos _).le _ n
    exact Real.exp_le_exp.mpr (neg_le_neg harg)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-(Real.exp x / scale))^n)]
  exact mul_le_mul (coeff_abs_le n) hpower (by positivity) (by positivity)

theorem scale_at_tail (x : ℝ) :
    40 * Real.exp (x-18) < Real.exp x / scale := by
  have h₁ : (40 : ℝ) < Real.exp 18 / scale := by
    apply (lt_div_iff₀ scale_pos).mpr
    linarith [scale_lt, exponential_left_endpoint]
  have h₂ := mul_lt_mul_of_pos_left h₁ (Real.exp_pos (x-18))
  have he : Real.exp (x-18) * Real.exp 18 = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, he, mul_comm (Real.exp (x-18)) 40] at h₂
  exact h₂

theorem kernel_pos_on_tail {x : ℝ} (hx : 18 ≤ x) : 0 < kernel x := by
  have h := scale_at_tail x
  have he : 1 ≤ Real.exp (x-18) := Real.one_le_exp_iff.mpr (by linarith)
  exact mul_pos (Real.exp_pos _) (theta_pos_of_two_le (by linarith))

theorem kernel_upper_on_tail {x : ℝ} (hx : 18 ≤ x) :
    kernel x ≤ 3 * Real.exp (x/2) * Real.exp (-40 * Real.exp (x-18)) := by
  have h := scale_at_tail x
  have he : 1 ≤ Real.exp (x-18) := Real.one_le_exp_iff.mpr (by linarith)
  let u := Real.exp x / scale
  have hu : 2 ≤ u := by dsimp [u]; linarith
  have ht := (le_abs_self _).trans (theta_abs_le (by linarith : 0 < u))
  have hb : Real.exp (-u) ≤ Real.exp (-40 * Real.exp (x-18)) :=
    Real.exp_le_exp.mpr (by dsimp [u]; linarith)
  calc
    kernel x ≤ Real.exp (x/2) * (2 * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left (ht.trans (geometric_majorant hu).le) (by positivity)
    _ ≤ Real.exp (x/2) * (2 * Real.exp (-40 * Real.exp (x-18))) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (Real.exp_pos (x/2)).le (Real.exp_pos (-40 * Real.exp (x-18))).le]

open MeasureTheory

theorem weighted_tail :
    IntegrableOn (fun x => (2*kernel x*x^2) * Real.exp (x/20)) (Ioi 18) ∧
      (∫ x in Ioi 18, (2*kernel x*x^2) * Real.exp (x/20)) < (1:ℝ)/10^10 := by
  refine GaussianSideError.tail_of_kernel_majorant
    (fun x hx => (kernel_pos_on_tail hx.le).le)
    (fun x hx => kernel_upper_on_tail hx.le) ?_
  have hs : Ioi (18:ℝ) ⊆ Ici 0 := fun x hx => by
    rw [mem_Ici]
    linarith [mem_Ioi.mp hx]
  have hc := kernel_continuousOn.mono hs
  have hc' : ContinuousOn (fun x => (2*kernel x*x^2) * Real.exp (x/20)) (Ioi 18) := by
    fun_prop
  exact hc'.aestronglyMeasurable measurableSet_Ioi

#print axioms sign_at_73
#print axioms coeff_abs_le
#print axioms weighted_tail

end QuarticKernel
