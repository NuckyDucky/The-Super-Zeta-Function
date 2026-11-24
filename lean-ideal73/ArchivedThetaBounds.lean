import ArchivedGaussianMellin
import Batteries.Tactic.OpenPrivate

/-! The continuity and exponential estimate used by the original Mellin
continuation, with the archived row enumeration in this toolchain. -/

open Filter Set Asymptotics
open scoped Topology

namespace QuarticModel

open private rowIndex from ArchivedQuarticLatticeCoefficients

private theorem archivedLatticeCoeff_abs_le (n : ℕ) : |(archivedLatticeCoeff n : ℝ)| ≤ n := by
  have hrow (j : ℕ) : |(archivedLatticeRow n j : ℝ)| ≤ 1 := by
    unfold archivedLatticeRow
    split_ifs
    · have h := archivedQuarterWeight_norm_le (rowIndex n j)
      simpa only [archivedQuarterWeight, rowIndex, ← Complex.ofReal_intCast,
        Complex.norm_real, Real.norm_eq_abs] using h
    · norm_num
  rw [archivedLatticeCoeff, Int.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range n.sqrt, |(archivedLatticeRow n j : ℝ)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (Finset.range n.sqrt) (fun j => (archivedLatticeRow n j : ℝ))
    _ ≤ ∑ _j ∈ Finset.range n.sqrt, (1 : ℝ) := Finset.sum_le_sum fun j _ => hrow j
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast Nat.sqrt_le_self n

private theorem norm_exp_neg_lt_one {u : ℝ} (hu : 0 < u) : ‖Real.exp (-u)‖ < 1 := by
  rw [Real.norm_eq_abs, Real.abs_exp]
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)

private theorem archivedTheta_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => (archivedLatticeCoeff n : ℝ) * Real.exp (-u)^n) := by
  refine (hasSum_coe_mul_geometric_of_norm_lt_one (norm_exp_neg_lt_one hu)).summable.of_norm_bounded (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-u)^n)]
  exact mul_le_mul_of_nonneg_right (archivedLatticeCoeff_abs_le n) (by positivity)

private theorem archivedTheta_abs_le {u : ℝ} (hu : 0 < u) :
    |archivedTheta u| ≤ Real.exp (-u)/(1-Real.exp (-u))^2 := by
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one (norm_exp_neg_lt_one hu)
  have hterm (n : ℕ) : |(archivedLatticeCoeff n : ℝ)*Real.exp (-u)^n| ≤ n*Real.exp (-u)^n := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-u)^n)]
    exact mul_le_mul_of_nonneg_right (archivedLatticeCoeff_abs_le n) (by positivity)
  unfold archivedTheta
  calc
    _ ≤ ∑' n : ℕ, |(archivedLatticeCoeff n : ℝ)*Real.exp (-u)^n| := by
      simpa only [← Real.norm_eq_abs] using norm_tsum_le_tsum_norm (archivedTheta_summable hu).norm
    _ ≤ ∑' n : ℕ, (n : ℝ)*Real.exp (-u)^n :=
      Summable.tsum_le_tsum hterm (archivedTheta_summable hu).abs hsum.summable
    _ = _ := hsum.tsum_eq

theorem archivedTheta_exp_bound {u : ℝ} (hu : 2 ≤ u) : |archivedTheta u| ≤ 2*Real.exp (-u) := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show Real.exp (2 : ℝ) = Real.exp 1^2 by norm_num [← Real.exp_nat_mul]]
    nlinarith [Real.add_one_le_exp 1, Real.exp_pos 1]
  have he : Real.exp (-u) ≤ 1/4 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : 0 < (1/4 : ℝ))]
    norm_num
    exact h4.trans (Real.exp_le_exp.mpr hu)
  have hbase : 0 < 1-Real.exp (-u) := by linarith
  have hsq : 0 < (1-Real.exp (-u))^2 := by positivity
  refine (archivedTheta_abs_le (by linarith : 0 < u)).trans ?_
  apply (div_le_iff₀ hsq).mpr
  have hhalf : (1/2 : ℝ) ≤ (1-Real.exp (-u))^2 := by nlinarith [sq_nonneg (1/4-Real.exp (-u))]
  nlinarith [mul_nonneg (Real.exp_pos (-u)).le (sub_nonneg.mpr hhalf)]

private theorem archivedTheta_continuous_from {c : ℝ} (hc : 0 < c) : ContinuousOn archivedTheta (Ici c) := by
  unfold archivedTheta
  refine continuousOn_tsum (fun n => by fun_prop)
    (hasSum_coe_mul_geometric_of_norm_lt_one (norm_exp_neg_lt_one hc)).summable ?_
  intro n x hx
  have hr : Real.exp (-x) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (neg_le_neg hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-x)^n)]
  exact mul_le_mul (archivedLatticeCoeff_abs_le n) (pow_le_pow_left₀ (by positivity) hr n)
    (by positivity) (by positivity)

theorem archivedTheta_continuous_positive : ContinuousOn archivedTheta (Ioi 0) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  have h : 0 < x := hx
  refine ⟨Ioi (x/2), isOpen_Ioi, by simpa only [mem_Ioi] using (by linarith : x/2 < x),
    (archivedTheta_continuous_from (show 0 < x/2 by positivity)).mono ?_⟩
  intro y hy
  exact (show x/2 < y from hy.2).le

theorem archivedTheta_exponential_decay :
    (fun t : ℝ => (archivedTheta (t/archivedThetaScale) : ℂ)) =O[atTop]
      fun t => Real.exp (-(1/archivedThetaScale)*t) := by
  apply IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (2*archivedThetaScale)] with t ht
  have hu : 2 ≤ t/archivedThetaScale := (le_div_iff₀ archivedThetaScale_pos).2 ht
  rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
  have he : -(1/archivedThetaScale)*t = -(t/archivedThetaScale) := by ring
  rw [he]
  exact archivedTheta_exp_bound hu

#print axioms archivedTheta_continuous_positive
#print axioms archivedTheta_exponential_decay

end QuarticModel
