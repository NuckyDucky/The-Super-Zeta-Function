import GaussianHermiteIntegratedWindow
import Mathlib.Analysis.PSeries

/-! The logarithmic second moment of the archived signed prime count.
Each prime contributes on its own half-open log interval. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArithmeticFunction MeasureTheory Set

noncomputable section

private def primeLogInterval (p : ℕ) : Set ℝ :=
  Ioc (Real.log (p : ℝ)) (Real.log (2 * (p : ℝ)))

private def primeLogContribution (p : ℕ) : ℝ → ℝ :=
  (primeLogInterval p).indicator (fun _ => archivedGaussianSignedPrimeWeight p)

private theorem signedPrimeWeight_eq_zero {p : ℕ} (hp : ¬p.Prime) :
    archivedGaussianSignedPrimeWeight p = 0 := by
  simp [archivedGaussianSignedPrimeWeight, hp]

private theorem primeLogContribution_eq (p : ℕ) (u : ℝ) :
    primeLogContribution p u =
      if p.Prime ∧ Real.exp u / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.exp u then
        -Real.log (p : ℝ) * archivedGaussianPrimeWeight p else 0 := by
  classical
  by_cases hp : p.Prime
  · have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have h₁ := Real.log_lt_iff_lt_exp (y := u) hp₀
    have h₂ := Real.le_log_iff_exp_le (x := u) (mul_pos (by norm_num : (0 : ℝ) < 2) hp₀)
    have h₃ : Real.exp u / 2 ≤ (p : ℝ) ↔ Real.exp u ≤ 2 * (p : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm (p : ℝ)]
    simp [primeLogContribution, primeLogInterval, indicator, h₁, h₂, h₃, and_comm,
      archivedGaussianSignedPrimeWeight, hp, vonMangoldt_apply_prime hp]
  · simp [primeLogContribution, signedPrimeWeight_eq_zero hp, hp]

private theorem dyadicPrimeWindow_eq_log_sum {u V : ℝ} (hu : u ≤ V) :
    archivedGaussianDyadicPrimeWindow (Real.exp u) =
      ∑ p ∈ Finset.range (⌊Real.exp V⌋₊ + 1), primeLogContribution p u := by
  classical
  rw [archivedGaussianDyadicPrimeWindow_eq_sum (Real.exp_nonneg _), Finset.sum_filter,
    ← Finset.sum_congr rfl (fun p _ => primeLogContribution_eq p u)]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ
    (Nat.floor_mono (Real.exp_le_exp.mpr hu))))
  intro p _ hp
  have hFloor : ⌊Real.exp u⌋₊ < p := Nat.lt_of_succ_le
    (by simpa only [Finset.mem_range, not_lt] using hp)
  have hP := (Nat.floor_lt (Real.exp_nonneg _)).mp hFloor
  simp [primeLogContribution_eq, not_lt_of_ge hP.le]

/-- The kernel is the integral of the exponential weight where both
primes contribute to the signed reading. -/
def dyadicPrimePairKernel (θ U V : ℝ) (p q : ℕ) : ℝ :=
  ∫ u in Icc U V ∩ (primeLogInterval p ∩ primeLogInterval q), Real.exp (-2 * θ * u)

theorem dyadicPrimePairKernel_nonneg (θ U V : ℝ) (p q : ℕ) :
    0 ≤ dyadicPrimePairKernel θ U V p q :=
  setIntegral_nonneg (measurableSet_Icc.inter (measurableSet_Ioc.inter measurableSet_Ioc))
    (fun _ _ => Real.exp_nonneg _)

theorem dyadicPrimePairKernel_comm (θ U V : ℝ) (p q : ℕ) :
    dyadicPrimePairKernel θ U V p q = dyadicPrimePairKernel θ U V q p := by
  rw [dyadicPrimePairKernel, dyadicPrimePairKernel, inter_comm (primeLogInterval p)]

theorem dyadicPrimePairKernel_eq_zero_of_twice_le {θ U V : ℝ} {p q : ℕ}
    (hp : 0 < p) (h : 2 * p ≤ q) :
    dyadicPrimePairKernel θ U V p q = 0 := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq : (2 : ℝ) * (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
  have hLog := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 2) hp₀) hq
  have he : primeLogInterval p ∩ primeLogInterval q = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact (not_lt_of_ge (hLog.trans' hu.1.2)) hu.2.1
  simp [dyadicPrimePairKernel, he]

private theorem expWeight_integrableOn_Icc (θ U V : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (-2 * θ * u)) (Icc U V) := by
  have h : Continuous (fun u : ℝ => Real.exp (-2 * θ * u)) := by fun_prop
  exact h.continuousOn.integrableOn_compact isCompact_Icc

private theorem dyadicPrimePairKernel_le_of_subset {θ U V l r : ℝ} {p q : ℕ}
    (hθ : 0 ≤ θ) (hlr : l ≤ r)
    (hSub : Icc U V ∩ (primeLogInterval p ∩ primeLogInterval q) ⊆ Icc l r) :
    dyadicPrimePairKernel θ U V p q ≤ (r - l) * Real.exp (-2 * θ * l) := by
  calc
    _ ≤ ∫ u in Icc l r, Real.exp (-2 * θ * u) :=
      setIntegral_mono_set (expWeight_integrableOn_Icc θ l r)
        (ae_of_all _ fun _ => Real.exp_nonneg _) (ae_of_all _ hSub)
    _ ≤ ∫ _ in Icc l r, Real.exp (-2 * θ * l) :=
      setIntegral_mono_on (expWeight_integrableOn_Icc θ l r) (integrableOn_const (by simp))
        measurableSet_Icc (fun _ hu => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hu.1 (by linarith)))
    _ = _ := by rw [setIntegral_const, Real.volume_real_Icc_of_le hlr, smul_eq_mul]

theorem dyadicPrimePairKernel_le_log_two {θ U V : ℝ} {p q : ℕ}
    (hθ : 0 ≤ θ) (hp : 0 < p) :
    dyadicPrimePairKernel θ U V p q ≤ Real.log 2 * (p : ℝ) ^ (-2 * θ) := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlr : Real.log (p : ℝ) ≤ Real.log (2 * (p : ℝ)) :=
    Real.log_le_log hp₀ (by linarith)
  have h := dyadicPrimePairKernel_le_of_subset (p := p) (q := q) (U := U) (V := V)
    hθ hlr (fun _ hu => ⟨hu.2.1.1.le, hu.2.1.2⟩)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp₀.ne', add_sub_cancel_right,
    mul_comm (-2 * θ) (Real.log (p : ℝ)),
    ← Real.rpow_def_of_pos hp₀] at h
  exact h

/-- A pair approaching the outer end of its overlap has an extra factor
proportional to the remaining length of that overlap. -/
theorem dyadicPrimePairKernel_le_outer_gap {θ U V : ℝ} {p q : ℕ}
    (hθ : 0 ≤ θ) (hq : 0 < q) (hq₂ : q ≤ 2 * p) :
    dyadicPrimePairKernel θ U V p q ≤
      ((2 * (p : ℝ) - (q : ℝ)) / (q : ℝ)) * (q : ℝ) ^ (-2 * θ) := by
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq₂' : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hq₂
  have hp₂ : 0 < 2 * (p : ℝ) := hq₀.trans_le hq₂'
  have h := dyadicPrimePairKernel_le_of_subset (p := p) (q := q) (U := U) (V := V) hθ
    (Real.log_le_log hq₀ hq₂') (fun _ hu => ⟨hu.2.2.1.le, hu.2.1.2⟩)
  rw [← Real.log_div hp₂.ne' hq₀.ne', mul_comm (-2 * θ) (Real.log (q : ℝ)),
    ← Real.rpow_def_of_pos hq₀] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq₀.le _)
  have he : (2 * (p : ℝ) - (q : ℝ)) / (q : ℝ) = 2 * (p : ℝ) / (q : ℝ) - 1 := by
    rw [sub_div, div_self hq₀.ne']
  rw [he]
  exact Real.log_le_sub_one_of_pos (div_pos hp₂ hq₀)

/-- The signed dyadic prime count has an exact finite pair expansion on
each bounded logarithmic window. -/
def archivedGaussianDyadicSecondMoment (θ U V : ℝ) : ℝ :=
  ∫ u in Icc U V, (archivedGaussianDyadicPrimeWindow (Real.exp u)) ^ 2 * Real.exp (-2 * θ * u)

private def dyadicPrimePairIntegrand (θ : ℝ) (p q : ℕ) : ℝ → ℝ :=
  fun u => (archivedGaussianSignedPrimeWeight p * archivedGaussianSignedPrimeWeight q) *
    (primeLogInterval p ∩ primeLogInterval q).indicator (fun v => Real.exp (-2 * θ * v)) u

private theorem dyadicPrimePairIntegrand_eq (θ : ℝ) (p q : ℕ) (u : ℝ) :
    dyadicPrimePairIntegrand θ p q u =
      primeLogContribution p u * primeLogContribution q u * Real.exp (-2 * θ * u) := by
  by_cases hp : u ∈ primeLogInterval p <;> by_cases hq : u ∈ primeLogInterval q <;>
    simp [dyadicPrimePairIntegrand, primeLogContribution, hp, hq]

private theorem dyadicPrimePairIntegrand_integrableOn (θ U V : ℝ) (p q : ℕ) :
    IntegrableOn (dyadicPrimePairIntegrand θ p q) (Icc U V) :=
  ((expWeight_integrableOn_Icc θ U V).indicator
    (measurableSet_Ioc.inter measurableSet_Ioc)).const_mul _

private theorem dyadicSecondMoment_integrand_eq (θ V : ℝ) {u : ℝ} (hu : u ≤ V) :
    (archivedGaussianDyadicPrimeWindow (Real.exp u)) ^ 2 * Real.exp (-2 * θ * u) =
      ∑ p ∈ Finset.range (⌊Real.exp V⌋₊ + 1), ∑ q ∈ Finset.range (⌊Real.exp V⌋₊ + 1),
        dyadicPrimePairIntegrand θ p q u := by
  simp only [dyadicPrimeWindow_eq_log_sum hu, dyadicPrimePairIntegrand_eq, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  simp only [mul_comm (primeLogContribution _ u) (primeLogContribution _ u)]

theorem archivedGaussianDyadicSecondMoment_integrableOn (θ U V : ℝ) :
    IntegrableOn (fun u => (archivedGaussianDyadicPrimeWindow (Real.exp u)) ^ 2 *
      Real.exp (-2 * θ * u)) (Icc U V) := by
  have h : IntegrableOn (fun u => ∑ p ∈ Finset.range (⌊Real.exp V⌋₊ + 1),
      ∑ q ∈ Finset.range (⌊Real.exp V⌋₊ + 1), dyadicPrimePairIntegrand θ p q u) (Icc U V) :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
      dyadicPrimePairIntegrand_integrableOn θ U V p q
  exact h.congr_fun (fun _ hu => (dyadicSecondMoment_integrand_eq θ V hu.2).symm) measurableSet_Icc

theorem archivedGaussianDyadicSecondMoment_eq_pairs (θ U V : ℝ) :
    archivedGaussianDyadicSecondMoment θ U V =
      ∑ p ∈ Finset.range (⌊Real.exp V⌋₊ + 1), ∑ q ∈ Finset.range (⌊Real.exp V⌋₊ + 1),
        (archivedGaussianSignedPrimeWeight p * archivedGaussianSignedPrimeWeight q) *
          dyadicPrimePairKernel θ U V p q := by
  rw [archivedGaussianDyadicSecondMoment]
  rw [setIntegral_congr_fun measurableSet_Icc (fun _ hu => dyadicSecondMoment_integrand_eq θ V hu.2),
    integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ =>
      dyadicPrimePairIntegrand_integrableOn θ U V p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => dyadicPrimePairIntegrand_integrableOn θ U V p q)]
  apply Finset.sum_congr rfl
  intro q _
  have hs : MeasurableSet (primeLogInterval p ∩ primeLogInterval q) :=
    measurableSet_Ioc.inter measurableSet_Ioc
  simp only [dyadicPrimePairIntegrand, integral_const_mul, dyadicPrimePairKernel]
  rw [setIntegral_indicator hs]

#print axioms dyadicPrimePairKernel_eq_zero_of_twice_le
#print axioms dyadicPrimePairKernel_le_log_two
#print axioms dyadicPrimePairKernel_le_outer_gap
#print axioms archivedGaussianDyadicSecondMoment_integrableOn
#print axioms archivedGaussianDyadicSecondMoment_eq_pairs

end
end GaussianQuarticClosure
end AlpogeSuperZeta
