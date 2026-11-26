import ArchivedGaussianLogDerivative

/-! The higher powers in the archived Gaussian prime-norm ramp contribute
a convergent linear correction and an error of order at most x^θ for θ > 1/2. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Set
open scoped Classical

noncomputable section

/-- The actual Mangoldt coefficient restricted to prime powers with exponent at least two. -/
def gaussianHigherPrimeCoefficient (n : ℕ) : ℝ :=
  if n.Prime then 0 else vonMangoldt n * archivedGaussianPrimeWeight n

private abbrev HigherPower := {n : ℕ // IsPrimePow n ∧ ¬n.Prime}

private theorem higherPower_has_index (n : HigherPower) :
    ∃ pk : Nat.Primes × ℕ, (pk.1.val ^ (pk.2 + 2)) = n.val := by
  obtain ⟨p, j, hp, hj, heq⟩ := (isPrimePow_nat_iff n.val).mp n.property.1
  have hj' : 2 ≤ j := by
    by_contra! h
    have h1 : j = 1 := by omega
    apply n.property.2
    rwa [← heq, h1, pow_one]
  exact ⟨(⟨p, hp⟩, j - 2), by simpa [Nat.sub_add_cancel hj'] using heq⟩

private def higherPowerIndex (n : HigherPower) : Nat.Primes × ℕ :=
  (higherPower_has_index n).choose

private theorem higherPowerIndex_spec (n : HigherPower) :
    (higherPowerIndex n).1.val ^ ((higherPowerIndex n).2 + 2) = n.val :=
  (higherPower_has_index n).choose_spec

private theorem higherPowerIndex_injective : Function.Injective higherPowerIndex := by
  intro n m h
  apply Subtype.ext
  exact (higherPowerIndex_spec n).symm.trans (h ▸ higherPowerIndex_spec m)

set_option maxHeartbeats 450000 in
private theorem gaussianHigherPrime_summable_subtype {θ : ℝ} (hθ : 1 / 2 < θ) :
    Summable (fun n : HigherPower => |gaussianHigherPrimeCoefficient n.val| / (n.val : ℝ) ^ θ) := by
  let b (n : ℕ) := |gaussianHigherPrimeCoefficient n| / (n : ℝ) ^ θ
  let r := (2 : ℝ) ^ (-θ)
  let u (p : Nat.Primes) := 2 * (Real.log p.val / (p.val : ℝ) ^ (2 * θ))
  have hu_nonneg (p : Nat.Primes) : 0 ≤ u p :=
    mul_nonneg (by norm_num)
      (div_nonneg (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le))
        (Real.rpow_nonneg p.val.cast_nonneg _))
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show -θ < 0 by linarith)
    simpa [r] using h
  have hu : Summable u := by
    have hs : 1 < (((2 * θ : ℝ) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith
    have h := (LSeriesSummable_vonMangoldt
      (s := ((2 * θ : ℝ) : ℂ)) hs).norm
    have hp := (h.mul_left (2 : ℝ)).comp_injective
      (show Function.Injective (fun p : Nat.Primes => p.val) from Subtype.coe_injective)
    refine hp.congr (fun p => ?_)
    have hlog : 0 ≤ Real.log (p.val : ℝ) :=
      Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
    simp [u, LSeries.norm_term_eq, p.property.ne_zero,
      vonMangoldt_apply_prime p.property, Real.norm_eq_abs, abs_of_nonneg hlog]
  let majorant (pk : Nat.Primes × ℕ) := u pk.1 * r ^ pk.2
  have hm : Summable majorant := by
    have hgeom := summable_geometric_of_lt_one hr₀ hr₁
    apply (summable_prod_of_nonneg
      (f := majorant) (fun pk => mul_nonneg (hu_nonneg pk.1) (pow_nonneg hr₀ _))).2
    refine ⟨fun p => hgeom.mul_left (u p), ?_⟩
    simpa only [majorant, hgeom.tsum_mul_left] using hu.mul_right (∑' k : ℕ, r ^ k)
  change Summable (fun n : HigherPower => b n.val)
  refine (hm.comp_injective higherPowerIndex_injective).of_nonneg_of_le
    (fun _ => by dsimp [b]; positivity) ?_
  intro n
  change b n.val ≤ majorant (higherPowerIndex n)
  rcases hpk : higherPowerIndex n with ⟨p, k⟩
  have heq : p.val ^ (k + 2) = n.val := by
    simpa only [hpk] using higherPowerIndex_spec n
  have hl : 0 ≤ Real.log (p.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  have hq : (p.val : ℝ) ^ (-θ) ≤ r := by
    have h2 : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
    rw [show r = (2 : ℝ) ^ (-θ) from rfl, Real.rpow_neg p.val.cast_nonneg,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) h2 (by linarith))
  calc
    b n.val ≤ 2 * (Real.log p.val / (n.val : ℝ) ^ θ) := by
      dsimp [b]
      rw [gaussianHigherPrimeCoefficient, if_neg n.property.2,
        show vonMangoldt n.val = Real.log p.val by
          rw [← heq, vonMangoldt_apply_pow (by omega : k + 2 ≠ 0),
            vonMangoldt_apply_prime p.property],
        abs_mul, abs_of_nonneg hl, mul_comm (Real.log p.val), mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (archivedGaussianPrimeWeight_abs_le_two _) (by positivity)
    _ = u p * ((p.val : ℝ) ^ (-θ)) ^ k := by
      rw [← heq, Nat.cast_pow, ← Real.rpow_natCast_mul p.val.cast_nonneg,
        show ((k + 2 : ℕ) : ℝ) * θ = 2 * θ + θ * k by push_cast; ring,
        Real.rpow_add (by exact_mod_cast p.property.pos),
        Real.rpow_mul_natCast p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg, inv_pow]
      dsimp only [u]
      rw [← div_div, div_eq_mul_inv
        (Real.log (p.val : ℝ) / (p.val : ℝ) ^ (2 * θ)) (((p.val : ℝ) ^ θ) ^ k),
        ← mul_assoc]
    _ ≤ majorant (p, k) := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _) (hu_nonneg p)

/-- Absolute summability of the higher prime powers down to any exponent strictly above 1/2. -/
theorem gaussianHigherPrime_summable {θ : ℝ} (hθ : 1 / 2 < θ) :
    Summable (fun n : ℕ => |gaussianHigherPrimeCoefficient n| / (n : ℝ) ^ θ) := by
  let b (n : ℕ) := |gaussianHigherPrimeCoefficient n| / (n : ℝ) ^ θ
  let P : Set ℕ := {n | IsPrimePow n ∧ ¬n.Prime}
  have hsub : Summable (fun n : P => b n.val) := gaussianHigherPrime_summable_subtype hθ
  have hind : Summable (P.indicator b) := summable_subtype_iff_indicator.mp hsub
  refine hind.congr (fun n => ?_)
  by_cases hn : n ∈ P
  · exact indicator_of_mem hn _
  · rw [indicator_of_notMem hn]
    by_cases hp : n.Prime
    · simp [gaussianHigherPrimeCoefficient, hp]
    · have hpow : ¬IsPrimePow n := fun h => hn ⟨h, hp⟩
      simp [gaussianHigherPrimeCoefficient, hp, vonMangoldt_eq_zero_iff.mpr hpow]

#print axioms gaussianHigherPrime_summable

end
end AlpogeSuperZeta
