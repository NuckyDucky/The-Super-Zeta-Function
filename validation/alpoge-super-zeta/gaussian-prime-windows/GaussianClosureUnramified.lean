import ArchivedGaussianRetainedNormWindow
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! Primes in the retained window of the actual splitting field eventually
avoid its discriminant. The local exponent condition uses membership in
the square of a prime ideal, so we relate it to the ramification index. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open Finset NumberField UniqueFactorizationMonoid

noncomputable section

def rationalPrimeIdeal (p : ℕ) : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)

theorem rationalPrimeIdeal_isMaximal {p : ℕ} (hp : p.Prime) :
    (rationalPrimeIdeal p).IsMaximal :=
  (Nat.prime_iff_prime_int.mp hp).isMaximal_span_singleton

private theorem rationalPrimeIdeal_ne_bot {p : ℕ} (hp : p.Prime) :
    rationalPrimeIdeal p ≠ ⊥ := by
  simpa only [rationalPrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℤ) ≠ 0)

private theorem rationalPrimeIdeal_map (p : ℕ) :
    (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 L)) =
      Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)) := by
  simp [rationalPrimeIdeal, Ideal.map_span]

theorem mem_closurePrimeFiber_iff {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 L)} :
    P ∈ closurePrimeFiber p ↔ P ∈ (rationalPrimeIdeal p).primesOver (𝓞 L) := by
  let : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
  change P ∈ (normalizedFactors (Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L)))).toFinset ↔ _
  rw [Multiset.mem_toFinset, ← rationalPrimeIdeal_map,
    Ideal.mem_primesOver_iff_mem_normalizedFactors _ (rationalPrimeIdeal_ne_bot hp)]

theorem closurePrimeFiber_unramified {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr L) {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p) :
    (p : 𝓞 L) ∉ P ^ 2 := by
  classical
  have hf := (mem_closurePrimeFiber_iff hp).mp hP
  let : P.IsPrime := hf.1
  let : P.LiesOver (rationalPrimeIdeal p) := hf.2
  have hSpan : (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot (rationalPrimeIdeal_ne_bot hp)
  have hLe : (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 L)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, Ideal.over_def P (rationalPrimeIdeal p)]
  have hMax : P.IsMaximal := hf.1.isMaximal (ne_bot_of_le_ne_bot hSpan hLe)
  let : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L)
      (Nat.prime_iff_prime_int.mp hp)).mp hd P hMax hf.2
  intro hPow
  have hCount : (normalizedFactors ((rationalPrimeIdeal p).map
      (algebraMap ℤ (𝓞 L)))).count P = 1 := by
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hSpan,
      Ideal.ramificationIdx_eq_one]
  have hDiv : P ^ 2 ∣ (rationalPrimeIdeal p).map (algebraMap ℤ (𝓞 L)) :=
    Ideal.dvd_iff_le.mpr (by
      rw [rationalPrimeIdeal_map, Ideal.span_singleton_le_iff_mem]
      exact hPow)
  have he := pow_dvd_iff_le_emultiplicity.mp hDiv
  have hi : Irreducible P :=
    (Ideal.prime_of_isPrime (ne_bot_of_le_ne_bot hSpan hLe) hf.1).irreducible
  rw [emultiplicity_eq_count_normalizedFactors hi hSpan, normalize_eq, hCount] at he
  exact (by decide : ¬ ((2 : ℕ) : ℕ∞) ≤ (1 : ℕ∞)) he

theorem retained_prime_gt_of_cutoff {M : ℕ} {x : ℝ} (hx : ((M : ℝ) + 1) ^ 2 ≤ x)
    {p : ℕ} (hp : p ∈ retainedPrimes x) : M < p := by
  classical
  have hh : p ∈ (range (⌊x⌋₊ + 1)).filter
      (fun n : ℕ => gaussianSqrtTriangleScale x ≤ (n : ℝ) ∧ n.Prime) := hp
  have hLow := (mem_filter.mp hh).2.1
  have hRoot : (M : ℝ) + 1 ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le hx
  unfold gaussianSqrtTriangleScale at hLow
  exact_mod_cast (show (M : ℝ) < p by linarith)

/-- At every sufficiently late cutoff all retained primes are unramified
in the ideal-power formulation used by the norm-window theorem. -/
theorem eventually_retained_unramified :
    ∃ X₀ : ℝ, ∀ x ≥ X₀, ∀ p ∈ retainedPrimes x, ∀ P ∈ closurePrimeFiber p,
      (p : 𝓞 L) ∉ P ^ 2 := by
  classical
  refine ⟨(((discr L).natAbs : ℝ) + 1) ^ 2, fun x hx p hp P hP => ?_⟩
  have hp' : p.Prime := (mem_filter.mp
    (show p ∈ (range (⌊x⌋₊ + 1)).filter
      (fun n : ℕ => gaussianSqrtTriangleScale x ≤ (n : ℝ) ∧ n.Prime) from hp)).2.2
  apply closurePrimeFiber_unramified hp' _ hP
  intro hd
  have hDvd : p ∣ (discr L).natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) hDvd))
    (retained_prime_gt_of_cutoff hx hp)

#print axioms mem_closurePrimeFiber_iff
#print axioms closurePrimeFiber_unramified
#print axioms retained_prime_gt_of_cutoff
#print axioms eventually_retained_unramified

end
end GaussianQuarticClosure
end AlpogeSuperZeta
