import GaussianHermiteSharpCount
import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-! A single congruence for the Hermite value puts separate divisibility
conditions on the sum and difference of two integers. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open Finset
open scoped Classical

noncomputable section

def hermiteResidueLattice (x : ℝ) (a b : ℤ) : Prop :=
  (dyadicComparisonProduct x : ℤ) ∣
    hermitePrimeScale ⌈x / 2⌉₊ * a - hermiteShellRealCoordinate x * b

private theorem intCast_prime_product_dvd_iff {S : Finset ℕ}
    (hPrime : ∀ p ∈ S, p.Prime) (n : ℤ) :
    ((∏ p ∈ S, p : ℕ) : ℤ) ∣ n ↔ ∀ p ∈ S, (p : ℤ) ∣ n := by
  constructor
  · intro h p hp
    have hd : p ∣ ∏ q ∈ S, q := dvd_prod_of_mem _ hp
    exact (Int.ofNat_dvd.mpr hd).trans h
  · intro h
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    apply Finset.prod_dvd_of_isRelPrime
    · intro p hp q hq hne
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hPrime p hp) (hPrime q hq)).mpr hne)
    · intro p hp
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (h p hp)

private theorem shellPrime_modulus {x : ℝ} {p : ℕ} (hp : p ∈ dyadicPrimes x) : p.Prime :=
  (mem_filter.mp hp).2.1

theorem hermiteResidueLattice_iff {x : ℝ} (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x)
    (a b : ℤ) :
    hermiteResidueLattice x a b ↔
      (hermiteShellClassProduct x gaussianCentralElement : ℤ) ∣ a + b ∧
      (hermiteShellClassProduct x 1 : ℤ) ∣ a - b := by
  let D := hermitePrimeScale ⌈x / 2⌉₊
  let R := hermiteShellRealCoordinate x
  have hS (p : ℕ) (hp : p ∈ dyadicComparisonPrimes x) : p.Prime :=
    shellPrime_modulus (mem_filter.mp hp).1
  have hC (g : GaussianClosureGroup) (p : ℕ)
      (hp : p ∈ (dyadicPrimes x).filter (fun q => closurePrimeLabel q = g)) : p.Prime :=
    shellPrime_modulus (mem_filter.mp hp).1
  have hne : gaussianCentralElement ≠ (1 : GaussianClosureGroup) := by decide +kernel
  have hAt (p : ℕ) (hp : p ∈ dyadicComparisonPrimes x) :
      ((p : ℤ) ∣ D * a - R * b ↔ (p : ℤ) ∣ a + b) ∧
        closurePrimeLabel p = gaussianCentralElement ∨
      ((p : ℤ) ∣ D * a - R * b ↔ (p : ℤ) ∣ a - b) ∧ closurePrimeLabel p = 1 := by
    let : Fact p.Prime := ⟨hS p hp⟩
    obtain ⟨hD, hP⟩ := dyadicComparisonPrime_read hx hp
    change (D : ZMod p) ≠ 0 at hD
    rcases hP with ⟨hg, hR⟩ | ⟨hg, hR⟩
    · right
      refine ⟨?_, hg⟩
      change (R : ZMod p) = (D : ZMod p) at hR
      simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_mul, hR,
        ← mul_sub, mul_eq_zero, hD, false_or]
    · left
      refine ⟨?_, hg⟩
      change (R : ZMod p) = -(D : ZMod p) at hR
      simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_add, Int.cast_mul,
        hR, neg_mul, sub_neg_eq_add, ← mul_add, mul_eq_zero, hD, false_or]
  rw [hermiteResidueLattice, dyadicComparisonProduct, hermiteShellClassProduct, hermiteShellClassProduct,
    intCast_prime_product_dvd_iff hS, intCast_prime_product_dvd_iff (hC _),
    intCast_prime_product_dvd_iff (hC _), ← dyadicComparisonPrimes_filter_eq_class hx (Or.inr rfl),
    ← dyadicComparisonPrimes_filter_eq_class hx (Or.inl rfl)]
  change (∀ p ∈ dyadicComparisonPrimes x, (p : ℤ) ∣ D * a - R * b) ↔ _
  constructor
  · intro h
    constructor
    · intro p hp
      obtain ⟨hS', hg⟩ := mem_filter.mp hp
      rcases hAt p hS' with ⟨hA, _⟩ | ⟨_, hB⟩
      · exact hA.mp (h p hS')
      · exact (hne (hg.symm.trans hB)).elim
    · intro p hp
      obtain ⟨hS', hg⟩ := mem_filter.mp hp
      rcases hAt p hS' with ⟨_, hA⟩ | ⟨hB, _⟩
      · exact (hne (hA.symm.trans hg)).elim
      · exact hB.mp (h p hS')
  · rintro ⟨hA, hB⟩ p hp
    rcases hAt p hp with ⟨h, hg⟩ | ⟨h, hg⟩
    · exact h.mpr (hA p (mem_filter.mpr ⟨hp, hg⟩))
    · exact h.mpr (hB p (mem_filter.mpr ⟨hp, hg⟩))

private theorem hermiteShellClassProduct_pos (x : ℝ) (g : GaussianClosureGroup) :
    0 < hermiteShellClassProduct x g := by
  apply prod_pos
  intro p hp
  exact (shellPrime_modulus (mem_filter.mp hp).1).pos

theorem hermiteResidueLattice_sum_lower {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) {a b : ℤ}
    (h : hermiteResidueLattice x a b) (hne : a + b ≠ 0) :
    hermiteShellClassProduct x gaussianCentralElement ≤ (a + b).natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr hne)
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr
    ((hermiteResidueLattice_iff hx a b).mp h).1

theorem hermiteResidueLattice_attains_sum {x : ℝ} (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    ∃ a b : ℤ, hermiteResidueLattice x a b ∧
      a + b = (hermiteShellClassProduct x gaussianCentralElement : ℤ) ∧
      a - b = (hermiteShellClassProduct x 1 : ℤ) := by
  have hOdd (g : GaussianClosureGroup) : Odd (hermiteShellClassProduct x g : ℤ) := by
    apply Odd.natCast
    apply Finset.prod_induction (fun p : ℕ => p) Odd (fun _ _ => Odd.mul) odd_one
    intro p hp
    have hd := (mem_filter.mp hp).1
    have h := dyadicPrime_gt_conductor hx hd
    exact (shellPrime_modulus hd).odd_of_ne_two (by omega)
  obtain ⟨r, hr⟩ := hOdd gaussianCentralElement
  obtain ⟨s, hs⟩ := hOdd 1
  let a := r + s + 1
  let b := r - s
  have hAdd : a + b = (hermiteShellClassProduct x gaussianCentralElement : ℤ) := by
    dsimp [a, b]
    linarith only [hr]
  have hSub : a - b = (hermiteShellClassProduct x 1 : ℤ) := by
    dsimp [a, b]
    linarith only [hs]
  refine ⟨a, b, (hermiteResidueLattice_iff hx a b).mpr ?_, hAdd, hSub⟩
  rw [hAdd, hSub]
  exact ⟨dvd_rfl, dvd_rfl⟩

theorem hermiteResidueLattice_signed_bound_iff {x B : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    (∃ a b : ℤ, hermiteResidueLattice x a b ∧ a + b ≠ 0 ∧
      Real.log ((a + b).natAbs : ℝ) - x / 16 ≤ B) ↔ archivedGaussianCentralPrimeExcess x ≤ B := by
  let P := hermiteShellClassProduct x gaussianCentralElement
  have hP : 0 < P := hermiteShellClassProduct_pos x gaussianCentralElement
  have hLog : Real.log (P : ℝ) - x / 16 = archivedGaussianCentralPrimeExcess x := by
    rw [show P = hermiteShellClassProduct x gaussianCentralElement from rfl,
      log_hermiteShellClassProduct, archivedGaussianCentralPrimeExcess]
  rw [← hLog]
  constructor
  · rintro ⟨a, b, hab, hs, hB⟩
    have he := hermiteResidueLattice_sum_lower hx hab hs
    exact (sub_le_sub_right (Real.log_le_log (by exact_mod_cast hP) (by exact_mod_cast he)) _).trans hB
  · intro hB
    obtain ⟨a, b, hab, hAdd, _⟩ := hermiteResidueLattice_attains_sum hx
    refine ⟨a, b, hab, ?_, ?_⟩
    · exact hAdd.trans_ne (by exact_mod_cast hP.ne')
    · simpa only [hAdd, Int.natAbs_natCast] using hB

#print axioms hermiteResidueLattice_iff
#print axioms hermiteResidueLattice_sum_lower
#print axioms hermiteResidueLattice_attains_sum
#print axioms hermiteResidueLattice_signed_bound_iff

end
end GaussianQuarticClosure
end AlpogeSuperZeta
