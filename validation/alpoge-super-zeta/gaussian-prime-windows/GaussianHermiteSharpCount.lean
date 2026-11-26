import GaussianHermiteOddValue
import GaussianDyadicCentralPrimeCriterion
import Mathlib.Data.Nat.Squarefree

/-! The marked prime product is a gcd of a single real integer value
and the rational comparison product. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget Finset QuarticModel
open scoped Classical

noncomputable section

def dyadicComparisonPrimes (x : ℝ) : Finset ℕ :=
  (dyadicPrimes x).filter (fun p => p % 4 = 1 ∧ rationalNormSign p = 1)

def dyadicComparisonProduct (x : ℝ) : ℕ := ∏ p ∈ dyadicComparisonPrimes x, p

def hermiteShellRealCoordinate (x : ℝ) : ℤ :=
  (archivedHermiteOddValue ⌈x / 2⌉₊).re

private theorem central_ne_one : gaussianCentralElement ≠ (1 : GaussianClosureGroup) := by
  decide +kernel

private theorem dyadic_weight_alignment {x : ℝ} {p : ℕ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) (hp : p ∈ dyadicPrimes x) :
    p.Prime ∧ p ≠ 2 ∧ p.Coprime 26509772707289 ∧
    archivedGaussianPrimeWeight p = (closurePrimeTrace (closurePrimeLabel p) : ℝ) := by
  have hP := (mem_filter.mp hp).2.1
  have hbig := dyadicPrime_gt_conductor hx hp
  have h₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ 26509772707289).trans_lt hbig)
  have hD : p.Coprime 26509772707289 := hP.coprime_iff_not_dvd.mpr fun hd =>
    (not_le_of_gt hbig) (Nat.le_of_dvd (by decide) hd)
  exact ⟨hP, h₂, hD, closurePrimeLabel_weight hP hbig⟩

theorem dyadicComparisonPrime_read {x : ℝ} {p : ℕ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) (hp : p ∈ dyadicComparisonPrimes x) :
    (hermitePrimeScale ⌈x / 2⌉₊ : ZMod p) ≠ 0 ∧
      ((closurePrimeLabel p = 1 ∧ (hermiteShellRealCoordinate x : ZMod p) =
        (hermitePrimeScale ⌈x / 2⌉₊ : ZMod p)) ∨
       (closurePrimeLabel p = gaussianCentralElement ∧ (hermiteShellRealCoordinate x : ZMod p) =
        -(hermitePrimeScale ⌈x / 2⌉₊ : ZMod p))) := by
  obtain ⟨hP, hsplit, hNorm⟩ := mem_filter.mp hp
  have hBounds := (mem_filter.mp hP).2.2
  obtain ⟨hprime, _, hD, hWeight⟩ := dyadic_weight_alignment hx hP
  let m := ⌈x / 2⌉₊
  have hLow : m ≤ p := Nat.ceil_le.mpr hBounds.1
  have hHigh : p < 2 * m := by
    have hceil : x / 2 ≤ (m : ℝ) := Nat.le_ceil (x / 2)
    exact_mod_cast (show (p : ℝ) < 2 * (m : ℝ) by linarith [hBounds.2])
  obtain ⟨e, he, hW, hRe, _⟩ := archivedHermiteOddValue_mod_comparison_prime
    hprime hLow hHigh hsplit hD hNorm
  refine ⟨hermitePrimeScale_cast_ne_zero hprime hLow, ?_⟩
  change (hermiteShellRealCoordinate x : ZMod p) =
    (hermitePrimeScale m : ZMod p) * (e : ZMod p) at hRe
  have hEq : (closurePrimeTrace (closurePrimeLabel p) : ℝ) = 2 * (e : ℝ) := hWeight.symm.trans hW
  rcases he with rfl | rfl
  · left
    refine ⟨?_, by simpa only [Int.cast_one, mul_one] using hRe⟩
    by_contra hnot
    by_cases hz : closurePrimeLabel p = gaussianCentralElement <;>
      norm_num [closurePrimeTrace, hnot, hz, central_ne_one] at hEq
  · right
    refine ⟨?_, by simpa only [Int.cast_neg, Int.cast_one, mul_neg, mul_one] using hRe⟩
    by_contra hnot
    by_cases hz : closurePrimeLabel p = 1 <;>
      norm_num [closurePrimeTrace, hnot, hz, Ne.symm central_ne_one] at hEq

theorem dyadicComparisonPrimes_filter_eq_class {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x)
    {g : GaussianClosureGroup} (hg : g = 1 ∨ g = gaussianCentralElement) :
    (dyadicComparisonPrimes x).filter (fun p => closurePrimeLabel p = g) =
      (dyadicPrimes x).filter (fun p => closurePrimeLabel p = g) := by
  ext p
  simp only [dyadicComparisonPrimes, mem_filter]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun ⟨hp, hg'⟩ => ⟨⟨hp, ?_⟩, hg'⟩⟩
  obtain ⟨hprime, h₂, hD, hW⟩ := dyadic_weight_alignment hx hp
  let : Fact p.Prime := ⟨hprime⟩
  apply (archivedGaussianPrimeWeight_ne_zero_iff h₂ hD).mp
  rw [hW, hg']
  rcases hg with rfl | rfl
  · norm_num [closurePrimeTrace, Ne.symm central_ne_one]
  · norm_num [closurePrimeTrace, central_ne_one]

private theorem prime_product_gcd_filter (S : Finset ℕ) (a : ℕ)
    (hs : ∀ p ∈ S, p.Prime) :
    Nat.gcd (∏ p ∈ S, p) a = ∏ p ∈ S.filter (fun p => p ∣ a), p := by
  let P := ∏ p ∈ S, p
  have hP : Squarefree P := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hne
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hne)
    · exact fun p hp => (hs p hp).squarefree
  have hg := Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left P a) hP
  have he : (P.gcd a).primeFactors = S.filter (fun p => p ∣ a) := by
    ext p
    rw [Nat.mem_primeFactors_of_ne_zero hg.ne_zero, mem_filter]
    constructor
    · rintro ⟨hp, hd⟩
      obtain ⟨q, hq, hd'⟩ := (hp.prime.dvd_finsetProd_iff _).mp (hd.trans (Nat.gcd_dvd_left P a))
      have heq := ((hs q hq).dvd_iff_eq hp.ne_one).mp hd'
      exact ⟨heq ▸ hq, hd.trans (Nat.gcd_dvd_right P a)⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hs p hp, Nat.dvd_gcd (dvd_prod_of_mem _ hp) hd⟩
  rw [← he, Nat.prod_primeFactors_of_squarefree hg]

def hermiteShellSignedInteger (x : ℝ) (g : GaussianClosureGroup) : ℤ :=
  if g = gaussianCentralElement then hermiteShellRealCoordinate x + hermitePrimeScale ⌈x / 2⌉₊
    else hermiteShellRealCoordinate x - hermitePrimeScale ⌈x / 2⌉₊

def hermiteShellClassProduct (x : ℝ) (g : GaussianClosureGroup) : ℕ :=
  ∏ p ∈ (dyadicPrimes x).filter (fun p => closurePrimeLabel p = g), p

private theorem cast_two_ne_zero {p : ℕ} (hp : p.Prime) (h : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun hd => h ((Nat.dvd_prime_two_le Nat.prime_two hp.two_le).mp hd)

theorem dyadicComparisonPrime_dvd_iff {x : ℝ} {p : ℕ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) (hp : p ∈ dyadicComparisonPrimes x)
    {g : GaussianClosureGroup} (hg : g = 1 ∨ g = gaussianCentralElement) :
    p ∣ (hermiteShellSignedInteger x g).natAbs ↔ closurePrimeLabel p = g := by
  have hprime := (mem_filter.mp (mem_filter.mp hp).1).2.1
  let : Fact p.Prime := ⟨hprime⟩
  have h₂ : p ≠ 2 := by have h := (mem_filter.mp hp).2.1; omega
  have h2 := cast_two_ne_zero hprime h₂
  obtain ⟨hScale, hres⟩ := dyadicComparisonPrime_read hx hp
  change (p : ℤ).natAbs ∣ (hermiteShellSignedInteger x g).natAbs ↔ _
  rw [Int.natAbs_dvd_natAbs, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hg with rfl | rfl
  · simp only [hermiteShellSignedInteger, Ne.symm central_ne_one, if_false, Int.cast_sub]
    rcases hres with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simp [hl, hr]
    · have h : -(hermitePrimeScale ⌈x / 2⌉₊ : ZMod p) -
          (hermitePrimeScale ⌈x / 2⌉₊ : ZMod p) ≠ 0 := by
        rw [sub_eq_add_neg, ← neg_add, ← two_mul]
        exact neg_ne_zero.mpr (mul_ne_zero h2 hScale)
      simp only [hl, hr, h, central_ne_one]
  · simp only [hermiteShellSignedInteger, if_true, Int.cast_add]
    rcases hres with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · have h : (hermitePrimeScale ⌈x / 2⌉₊ : ZMod p) +
          (hermitePrimeScale ⌈x / 2⌉₊ : ZMod p) ≠ 0 := by
        rw [← two_mul]
        exact mul_ne_zero h2 hScale
      simp only [hl, hr, h, Ne.symm central_ne_one]
    · simp [hl, hr]

theorem dyadicComparisonProduct_gcd_eq_class {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x)
    {g : GaussianClosureGroup} (hg : g = 1 ∨ g = gaussianCentralElement) :
    Nat.gcd (dyadicComparisonProduct x) (hermiteShellSignedInteger x g).natAbs =
      hermiteShellClassProduct x g := by
  have hprime (p : ℕ) (hp : p ∈ dyadicComparisonPrimes x) : p.Prime :=
    (mem_filter.mp (mem_filter.mp hp).1).2.1
  rw [dyadicComparisonProduct, prime_product_gcd_filter _ _ hprime, hermiteShellClassProduct,
    ← dyadicComparisonPrimes_filter_eq_class hx hg]
  congr 1
  exact filter_congr fun p hp => dyadicComparisonPrime_dvd_iff hx hp hg

theorem log_hermiteShellClassProduct (x : ℝ) (g : GaussianClosureGroup) :
    Real.log (hermiteShellClassProduct x g : ℝ) = dyadicFrobeniusLogMass g x := by
  rw [hermiteShellClassProduct, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro p hp
    exact Nat.cast_ne_zero.mpr ((mem_filter.mp (mem_filter.mp hp).1).2.1).ne_zero

def archivedGaussianHermiteValueExcess (x : ℝ) : ℝ :=
  Real.log ((Nat.gcd (dyadicComparisonProduct x)
    (hermiteShellSignedInteger x gaussianCentralElement).natAbs : ℕ) : ℝ) - x / 16

theorem archivedGaussianHermiteValueExcess_eq {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    archivedGaussianHermiteValueExcess x = archivedGaussianCentralPrimeExcess x := by
  rw [archivedGaussianHermiteValueExcess, dyadicComparisonProduct_gcd_eq_class hx (Or.inr rfl),
    log_hermiteShellClassProduct, archivedGaussianCentralPrimeExcess]

theorem archivedGaussianHermiteValueExcess_window_iff :
    GaussianCutoffWindowBound archivedGaussianHermiteValueExcess ↔
      GaussianCutoffWindowBound archivedGaussianCentralPrimeExcess := by
  apply gaussianCutoffWindowBound_iff_of_error (X₀ := 2 * (26509772707289 + 1 : ℝ))
  intro t _ _
  refine ⟨0, le_rfl, fun x hx => ?_⟩
  rw [archivedGaussianHermiteValueExcess_eq hx, sub_self, abs_zero, zero_mul]

theorem quartic_rh_of_archived_gaussian_hermite_value_windows
    (hDir : DirichletLZerosOnLine)
    (hcut : GaussianCutoffWindowBound archivedGaussianHermiteValueExcess) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_sharp_central_windows hDir
    (archivedGaussianHermiteValueExcess_window_iff.mp hcut)

#check quartic_rh_of_archived_gaussian_hermite_value_windows
#print axioms dyadicComparisonPrime_read
#print axioms dyadicComparisonPrimes_filter_eq_class
#print axioms dyadicComparisonPrime_dvd_iff
#print axioms dyadicComparisonProduct_gcd_eq_class
#print axioms log_hermiteShellClassProduct
#print axioms archivedGaussianHermiteValueExcess_eq
#print axioms archivedGaussianHermiteValueExcess_window_iff
#print axioms quartic_rh_of_archived_gaussian_hermite_value_windows

end
end GaussianQuarticClosure
end AlpogeSuperZeta
