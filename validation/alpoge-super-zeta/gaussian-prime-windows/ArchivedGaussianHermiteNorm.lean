import GaussianDyadicFrobeniusWindow
import GaussianHermiteFrobeniusIdeal

/-! The same numerator polynomial reads both central Frobenius addresses.
Retaining the ideal factors in the dyadic band gives the sharp count. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget Finset NumberField UniqueFactorizationMonoid
open scoped Classical Pointwise

noncomputable section

local instance : IsGaloisGroup ClosureAut ℤ (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing ClosureAut ℤ (𝓞 L) ℚ L

private theorem arithmetic_reading_iff_chosen_central {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr L) {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p)
    (label : GaussianClosureGroup) (hl : label = 1 ∨ label = gaussianCentralElement) :
    (∀ a : 𝓞 L, Ideal.Quotient.mk P (integerAction label a) = (Ideal.Quotient.mk P a) ^ p) ↔
      closurePrimeLabel p = label := by
  obtain ⟨P₀, σ, hP₀, hσ, hg⟩ := closurePrimeLabel_arithmetic hp
  have hf := (mem_closurePrimeFiber_iff hp).mp hP
  have hf₀ := (mem_closurePrimeFiber_iff hp).mp hP₀
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  let : P₀.IsPrime := hf₀.1
  let : P.LiesOver (rationalPrimeIdeal p) := hf.2
  let : P₀.LiesOver (rationalPrimeIdeal p) := hf₀.2
  let : (rationalPrimeIdeal p).IsMaximal := rationalPrimeIdeal_isMaximal hp
  let : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L)
      (Nat.prime_iff_prime_int.mp hp)).mp hd P inferInstance hf.2
  obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (rationalPrimeIdeal p) P₀ P ClosureAut
  let τ : ClosureAut := γ * σ * γ⁻¹
  have hτ : IsArithFrobAt ℤ τ P := hγ ▸ hσ.conj γ
  have hc : Commute (closureGaloisEquiv γ) label := by
    rcases hl with rfl | rfl
    · exact Commute.one_right _
    · exact gaussianCentral_commute_all _
  have hc' : closureGaloisEquiv γ * label * (closureGaloisEquiv γ)⁻¹ = label := by
    rw [hc.eq, mul_inv_cancel_right]
  have hLabel : closureGaloisEquiv τ = label ↔ closurePrimeLabel p = label := by
    rw [hg]
    simp only [τ, map_mul, map_inv]
    exact ⟨fun h => mul_left_cancel (mul_right_cancel (h.trans hc'.symm)), fun h => h ▸ hc'⟩
  constructor
  · intro h
    let σ' : ClosureAut := closureGaloisEquiv.symm label
    have hcard : Nat.card (ℤ ⧸ P.under ℤ) = p := by
      rw [← Ideal.over_def P (rationalPrimeIdeal p)]
      exact (Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv).trans (Nat.card_zmod p)
    have hσ' : IsArithFrobAt ℤ σ' P := by
      intro a
      change σ' • a - a ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
      rw [hcard]
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk P (integerAction label a - a ^ p) = 0
      rw [map_sub, map_pow, h a, sub_self]
    have he := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt hσ' hτ P.primeCompl_le_nonZeroDivisors
    let : FaithfulSMul ClosureAut (𝓞 L) := IsGaloisGroup.faithful (A := ℤ)
    have he' : σ' = τ := eq_of_smul_eq_smul fun a : 𝓞 L => AlgHom.congr_fun he a
    exact hLabel.mp (he' ▸ closureGaloisEquiv.apply_symm_apply label)
  · intro h a
    simpa only [hLabel.mpr h] using arithmeticFrobenius_reading hp hP hτ a

private theorem dyadicPrime_gt_discriminant {x : ℝ}
    (hx : 2 * (((discr L).natAbs : ℝ) + 1) ≤ x) {p : ℕ} (hp : p ∈ dyadicPrimes x) :
    ¬ (p : ℤ) ∣ discr L := by
  have hl : x / 2 ≤ (p : ℝ) := (mem_filter.mp hp).2.2.1
  have hbig : (discr L).natAbs < p := by
    exact_mod_cast (show ((discr L).natAbs : ℝ) < (p : ℝ) by linarith)
  intro hd
  have hd' : p ∣ (discr L).natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hd
  exact hbig.not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) hd')

/-- Keep the Hermite value-ideal factors above primes in \([x/2,x)\). -/
def hermiteShellPart (x : ℝ) (label : GaussianClosureGroup) : Ideal (𝓞 L) :=
  ∏ p ∈ dyadicPrimes x, ∏ P ∈ closurePrimeFiber p,
    P ^ (normalizedFactors (hermiteFrobeniusIdeal ⌈x / 2⌉₊ (integerAction label).toRingHom)).count P

/-- Each matching rational prime contributes its eighth power to the shell norm. -/
theorem hermiteShellPart_factorization {x : ℝ}
    (hx : 2 * (((discr L).natAbs : ℝ) + 1) ≤ x)
    (label : GaussianClosureGroup) (hl : label = 1 ∨ label = gaussianCentralElement) :
    (hermiteShellPart x label).absNorm =
      ∏ p ∈ dyadicPrimes x, p ^ (8 * (if closurePrimeLabel p = label then 1 else 0)) := by
  unfold hermiteShellPart
  rw [map_prod]
  apply prod_congr rfl
  intro p hp
  have hmem : p.Prime ∧ x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x := (mem_filter.mp hp).2
  have hd := dyadicPrime_gt_discriminant hx hp
  let m := ⌈x / 2⌉₊
  have hlower : m ≤ p := Nat.ceil_le.mpr hmem.2.1
  have hupper : p < 2 * m := by
    have hm : x / 2 ≤ (m : ℝ) := Nat.le_ceil _
    exact_mod_cast (show (p : ℝ) < 2 * (m : ℝ) by linarith [hmem.2.2])
  let e : ℕ := if closurePrimeLabel p = label then 1 else 0
  have hE : (∏ P ∈ closurePrimeFiber p,
      P ^ (normalizedFactors (hermiteFrobeniusIdeal m (integerAction label).toRingHom)).count P) =
      (∏ P ∈ closurePrimeFiber p, P) ^ e := by
    rw [← prod_pow]
    apply prod_congr rfl
    intro P hP
    let : P.IsMaximal := closurePrimeFiber_isMaximal hmem.1 hP
    let : CharP (𝓞 L ⧸ P) p := closurePrimeFiber_charP hmem.1 hP
    congr 1
    rw [hermiteFrobeniusIdeal_count P _ hmem.1 hlower hupper
      (closurePrimeFiber_unramified hmem.1 hd hP)]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, e,
      arithmetic_reading_iff_chosen_central hmem.1 hd hP label hl]
  change (∏ P ∈ closurePrimeFiber p,
      P ^ (normalizedFactors (hermiteFrobeniusIdeal m (integerAction label).toRingHom)).count P).absNorm =
      p ^ (8 * e)
  rw [hE, map_pow,
    closurePrimeFiber_product hmem.1 (fun _ hP => closurePrimeFiber_unramified hmem.1 hd hP)]
  change (Ideal.span ({(p : 𝓞 L)} : Set (𝓞 L))).absNorm ^ e = p ^ (8 * e)
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, degree_eight, ← pow_mul]

theorem hermiteShellPart_log_norm {x : ℝ}
    (hx : 2 * (((discr L).natAbs : ℝ) + 1) ≤ x)
    (label : GaussianClosureGroup) (hl : label = 1 ∨ label = gaussianCentralElement) :
    Real.log ((hermiteShellPart x label).absNorm : ℝ) = 8 * dyadicFrobeniusLogMass label x := by
  rw [hermiteShellPart_factorization hx label hl, Nat.cast_prod, Real.log_prod]
  · have hs : dyadicFrobeniusLogMass label x =
        ∑ p ∈ dyadicPrimes x, if closurePrimeLabel p = label then Real.log (p : ℝ) else 0 :=
      sum_filter _ _
    rw [hs, mul_sum]
    apply sum_congr rfl
    intro p _
    by_cases hp : closurePrimeLabel p = label <;>
      simp [hp, Nat.cast_pow, Real.log_pow]
  · intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2.1
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ hprime.ne_zero)

def archivedGaussianHermiteNormWindow (x : ℝ) : ℝ :=
  (Real.log ((hermiteShellPart x gaussianCentralElement).absNorm : ℝ) -
    Real.log ((hermiteShellPart x 1).absNorm : ℝ)) / 4

theorem archivedGaussianHermiteNormWindow_eq {x : ℝ}
    (hx : 2 * (((discr L).natAbs : ℝ) + 1) ≤ x) (hc : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    archivedGaussianHermiteNormWindow x = archivedGaussianDyadicPrimeWindow x := by
  rw [archivedGaussianHermiteNormWindow, hermiteShellPart_log_norm hx _ (Or.inr rfl),
    hermiteShellPart_log_norm hx _ (Or.inl rfl), archivedGaussianDyadicPrimeWindow_eq_frobenius hc]
  ring

/-- The sharp dyadic criterion on the two retained Hermite norms. -/
theorem quartic_rh_of_archived_gaussian_hermite_norm_windows (hD : DirichletLZerosOnLine)
    (hWindow : GaussianCutoffWindowBound archivedGaussianHermiteNormWindow) :
    DedekindZetaRH QuarticModel.K := by
  let X₀ : ℝ := max (2 * (((discr L).natAbs : ℝ) + 1)) (2 * (26509772707289 + 1))
  apply quartic_rh_of_archived_gaussian_dyadic_prime_windows hD
  apply (gaussianCutoffWindowBound_iff_of_error (X₀ := X₀)
    (A := archivedGaussianHermiteNormWindow) (B := archivedGaussianDyadicPrimeWindow) ?_).mp hWindow
  intro θ _ _
  refine ⟨0, le_rfl, fun x hx => ?_⟩
  rw [archivedGaussianHermiteNormWindow_eq ((le_max_left _ _).trans hx)
    ((le_max_right _ _).trans hx), sub_self, abs_zero, zero_mul]

#print axioms arithmetic_reading_iff_chosen_central
#print axioms hermiteShellPart_factorization
#print axioms hermiteShellPart_log_norm
#print axioms archivedGaussianHermiteNormWindow_eq
#check quartic_rh_of_archived_gaussian_hermite_norm_windows
#print axioms quartic_rh_of_archived_gaussian_hermite_norm_windows

end
end GaussianQuarticClosure
end AlpogeSuperZeta
