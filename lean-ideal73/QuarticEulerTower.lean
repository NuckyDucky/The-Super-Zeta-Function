import RelativeQuarticSplitting
import PrimePowerEulerSeries

/-! Group the actual quartic Euler factors at a rational prime by their
contraction to the Gaussian integers. -/

namespace QuarticModel

open NumberField UniqueFactorizationMonoid FieldCoefficientTransfer
open scoped Classical

noncomputable def gaussianPrimesAbove (p : ℕ) : Finset (Ideal GaussianInt) :=
  (normalizedFactors (Ideal.span {(p : GaussianInt)})).toFinset

private abbrev rationalPrimeIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

private theorem rationalPrimeIdeal_ne_bot (p : ℕ) [Fact p.Prime] :
    rationalPrimeIdeal p ≠ ⊥ := by
  simp [rationalPrimeIdeal, (Fact.out : p.Prime).ne_zero]

theorem mem_gaussianPrimesAbove (p : ℕ) [Fact p.Prime] {I : Ideal GaussianInt} :
    I ∈ gaussianPrimesAbove p ↔ I ∈ (rationalPrimeIdeal p).primesOver GaussianInt := by
  let : (rationalPrimeIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  simpa only [gaussianPrimesAbove, rationalPrimeIdeal, Multiset.mem_toFinset, Ideal.map_span,
    Set.image_singleton, map_natCast] using
    (Ideal.mem_primesOver_iff_mem_normalizedFactors GaussianInt (rationalPrimeIdeal_ne_bot p)).symm

private theorem mem_quarticPrimesAbove (p : ℕ) [Fact p.Prime] {P : Ideal (𝓞 K)} :
    P ∈ primesAbove K p ↔ P ∈ (rationalPrimeIdeal p).primesOver (𝓞 K) := by
  let : (rationalPrimeIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  simpa only [primesAbove, IdealPrimePower.primesAbove, rationalPrimeIdeal, Multiset.mem_toFinset, Ideal.map_span,
    Set.image_singleton, map_natCast] using
    (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) (rationalPrimeIdeal_ne_bot p)).symm

theorem gaussianPrimesAbove_isMaximal {p : ℕ} [Fact p.Prime] {I : Ideal GaussianInt}
    (hI : I ∈ gaussianPrimesAbove p) : I.IsMaximal := by
  let : (rationalPrimeIdeal p).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  exact Ideal.isMaximal_of_mem_primesOver ((mem_gaussianPrimesAbove p).mp hI)

theorem gaussianPrimesAbove_ne_bot {p : ℕ} [Fact p.Prime] {I : Ideal GaussianInt}
    (hI : I ∈ gaussianPrimesAbove p) : I ≠ ⊥ :=
  ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hI)

private theorem quartic_contracts_to_gaussian {p : ℕ} [Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesAbove K p) : P.under GaussianInt ∈ gaussianPrimesAbove p := by
  have hp := (mem_quarticPrimesAbove p).mp hP
  let : P.IsPrime := hp.1
  let : P.LiesOver (rationalPrimeIdeal p) := hp.2
  apply (mem_gaussianPrimesAbove p).mpr
  exact ⟨inferInstance, Ideal.LiesOver.tower_bot P (P.under GaussianInt) (rationalPrimeIdeal p)⟩

private theorem gaussian_fiber {p : ℕ} [Fact p.Prime] {I : Ideal GaussianInt}
    (hI : I ∈ gaussianPrimesAbove p) :
    (primesAbove K p).filter (fun P => P.under GaussianInt = I) =
      (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))).toFinset := by
  let : I.IsMaximal := gaussianPrimesAbove_isMaximal hI
  let : I.LiesOver (rationalPrimeIdeal p) := ((mem_gaussianPrimesAbove p).mp hI).2
  ext P
  rw [Finset.mem_filter, mem_quarticPrimesAbove, Multiset.mem_toFinset,
    ← Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K) (gaussianPrimesAbove_ne_bot hI)]
  constructor
  · rintro ⟨hP, he⟩
    exact ⟨hP.1, ⟨he.symm⟩⟩
  · intro hP
    let : P.LiesOver I := hP.2
    exact ⟨⟨hP.1, Ideal.LiesOver.trans P I (rationalPrimeIdeal p)⟩, (P.over_def I).symm⟩

/-- The actual rational-prime denominator is a product of the relative
Gaussian denominators with the substitution dictated by the residue degree. -/
theorem rational_euler_denominator_via_gaussian (p : ℕ) [Fact p.Prime] :
    (∏ P : PrimeAbove K p, (1 - (PowerSeries.X : PowerSeries ℂ)^(P.val.inertiaDeg ℤ))) =
      ∏ I ∈ gaussianPrimesAbove p,
        (quarticEulerDenominator I).eval₂ (Int.castRingHom (PowerSeries ℂ))
          ((PowerSeries.X : PowerSeries ℂ)^(I.inertiaDeg ℤ)) := by
  calc
    _ = ∏ P ∈ primesAbove K p, (1 - (PowerSeries.X : PowerSeries ℂ)^(P.inertiaDeg ℤ)) :=
      Finset.prod_coe_sort (primesAbove K p) (fun P => 1 - (PowerSeries.X : PowerSeries ℂ)^(P.inertiaDeg ℤ))
    _ = ∏ I ∈ gaussianPrimesAbove p, ∏ P ∈ primesAbove K p with P.under GaussianInt = I,
          (1 - (PowerSeries.X : PowerSeries ℂ)^(P.inertiaDeg ℤ)) :=
      (Finset.prod_fiberwise_of_maps_to (fun _ hP => quartic_contracts_to_gaussian hP) _).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro I hI
      unfold quarticEulerDenominator
      change _ = Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries ℂ))
        (PowerSeries.X^(I.inertiaDeg ℤ)) _
      rw [map_prod, gaussian_fiber hI]
      apply Finset.prod_congr rfl
      intro P hP
      let : I.IsMaximal := gaussianPrimesAbove_isMaximal hI
      have hp := (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 K)
        (gaussianPrimesAbove_ne_bot hI)).mpr (Multiset.mem_toFinset.mp hP)
      let : P.LiesOver I := hp.2
      rw [Ideal.inertiaDeg_tower (R := ℤ) I P, pow_mul]
      simp only [map_sub, map_one, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

theorem fieldLocalEulerSeries_mul_gaussian_denominators (p : ℕ) [Fact p.Prime] :
    fieldLocalEulerSeries K p *
      (∏ I ∈ gaussianPrimesAbove p,
        (quarticEulerDenominator I).eval₂ (Int.castRingHom (PowerSeries ℂ))
          ((PowerSeries.X : PowerSeries ℂ)^(I.inertiaDeg ℤ))) = 1 := by
  rw [← rational_euler_denominator_via_gaussian]
  exact fieldLocalEulerSeries_mul_denominator K p

#print axioms rational_euler_denominator_via_gaussian
#print axioms fieldLocalEulerSeries_mul_gaussian_denominators

end QuarticModel
