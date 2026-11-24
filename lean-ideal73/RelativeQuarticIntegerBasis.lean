import RelativeGaussianBase
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! The integral order in the quartic is generated over the Gaussian
integers by the checked element `thetaHalf`. -/

namespace QuarticModel

open NumberField Polynomial

private abbrev c : GaussianInt := ⟨1261289, -256927⟩

private noncomputable def polynomialOverBase : gaussianBase[X] :=
  relativePolynomial.map (algebraMap GaussianInt gaussianBase)

private theorem polynomialOverBase_aeval (z : K) :
    aeval z polynomialOverBase =
      z^2 - z + algebraMap gaussianBase K (algebraMap GaussianInt gaussianBase c) := by
  change polynomialOverBase.eval₂ (algebraMap gaussianBase K) z = _
  simp only [polynomialOverBase, relativePolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, map_X, map_C, eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]

private theorem thetaHalf_root : aeval (thetaHalf : K) polynomialOverBase = 0 := by
  rw [polynomialOverBase_aeval, gaussian_maps_agree]
  simpa only [map_add, map_sub, map_pow, map_zero] using
    congrArg (algebraMap (𝓞 K) K) relative_equation

private theorem minpoly_relative :
    minpoly gaussianBase (thetaHalf : K) = polynomialOverBase := by
  have hm := relativePolynomial_monic.map (algebraMap GaussianInt gaussianBase)
  have hdeg : polynomialOverBase.natDegree = 2 :=
    (relativePolynomial_monic.natDegree_map (algebraMap GaussianInt gaussianBase)).trans
      relativePolynomial_natDegree
  have hdeg' : (minpoly gaussianBase (thetaHalf : K)).natDegree = 2 := by
    rw [← relativeFieldBasis_gen, relativeFieldBasis.natDegree_minpoly, relativeFieldBasis_dim]
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsIntegral.of_finite _ _)) hm
    (minpoly.dvd _ _ thetaHalf_root)
  change polynomialOverBase.natDegree ≤ _
  rw [hdeg, hdeg']

private theorem second_root :
    aeval (1 - (thetaHalf : K)) (minpoly gaussianBase relativeFieldBasis.gen) = 0 := by
  rw [relativeFieldBasis_gen, minpoly_relative, polynomialOverBase_aeval]
  rw [show (1-(thetaHalf : K))^2 - (1-(thetaHalf : K)) =
    (thetaHalf : K)^2 - (thetaHalf : K) by ring]
  simpa only [polynomialOverBase_aeval] using thetaHalf_root

noncomputable def relativeConjugate : K →ₐ[gaussianBase] K :=
  relativeFieldBasis.lift (1 - (thetaHalf : K)) second_root

theorem relativeConjugate_thetaHalf : relativeConjugate (thetaHalf : K) = 1 - (thetaHalf : K) := by
  calc
    _ = relativeConjugate relativeFieldBasis.gen := congrArg _ relativeFieldBasis_gen.symm
    _ = _ := PowerBasis.lift_gen relativeFieldBasis _ second_root

private theorem square_thetaHalf :
    (2 * (thetaHalf : K) - 1)^2 =
      algebraMap gaussianBase K (algebraMap GaussianInt gaussianBase gaussianDiscriminant) := by
  rw [gaussian_maps_agree, gaussianDiscriminant, gaussianOrderMap, Zsqrtd.lift_apply_apply,
    map_add, map_mul, map_intCast, map_intCast]
  change (2 * ((1 + (theta : K)) / 2) - 1)^2 =
    (((-5045155 : ℤ) : K) + ((1027708 : ℤ) : K) * gaussianI)
  push_cast
  linear_combination theta_sq

theorem relative_discriminant_coordinates {x : K} {a b : gaussianBase}
    (hx : x = algebraMap gaussianBase K a + algebraMap gaussianBase K b * (thetaHalf : K)) :
    (x - relativeConjugate x)^2 =
      algebraMap gaussianBase K (b^2 * algebraMap GaussianInt gaussianBase gaussianDiscriminant) := by
  calc
    _ = (algebraMap gaussianBase K b)^2 * (2 * (thetaHalf : K) - 1)^2 := by
      rw [hx, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, relativeConjugate_thetaHalf]
      ring
    _ = _ := by rw [square_thetaHalf, map_mul, map_pow]

private theorem gaussian_of_integral (x : gaussianBase)
    (hx : IsIntegral ℤ (algebraMap gaussianBase K x)) :
    ∃ z : GaussianInt, algebraMap GaussianInt gaussianBase z = x := by
  have hx' := (isIntegral_algebraMap_iff (algebraMap gaussianBase K).injective).mp hx
  exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx'.tower_top (A := GaussianInt))

private theorem integral_coordinate_of_square (b : gaussianBase)
    (hb : IsIntegral ℤ (algebraMap gaussianBase K
      (b^2 * algebraMap GaussianInt gaussianBase gaussianDiscriminant))) :
    ∃ z : GaussianInt, algebraMap GaussianInt gaussianBase z = b := by
  obtain ⟨d, hd⟩ := gaussian_of_integral _ hb
  let u := IsFractionRing.num GaussianInt b
  let v : GaussianInt := IsFractionRing.den GaussianInt b
  have hv : b * algebraMap GaussianInt gaussianBase v = algebraMap GaussianInt gaussianBase u :=
    (IsFractionRing.num_mul_den_eq_num_iff_eq (A := GaussianInt)).mpr rfl
  have hprod : v^2*d = u^2*gaussianDiscriminant := by
    apply (IsFractionRing.injective GaussianInt gaussianBase)
    simp only [map_mul, map_pow, hd, ← hv]
    ring
  have hcop : IsCoprime u v := (IsFractionRing.num_den_reduced GaussianInt b).isCoprime
  exact IsFractionRing.isInteger_of_isUnit_den (A := GaussianInt)
    (unit_denominator_of_discriminant hcop ⟨d, hprod.symm⟩)

/-- Every algebraic integer in the actual quartic belongs to the order with
    Gaussian basis `1, thetaHalf`. -/
theorem integral_coordinates (x : 𝓞 K) :
    ∃ a b : GaussianInt, x = gaussianOrderMap a + gaussianOrderMap b * thetaHalf := by
  obtain ⟨a, b, hx⟩ := relative_exists_coordinates (x : K)
  have hx_int : IsIntegral ℤ (x : K) := x.2
  have hh_int : IsIntegral ℤ (thetaHalf : K) := thetaHalf.2
  have hconj : IsIntegral ℤ (relativeConjugate (x : K)) :=
    hx_int.map (relativeConjugate.restrictScalars ℤ)
  have hdisc := (hx_int.sub hconj).pow 2
  rw [relative_discriminant_coordinates hx] at hdisc
  obtain ⟨v, hv⟩ := integral_coordinate_of_square b hdisc
  have hvK : IsIntegral ℤ (algebraMap gaussianBase K b) := by
    rw [← hv, gaussian_maps_agree]
    exact (gaussianOrderMap v).2
  have haK : IsIntegral ℤ (algebraMap gaussianBase K a) := by
    have he : algebraMap gaussianBase K a = (x : K) -
        algebraMap gaussianBase K b * (thetaHalf : K) := by rw [hx]; ring
    rw [he]
    exact hx_int.sub (hvK.mul hh_int)
  obtain ⟨u, hu⟩ := gaussian_of_integral a haK
  refine ⟨u, v, ?_⟩
  apply Subtype.ext
  change (x : K) = algebraMap (𝓞 K) K (gaussianOrderMap u + gaussianOrderMap v * thetaHalf)
  rw [map_add, map_mul, ← gaussian_maps_agree, ← gaussian_maps_agree, hu, hv]
  exact hx

noncomputable instance : Algebra GaussianInt (𝓞 K) := gaussianOrderMap.toAlgebra

theorem gaussian_adjoin_thetaHalf_eq_top : Algebra.adjoin GaussianInt {thetaHalf} = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨u, v, rfl⟩ := integral_coordinates x
  let S := Algebra.adjoin GaussianInt {thetaHalf}
  exact S.add_mem (S.algebraMap_mem u) (S.mul_mem (S.algebraMap_mem v)
    (Algebra.subset_adjoin (Set.mem_singleton thetaHalf)))

instance : Module.IsTorsionFree GaussianInt (𝓞 K) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr gaussianOrderMap_injective

noncomputable instance : Algebra GaussianInt K :=
  ((algebraMap gaussianBase K).comp (algebraMap GaussianInt gaussianBase)).toAlgebra

instance : IsScalarTower GaussianInt gaussianBase K := IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower GaussianInt (𝓞 K) K := IsScalarTower.of_algebraMap_eq gaussian_maps_agree

theorem thetaHalf_integral_gaussian : IsIntegral GaussianInt thetaHalf :=
  ⟨relativePolynomial, relativePolynomial_monic, by
    change relativePolynomial.eval₂ gaussianOrderMap thetaHalf = 0
    rw [← Polynomial.eval_map]
    exact relativePolynomial_eval⟩

theorem thetaHalf_minpoly_gaussian : minpoly GaussianInt thetaHalf = relativePolynomial := by
  apply Polynomial.map_injective (algebraMap GaussianInt gaussianBase)
    (IsFractionRing.injective GaussianInt gaussianBase)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions gaussianBase K thetaHalf_integral_gaussian]
  exact minpoly_relative

noncomputable def relativeIntegersBasis : PowerBasis GaussianInt (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop' thetaHalf_integral_gaussian gaussian_adjoin_thetaHalf_eq_top

theorem relativeIntegersBasis_gen : relativeIntegersBasis.gen = thetaHalf :=
  PowerBasis.ofAdjoinEqTop'_gen _ _

theorem relativeIntegersBasis_dim : relativeIntegersBasis.dim = 2 := by
  rw [relativeIntegersBasis, PowerBasis.ofAdjoinEqTop'_dim, thetaHalf_minpoly_gaussian,
    relativePolynomial_natDegree]

/-- Reduction of the full quartic order modulo a Gaussian ideal. -/
noncomputable def quarticResidueEquiv (I : Ideal GaussianInt) :
    (𝓞 K ⧸ I.map (algebraMap GaussianInt (𝓞 K))) ≃+*
      ((GaussianInt ⧸ I)[X] ⧸ Ideal.span {relativePolynomial.map (Ideal.Quotient.mk I)}) := by
  rw [← thetaHalf_minpoly_gaussian]
  apply KummerDedekind.quotMapEquivQuotQuotMap (x := thetaHalf) _ thetaHalf_integral_gaussian
  rw [conductor_eq_top_of_adjoin_eq_top gaussian_adjoin_thetaHalf_eq_top, Ideal.comap_top, top_sup_eq]

attribute [local instance] Ideal.Quotient.field

open scoped Classical in
open UniqueFactorizationMonoid in
/-- At each Gaussian prime the factors of the reduced quadratic give
    the actual prime ideal factors in the quartic order. -/
noncomputable def quarticPrimeFactorEquiv (I : Ideal GaussianInt) [hI : I.IsMaximal]
    (hI' : I ≠ ⊥) :
    {J : Ideal (𝓞 K) | J ∈ normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))} ≃
      {q : (GaussianInt ⧸ I)[X] |
        q ∈ normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))} := by
  rw [← thetaHalf_minpoly_gaussian]
  apply KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' _
    thetaHalf_integral_gaussian
  rw [conductor_eq_top_of_adjoin_eq_top gaussian_adjoin_thetaHalf_eq_top, Ideal.comap_top, top_sup_eq]

#print axioms relative_discriminant_coordinates
#print axioms integral_coordinates
#print axioms gaussian_adjoin_thetaHalf_eq_top
#print axioms relativeIntegersBasis_gen
#print axioms relativeIntegersBasis_dim
#print axioms quarticResidueEquiv
#print axioms quarticPrimeFactorEquiv

end QuarticModel
