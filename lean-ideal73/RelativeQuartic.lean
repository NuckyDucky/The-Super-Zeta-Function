import QuarticAt73
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Coprime.Lemmas

/-! The integral relative quadratic presentation of the same quartic field
used by the repository's prime-73 computation. -/

namespace QuarticModel

open NumberField Polynomial

private theorem iIntegral_mul_self :
    QuarticAt73.iIntegral * QuarticAt73.iIntegral = ((-1 : ℤ) : 𝓞 K) := by
  apply Subtype.ext
  change gaussianI * gaussianI = ((-1 : ℤ) : K)
  simpa [pow_two] using gaussianI_sq

noncomputable def gaussianOrderMap : GaussianInt →+* 𝓞 K :=
  Zsqrtd.lift ⟨QuarticAt73.iIntegral, iIntegral_mul_self⟩

theorem gaussianOrderMap_injective : Function.Injective gaussianOrderMap := by
  apply Zsqrtd.lift_injective
  intro n h
  nlinarith only [h, sq_nonneg n]

private noncomputable def halfPolynomial : ℤ[X] :=
  X^4 - 2 * X^3 + 2522579 * X^2 - 2522578 * X + 1656861424850

private theorem squareRoot_equation :
    (theta : K)^4 + 10090310 * (theta : K)^2 + 26509772707289 = 0 := by
  have h : ((theta : K)^2 + 5045155)^2 = -(1027708 : K)^2 := by
    rw [show (theta : K)^2 + 5045155 = 1027708 * gaussianI by rw [theta_sq]; ring,
      mul_pow, gaussianI_sq]
    ring
  linear_combination h

noncomputable def thetaHalf : 𝓞 K :=
  ⟨(1 + (theta : K)) / 2, halfPolynomial, by unfold halfPolynomial; monicity!, by
    change halfPolynomial.eval₂ (algebraMap ℤ K) ((1 + (theta : K)) / 2) = 0
    simp only [halfPolynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow,
      eval₂_X, eval₂_ofNat]
    linear_combination squareRoot_equation / 16⟩

theorem two_thetaHalf :
    (2 : 𝓞 K) * thetaHalf = 1 + theta := by
  apply Subtype.ext
  change algebraMap (𝓞 K) K (2 * thetaHalf) = algebraMap (𝓞 K) K (1 + theta)
  rw [map_mul, map_add, map_one, map_ofNat]
  change 2 * ((1 + (theta : K)) / 2) = _
  ring

noncomputable def relativePolynomial : GaussianInt[X] :=
  X^2 - X + C (⟨1261289, -256927⟩ : GaussianInt)

theorem relativePolynomial_monic : relativePolynomial.Monic := by
  unfold relativePolynomial
  monicity!

theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 2 := by
  unfold relativePolynomial
  compute_degree!

theorem relative_equation :
    thetaHalf^2 - thetaHalf + gaussianOrderMap ⟨1261289, -256927⟩ = 0 := by
  apply Subtype.ext
  change algebraMap (𝓞 K) K (thetaHalf^2 - thetaHalf +
    gaussianOrderMap ⟨1261289, -256927⟩) = algebraMap (𝓞 K) K 0
  rw [map_add, map_sub, map_pow, map_zero, gaussianOrderMap, Zsqrtd.lift_apply_apply,
    map_add, map_mul, map_intCast, map_intCast]
  change ((1 + (theta : K)) / 2)^2 - (1 + (theta : K)) / 2 +
    (((1261289 : ℤ) : K) + ((-256927 : ℤ) : K) * gaussianI) = 0
  push_cast
  linear_combination theta_sq / 4

theorem relativePolynomial_eval :
    (relativePolynomial.map gaussianOrderMap).eval thetaHalf = 0 := by
  simpa only [relativePolynomial, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    map_X, map_C, eval_add, eval_sub, eval_pow, eval_X, eval_C] using relative_equation

def gaussianDiscriminant : GaussianInt := ⟨-5045155, 1027708⟩

theorem relative_discriminant :
    (1 : GaussianInt) - 4 * ⟨1261289, -256927⟩ = gaussianDiscriminant := by decide

theorem gaussianDiscriminant_norm :
    gaussianDiscriminant.norm.natAbs = 41 * 457 * 1414835497 := by decide

set_option maxRecDepth 60000 in
theorem gaussianDiscriminant_squarefree : Squarefree gaussianDiscriminant := by
  have hn : Squarefree gaussianDiscriminant.norm.natAbs := by
    rw [gaussianDiscriminant_norm, Nat.squarefree_mul (by decide : (41*457).Coprime 1414835497),
      Nat.squarefree_mul (by decide : (41 : ℕ).Coprime 457)]
    exact ⟨⟨(by norm_num : Nat.Prime 41).squarefree, (by norm_num : Nat.Prime 457).squarefree⟩,
      (by norm_num : Nat.Prime 1414835497).squarefree⟩
  intro z h
  apply Zsqrtd.norm_eq_one_iff.mp
  apply Nat.isUnit_iff.mp
  apply hn
  obtain ⟨w, hw⟩ := h
  exact ⟨w.norm.natAbs, by rw [hw, Zsqrtd.norm_mul, Zsqrtd.norm_mul, Int.natAbs_mul, Int.natAbs_mul]⟩

/-- A reduced Gaussian denominator cannot divide the discriminant relation
    of an integral element unless it is a unit. -/
theorem unit_denominator_of_discriminant {u v : GaussianInt} (huv : IsCoprime u v)
    (h : v^2 ∣ u^2 * gaussianDiscriminant) : IsUnit v := by
  have hcop : IsCoprime (v^2) (u^2) := (huv.symm.pow_left).pow_right
  exact gaussianDiscriminant_squarefree v (by simpa only [pow_two] using hcop.dvd_of_dvd_mul_left h)

/-- The Gaussian intermediate field inside the exact quartic model. -/
noncomputable def gaussianBase : IntermediateField ℚ K :=
  IntermediateField.adjoin ℚ {gaussianI}

theorem gaussianI_integral : IsIntegral ℚ gaussianI := by
  refine ⟨X^2 + 1, by monicity!, ?_⟩
  change (X^2 + 1).eval₂ (algebraMap ℚ K) gaussianI = 0
  rw [eval₂_add, eval₂_X_pow, eval₂_one, gaussianI_sq, neg_add_cancel]

theorem gaussianBase_finrank : Module.finrank ℚ gaussianBase = 2 := by
  have hle : (minpoly ℚ gaussianI).natDegree ≤ 2 := by
    have hd : minpoly ℚ gaussianI ∣ (X^2 + 1 : ℚ[X]) := minpoly.dvd ℚ gaussianI (by
      change (X^2 + 1).eval₂ (algebraMap ℚ K) gaussianI = 0
      rw [eval₂_add, eval₂_X_pow, eval₂_one, gaussianI_sq, neg_add_cancel])
    have hp : (X^2 + 1 : ℚ[X]).Monic := by monicity!
    have hdegree : (X^2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    exact hdegree ▸ natDegree_le_of_dvd hd hp.ne_zero
  have hne : Module.finrank ℚ gaussianBase ≠ 1 := by
    intro h
    have hi : gaussianI ∈ (⊥ : IntermediateField ℚ K) :=
      IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hi
    have h : (algebraMap ℚ K) (q^2 + 1) = 0 := by
      rw [map_add, map_pow, hq, gaussianI_sq, map_one, neg_add_cancel]
    have hf : q^2 + 1 = 0 := (algebraMap ℚ K).injective (h.trans (map_zero _).symm)
    nlinarith only [hf, sq_nonneg q]
  have hfin : Module.finrank ℚ gaussianBase = (minpoly ℚ gaussianI).natDegree :=
    IntermediateField.adjoin.finrank gaussianI_integral
  have hpos := minpoly.natDegree_pos gaussianI_integral
  omega

theorem relative_finrank : Module.finrank gaussianBase K = 2 := by
  have h := Module.finrank_mul_finrank ℚ gaussianBase K
  rw [gaussianBase_finrank, degree_four] at h
  omega

theorem thetaHalf_generates :
    IntermediateField.adjoin gaussianBase {(thetaHalf : K)} = ⊤ := by
  apply IntermediateField.adjoin_eq_top_of_adjoin_eq_top (F := ℚ)
  let S := IntermediateField.adjoin ℚ {(thetaHalf : K)}
  have hh : (thetaHalf : K) ∈ S :=
    IntermediateField.subset_adjoin ℚ {(thetaHalf : K)} (Set.mem_singleton _)
  have hlinear : (theta : K) = 2 * (thetaHalf : K) - 1 := by
    change (theta : K) = 2 * ((1 + (theta : K)) / 2) - 1
    ring
  have ht : (theta : K) ∈ S := by
    rw [hlinear]
    exact S.sub_mem (S.mul_mem (by exact_mod_cast S.algebraMap_mem (2 : ℚ)) hh) S.one_mem
  have hgen : Algebra.adjoin ℚ {(theta : K)} = ⊤ := theta_generates
  have htop : (⊤ : Subalgebra ℚ K) ≤ S.toSubalgebra := by
    rw [← hgen]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
  exact top_unique htop

/-- The basis (1,h) of the exact quartic over its Gaussian intermediate field. -/
noncomputable def relativeFieldBasis : PowerBasis gaussianBase K :=
  (IntermediateField.adjoin.powerBasis (IsIntegral.of_finite gaussianBase (thetaHalf : K))).map
    ((IntermediateField.equivOfEq thetaHalf_generates).trans IntermediateField.topEquiv)

theorem relativeFieldBasis_gen : relativeFieldBasis.gen = (thetaHalf : K) := rfl

theorem relativeFieldBasis_dim : relativeFieldBasis.dim = 2 :=
  relativeFieldBasis.finrank.symm.trans relative_finrank

#print axioms gaussianOrderMap_injective
#print axioms two_thetaHalf
#print axioms relativePolynomial_monic
#print axioms relativePolynomial_natDegree
#print axioms relativePolynomial_eval
#print axioms gaussianDiscriminant_squarefree
#print axioms unit_denominator_of_discriminant
#print axioms gaussianBase_finrank
#print axioms relative_finrank
#print axioms thetaHalf_generates
#print axioms relativeFieldBasis_gen
#print axioms relativeFieldBasis_dim

end QuarticModel
