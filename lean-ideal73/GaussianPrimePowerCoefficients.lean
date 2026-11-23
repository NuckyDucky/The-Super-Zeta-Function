import IdealPrimePowerExponents
import QuarticArchivedPrimePowers

/-! The original signed ideal sum is the coefficient of the Gaussian
Euler factor, by unique factorization with actual inertia degrees. -/

namespace QuarticModel

open PowerSeries
open scoped Classical

abbrev GaussianNormFiber (n : ℕ) := {I : Ideal GaussianInt // I.absNorm = n}

instance gaussianNormFiber_finite (n : ℕ) : Finite (GaussianNormFiber n) :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

noncomputable def signedIdealNormSum (n : ℕ) : ℂ :=
  ∑' I : GaussianNormFiber n, (archivedIdealCharacter I.val : ℂ)

private abbrev Above (p : ℕ) := IdealPrimePower.PrimeAbove GaussianInt p

private noncomputable def allowedWeights (p n : ℕ) : Finset (Above p →₀ ℕ) :=
  (Finset.univ.finsuppAntidiag n).filter fun e => ∀ I : Above p, I.val.inertiaDeg ℤ ∣ e I

private noncomputable def degreeEquivAllowedWeights (p n : ℕ) :
    {f : Above p → ℕ // IdealPrimePower.exponentDegree GaussianInt f = n} ≃ ↥(allowedWeights p n) where
  toFun f := by
    let e : Above p →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun I => I.val.inertiaDeg ℤ * f.val I)
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_finsuppAntidiag.mpr ⟨f.property, Finset.subset_univ _⟩,
      fun I => dvd_mul_right _ _⟩⟩
  invFun e := by
    have h := Finset.mem_filter.mp e.property
    refine ⟨fun I => e.val I / I.val.inertiaDeg ℤ, ?_⟩
    unfold IdealPrimePower.exponentDegree
    calc
      _ = ∑ I : Above p, e.val I := Finset.sum_congr rfl fun I _ => Nat.mul_div_cancel' (h.2 I)
      _ = n := (Finset.mem_finsuppAntidiag.mp h.1).1
  left_inv f := by
    apply Subtype.ext
    funext I
    change (I.val.inertiaDeg ℤ * f.val I) / I.val.inertiaDeg ℤ = f.val I
    exact Nat.mul_div_cancel_left (f.val I) (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt I)
  right_inv e := by
    apply Subtype.ext
    ext I
    change I.val.inertiaDeg ℤ * (e.val I / I.val.inertiaDeg ℤ) = e.val I
    exact Nat.mul_div_cancel' ((Finset.mem_filter.mp e.property).2 I)

private theorem coeff_signed_series_eligible (p n : ℕ) :
    coeff n (signedLocalEulerSeries p) = ∑ e : ↥(allowedWeights p n),
      ∏ I : Above p, (archivedIdealCharacter I.val : ℂ) ^ (e.val I / I.val.inertiaDeg ℤ) := by
  unfold signedLocalEulerSeries
  change coeff n (∏ I : Above p, weightedGeometricAtDegree
    (archivedIdealCharacter I.val : ℂ) (I.val.inertiaDeg ℤ)) = _
  rw [PowerSeries.coeff_prod]
  simp_rw [coeff_weightedGeometricAtDegree _ (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt _).ne']
  have hprod (e : Above p →₀ ℕ) :
      (∏ I : Above p, if I.val.inertiaDeg ℤ ∣ e I then
        (archivedIdealCharacter I.val : ℂ)^(e I/I.val.inertiaDeg ℤ) else 0) =
      if ∀ I : Above p, I.val.inertiaDeg ℤ ∣ e I then
        ∏ I : Above p, (archivedIdealCharacter I.val : ℂ)^(e I/I.val.inertiaDeg ℤ) else 0 := by
    split_ifs with h
    · simp only [h, if_true]
    · obtain ⟨I,hI⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ I) (if_neg hI)
  simp_rw [hprod]
  rw [← Finset.sum_filter]
  exact (Finset.sum_coe_sort (allowedWeights p n) (fun e =>
    ∏ I : Above p, (archivedIdealCharacter I.val : ℂ)^(e I/I.val.inertiaDeg ℤ))).symm

theorem signedIdealNormSum_primePower (p : ℕ) [Fact p.Prime] (n : ℕ) :
    signedIdealNormSum (p^n) = coeff n (signedLocalEulerSeries p) := by
  let : Fintype (GaussianNormFiber (p^n)) := Fintype.ofFinite _
  let e := (IdealPrimePower.primePowerIdealsEquivExponents GaussianInt p n).trans
    (degreeEquivAllowedWeights p n)
  rw [signedIdealNormSum, tsum_fintype, coeff_signed_series_eligible]
  symm
  refine Fintype.sum_equiv e.symm _ _ fun f => ?_
  change (∏ I : Above p, (archivedIdealCharacter I.val : ℂ)^(f.val I/I.val.inertiaDeg ℤ)) =
    (archivedIdealCharacter
      (IdealPrimePower.exponentProduct GaussianInt (fun I : Above p => f.val I/I.val.inertiaDeg ℤ)) : ℂ)
  simp only [IdealPrimePower.exponentProduct, map_prod, map_pow, Int.cast_prod, Int.cast_pow]

#print axioms signedIdealNormSum_primePower

end QuarticModel
