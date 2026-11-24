import QuarticArchivedEuler

/-! Extract each prime-power coefficient of the quartic field as a
product of the ordinary, beta, and original signed Gaussian local series. -/

namespace QuarticModel

open FieldCoefficientTransfer PowerSeries
open scoped Classical

local notation "T" => (PowerSeries.X : PowerSeries ℂ)

noncomputable def weightedGeometricAtDegree (a : ℂ) (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.subst (T^d) (PowerSeries.mk fun n => a^n)

theorem coeff_weightedGeometricAtDegree (a : ℂ) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    coeff n (weightedGeometricAtDegree a d) = if d ∣ n then a^(n/d) else 0 := by
  rw [weightedGeometricAtDegree, coeff_subst_X_pow hd, coeff_mk]
  rfl

theorem weightedGeometricAtDegree_mul_denominator (a : ℂ) {d : ℕ} (hd : d ≠ 0) :
    weightedGeometricAtDegree a d * (1-C a*T^d) = 1 := by
  have h0 : (PowerSeries.mk fun n => a^n) * (1-C a*T) = 1 := by
    rw [mul_sub, mul_one, ← mul_assoc, PowerSeries.ext_iff]
    intro n
    cases n with
    | zero => simp
    | succ n => simp [coeff_mul_C, coeff_succ_mul_X, pow_succ]
  have ha : PowerSeries.HasSubst (T^d) := .X_pow hd
  have h := congrArg (PowerSeries.substAlgHom ha) h0
  have hC : PowerSeries.substAlgHom ha (C a) = C a := (PowerSeries.substAlgHom ha).commutes a
  rw [map_mul, map_sub, map_one, map_mul, hC, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom] at h
  exact h

noncomputable def signedLocalEulerSeries (p : ℕ) : PowerSeries ℂ :=
  ∏ I : ↥(gaussianPrimesAbove p), weightedGeometricAtDegree (archivedIdealCharacter I.val : ℂ) (I.val.inertiaDeg ℤ)

private theorem gaussianPrime_degree_pos {p : ℕ} (I : ↥(gaussianPrimesAbove p)) :
    0 < I.val.inertiaDeg ℤ := by
  let : I.val.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor _
    (Multiset.mem_toFinset.mp I.property))
  exact I.val.inertiaDeg_pos ℤ

theorem signedLocalEulerSeries_mul_denominator (p : ℕ) :
    signedLocalEulerSeries p *
      (∏ I : ↥(gaussianPrimesAbove p), (1-(archivedIdealCharacter I.val : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ))) = 1 := by
  rw [signedLocalEulerSeries, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro I _
  simpa only [map_intCast] using
    weightedGeometricAtDegree_mul_denominator (archivedIdealCharacter I.val : ℂ) (gaussianPrime_degree_pos I).ne'

theorem fieldLocalEulerSeries_eq_archived_series (p : ℕ) [Fact p.Prime] :
    fieldLocalEulerSeries K p = weightedGeometricAtDegree 1 1 *
      weightedGeometricAtDegree (ZMod.χ₄ (p : ZMod 4) : ℂ) 1 * signedLocalEulerSeries p := by
  let den := ∏ I : ↥(gaussianPrimesAbove p), (1-(archivedIdealCharacter I.val : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ))
  let D := (1-T)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T)*den
  let Z := weightedGeometricAtDegree 1 1
  let B := weightedGeometricAtDegree (ZMod.χ₄ (p : ZMod 4) : ℂ) 1
  let G := signedLocalEulerSeries p
  have hZ : Z*(1-T) = 1 := by
    simpa only [Z, pow_one, map_one, one_mul] using weightedGeometricAtDegree_mul_denominator (1 : ℂ) one_ne_zero
  have hB : B*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T) = 1 := by
    simpa only [B, pow_one, map_intCast] using
      weightedGeometricAtDegree_mul_denominator (ZMod.χ₄ (p : ZMod 4) : ℂ) one_ne_zero
  have hG : G*den = 1 := signedLocalEulerSeries_mul_denominator p
  have hQ : (Z*B*G)*D = 1 := by
    unfold D
    rw [show Z*B*G*((1-T)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T)*den) =
      (Z*(1-T))*(B*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T))*(G*den) by ring,
      hZ, hB, hG]
    simp
  have hField : fieldLocalEulerSeries K p * D = 1 := fieldLocalEulerSeries_mul_archived_denominators p
  calc
    fieldLocalEulerSeries K p = (fieldLocalEulerSeries K p * D)*(Z*B*G) := by
      rw [mul_assoc, mul_comm D, hQ, mul_one]
    _ = Z*B*G := by rw [hField, one_mul]

theorem idealCounts_primePower_eq_archived_series (p : ℕ) [Fact p.Prime] (n : ℕ) :
    idealCounts K (p^n) = coeff n (weightedGeometricAtDegree 1 1 *
      weightedGeometricAtDegree (ZMod.χ₄ (p : ZMod 4) : ℂ) 1 * signedLocalEulerSeries p) := by
  rw [idealCounts_primePower_eq_localEuler, fieldLocalEulerSeries_eq_archived_series]

#print axioms coeff_weightedGeometricAtDegree
#print axioms fieldLocalEulerSeries_eq_archived_series
#print axioms idealCounts_primePower_eq_archived_series

end QuarticModel
