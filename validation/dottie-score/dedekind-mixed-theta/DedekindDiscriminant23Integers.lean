import DedekindDiscriminant23Unramified
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Norm.Basic

namespace FieldTarget

open Polynomial NumberField
open scoped NumberField

local notation "L" => Discriminant23GaloisField
local notation "F" => (discriminant23QuadraticSubfield : Type)

noncomputable section

private def quadraticSqrt : F :=
  discriminant23QuadraticEquiv (AdjoinRoot.root discriminant23Quadratic)

private theorem quadraticSqrt_sq : quadraticSqrt ^ 2 = -23 := by
  have h : (AdjoinRoot.root discriminant23Quadratic) ^ 2 + 23 = 0 := by
    calc
      _ = AdjoinRoot.mk discriminant23Quadratic discriminant23Quadratic := by
        change _ = AdjoinRoot.mk discriminant23Quadratic ((X : ℚ[X]) ^ 2 + C 23)
        rw [map_add, map_pow, AdjoinRoot.mk_C, map_ofNat]
        rfl
      _ = _ := AdjoinRoot.mk_self
  have hs := eq_neg_of_add_eq_zero_left h
  unfold quadraticSqrt
  rw [← map_pow, hs, map_neg, map_ofNat]

private def omegaField : F := (1 + quadraticSqrt) / 2

private theorem omegaField_relation : omegaField ^ 2 - omegaField + 6 = 0 := by
  unfold omegaField
  linear_combination (1 / 4 : F) * quadraticSqrt_sq

private theorem omegaField_isIntegral : IsIntegral ℤ omegaField := by
  have hd : ((X : ℤ[X]) ^ 2 - X).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt (by simp), degree_X_pow]
    norm_num
  have hc : (C (6 : ℤ)).degree < ((X : ℤ[X]) ^ 2 - X).degree := by
    rw [hd, degree_C (by norm_num : (6 : ℤ) ≠ 0)]
    norm_num
  refine ⟨X ^ 2 - X + C 6, ((monic_X.pow _).sub_of_left (by simp)).add_of_left hc, ?_⟩
  simpa [aeval_def] using omegaField_relation

/-- The integral element `(1 + √(-23))/2` in the quadratic subfield. -/
def discriminant23Omega : 𝓞 F := ⟨omegaField, omegaField_isIntegral⟩

theorem discriminant23Omega_sq : discriminant23Omega ^ 2 = discriminant23Omega - 6 := by
  apply RingOfIntegers.coe_injective
  change omegaField ^ 2 = omegaField - 6
  linear_combination omegaField_relation

private theorem trace_quadraticSqrt : Algebra.trace ℚ F quadraticSqrt = 0 := by
  have hmonic : discriminant23Quadratic.Monic := monic_X_pow_add_C (23 : ℚ) (n := 2) (by decide)
  let pb := AdjoinRoot.powerBasis hmonic.ne_zero
  have h := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
  have hm : minpoly ℚ pb.gen = discriminant23Quadratic :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic
  have hc : discriminant23Quadratic.nextCoeff = 0 := by
    simp [Polynomial.nextCoeff, discriminant23Quadratic]
  have hneg : -(minpoly ℚ pb.gen).nextCoeff = 0 :=
    neg_eq_zero.mpr ((congrArg Polynomial.nextCoeff hm).trans hc)
  unfold quadraticSqrt
  rw [Algebra.trace_eq_of_algEquiv discriminant23QuadraticEquiv]
  exact h.trans hneg

private theorem trace_int_to_rat (x : 𝓞 F) :
    (Algebra.trace ℤ (𝓞 F) x : ℚ) = Algebra.trace ℚ F (x : F) :=
  (Algebra.trace_localization ℤ (nonZeroDivisors ℤ) x).symm

private theorem trace_intCast (m : ℤ) : Algebra.trace ℤ (𝓞 F) (m : 𝓞 F) = 2 * m := by
  apply Int.cast_injective (α := ℚ)
  rw [trace_int_to_rat]
  change Algebra.trace ℚ F (algebraMap ℚ F (m : ℚ)) = _
  rw [Algebra.trace_algebraMap, discriminant23QuadraticSubfield_finrank]
  simp [two_mul]

private theorem trace_omega : Algebra.trace ℤ (𝓞 F) discriminant23Omega = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [trace_int_to_rat]
  have h : Algebra.trace ℚ F 1 = 2 := by
    have h := congrArg (fun x : ℤ ↦ (x : ℚ)) (trace_intCast 1)
    rw [trace_int_to_rat] at h
    simpa using h
  change Algebra.trace ℚ F omegaField = 1
  have he : omegaField = (2 : ℚ)⁻¹ • ((1 : F) + quadraticSqrt) := by
    rw [omegaField, Algebra.smul_def, map_inv₀, map_ofNat, div_eq_mul_inv, mul_comm]
  rw [he, LinearMap.map_smul, map_add, h, trace_quadraticSqrt]
  norm_num

private theorem trace_omega_sq : Algebra.trace ℤ (𝓞 F) (discriminant23Omega ^ 2) = -11 := by
  have h6 : Algebra.trace ℤ (𝓞 F) (6 : 𝓞 F) = 12 := by
    simpa using trace_intCast (6 : ℤ)
  rw [discriminant23Omega_sq, map_sub, trace_omega]
  norm_num [h6]

private def omegaVectors : Fin 2 → 𝓞 F := ![1, discriminant23Omega]

private theorem omega_discr : Algebra.discr ℤ omegaVectors = -23 := by
  have h1 : Algebra.trace ℤ (𝓞 F) 1 = 2 := by
    simpa using trace_intCast (1 : ℤ)
  have htrace : Algebra.traceMatrix ℤ omegaVectors = !![(2 : ℤ), 1; 1, -11] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [omegaVectors, Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        h1, trace_omega, ← pow_two, trace_omega_sq]
  rw [Algebra.discr_def, htrace, Matrix.det_fin_two]
  norm_num

private def comparisonBasis : Module.Basis (Fin 2) ℤ (𝓞 F) := by
  classical
  refine (RingOfIntegers.basis F).reindex (Fintype.equivFinOfCardEq ?_)
  rw [← Module.finrank_eq_card_basis (NumberField.integralBasis F), discriminant23QuadraticSubfield_finrank]

private theorem omega_discr_eq :
    (comparisonBasis.toMatrix omegaVectors).det ^ 2 * NumberField.discr F = -23 := by
  have h := omega_discr
  rw [← comparisonBasis.toMatrix_map_vecMul omegaVectors,
    Algebra.discr_of_matrix_vecMul, NumberField.discr_eq_discr F comparisonBasis] at h
  exact h

private theorem omega_change_det_isUnit : IsUnit (comparisonBasis.toMatrix omegaVectors).det := by
  have hs : Squarefree (-23 : ℤ) :=
    (Int.prime_iff_natAbs_prime.mpr (by decide +kernel)).squarefree
  apply hs
  exact ⟨NumberField.discr F, by rw [← pow_two, omega_discr_eq]⟩

theorem discriminant23_quadratic_discriminant : NumberField.discr F = -23 := by
  have h := omega_discr_eq
  rcases Int.isUnit_iff.mp omega_change_det_isUnit with hdet | hdet <;>
    simpa [hdet] using h

/-- The two displayed integral vectors form a basis of the full ring of integers. -/
def discriminant23IntegersBasis : Module.Basis (Fin 2) ℤ (𝓞 F) := by
  let f := comparisonBasis.constr ℤ omegaVectors
  have hm : LinearMap.toMatrix comparisonBasis comparisonBasis f =
      comparisonBasis.toMatrix omegaVectors := by
    ext i j
    simp [f, LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply]
  have hu : IsUnit (LinearMap.toMatrix comparisonBasis comparisonBasis f).det := by
    rw [hm]
    exact omega_change_det_isUnit
  exact comparisonBasis.map (LinearEquiv.ofIsUnitDet hu)

private theorem discriminant23IntegersBasis_apply (i : Fin 2) :
    discriminant23IntegersBasis i = omegaVectors i := by
  unfold discriminant23IntegersBasis
  rw [Module.Basis.map_apply, LinearEquiv.ofIsUnitDet_apply, Module.Basis.constr_basis]

@[simp] theorem discriminant23IntegersBasis_zero : discriminant23IntegersBasis 0 = 1 :=
  discriminant23IntegersBasis_apply 0

@[simp] theorem discriminant23IntegersBasis_one :
    discriminant23IntegersBasis 1 = discriminant23Omega :=
  discriminant23IntegersBasis_apply 1

theorem discriminant23Integers_coordinates (x : 𝓞 F) :
    x = (discriminant23IntegersBasis.repr x 0 : 𝓞 F) +
      (discriminant23IntegersBasis.repr x 1 : 𝓞 F) * discriminant23Omega := by
  simpa [Fin.sum_univ_two, Algebra.smul_def] using (discriminant23IntegersBasis.sum_repr x).symm

theorem discriminant23Integers_repr (m n : ℤ) (i : Fin 2) :
    discriminant23IntegersBasis.repr ((m : 𝓞 F) + n * discriminant23Omega) i = ![m, n] i := by
  have h : (m : 𝓞 F) + n * discriminant23Omega =
      m • discriminant23IntegersBasis 0 + n • discriminant23IntegersBasis 1 := by
    simp [Algebra.smul_def]
  rw [h, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  fin_cases i <;> simp

theorem discriminant23_quadratic_norm (m n : ℤ) :
    Algebra.norm ℤ ((m : 𝓞 F) + n * discriminant23Omega) = m ^ 2 + m * n + 6 * n ^ 2 := by
  have hmul : ((m : 𝓞 F) + n * discriminant23Omega) * discriminant23Omega =
      ((-6 * n : ℤ) : 𝓞 F) + ((m + n : ℤ) : 𝓞 F) * discriminant23Omega := by
    push_cast
    linear_combination (n : 𝓞 F) * discriminant23Omega_sq
  have hm : Algebra.leftMulMatrix discriminant23IntegersBasis
      ((m : 𝓞 F) + n * discriminant23Omega) = !![m, -6 * n; n, m + n] := by
    have h0 (i : Fin 2) : Algebra.leftMulMatrix discriminant23IntegersBasis
        ((m : 𝓞 F) + n * discriminant23Omega) i 0 = ![m, n] i := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, discriminant23IntegersBasis_zero, mul_one,
        discriminant23Integers_repr]
    have h1 (i : Fin 2) : Algebra.leftMulMatrix discriminant23IntegersBasis
        ((m : 𝓞 F) + n * discriminant23Omega) i 1 = ![-6 * n, m + n] i := by
      rw [Algebra.leftMulMatrix_eq_repr_mul, discriminant23IntegersBasis_one, hmul,
        discriminant23Integers_repr]
    ext i j
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    exacts [h0 0, h1 0, h0 1, h1 1]
  rw [Algebra.norm_eq_matrix_det discriminant23IntegersBasis, hm, Matrix.det_fin_two]
  simp
  ring

theorem discriminant23_galois_discriminant_abs : (NumberField.discr L).natAbs = 23 ^ 3 := by
  rw [discriminant23_discriminant_tower, discriminant23_quadratic_discriminant]
  norm_num

theorem discriminant23_quadratic_totallyComplex : IsTotallyComplex F := by
  constructor
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hr
  let e := InfinitePlace.embedding_of_isReal hr
  have h := congrArg e quadraticSqrt_sq
  simp only [map_pow, map_neg, map_ofNat] at h
  nlinarith only [h, sq_nonneg (e quadraticSqrt)]

theorem discriminant23_galois_signature :
    InfinitePlace.nrRealPlaces L = 0 ∧ InfinitePlace.nrComplexPlaces L = 3 := by
  let : IsTotallyComplex F := discriminant23_quadratic_totallyComplex
  let : IsTotallyComplex L := isTotallyComplex_of_algebra F L
  have h := IsTotallyComplex.finrank L
  rw [discriminant23_galois_field_finrank] at h
  exact ⟨IsTotallyComplex.nrRealPlaces_eq_zero L, by omega⟩

/-- The completion factor for this field has three complex factors. Removing
the factor of two in each complex Gamma convention leaves a factor of eight. -/
theorem discriminant23_completion_factor (w : ℂ) :
    (((|NumberField.discr L| : ℤ) : ℂ) ^ (w / 2)) *
        Complex.Gammaℝ w ^ InfinitePlace.nrRealPlaces L *
        Complex.Gammaℂ w ^ InfinitePlace.nrComplexPlaces L =
      8 * (((23 : ℂ) ^ (w / 2)) * ((2 : ℂ) * Real.pi) ^ (-w) * Complex.Gamma w) ^ 3 := by
  obtain ⟨hreal, hcomplex⟩ := discriminant23_galois_signature
  have hD : (|NumberField.discr L| : ℤ) = (23 : ℤ) ^ 3 := by
    rw [← Int.natCast_natAbs, discriminant23_galois_discriminant_abs, Nat.cast_pow]
    norm_num
  have harg : (23 : ℂ).arg = 0 := by
    simp
  have hP : (((23 : ℂ) ^ (3 : ℕ)) ^ (w / 2)) = ((23 : ℂ) ^ (w / 2)) ^ (3 : ℕ) := by
    rw [← Complex.cpow_nat_mul' (n := 3)
      (by simpa [harg] using (neg_lt_zero.mpr Real.pi_pos))
      (by simpa [harg] using Real.pi_pos.le), Complex.cpow_nat_mul]
  rw [hreal, hcomplex, pow_zero, mul_one, hD, Int.cast_pow, Int.cast_ofNat, hP, Complex.Gammaℂ_def]
  ring

#check @discriminant23_quadratic_discriminant
#check @discriminant23_galois_discriminant_abs
#check @discriminant23_galois_signature
#check @discriminant23_quadratic_norm
#check @discriminant23_completion_factor
#print axioms discriminant23_quadratic_discriminant
#print axioms discriminant23IntegersBasis
#print axioms discriminant23Integers_coordinates
#print axioms discriminant23_quadratic_norm
#print axioms discriminant23_galois_discriminant_abs
#print axioms discriminant23_galois_signature
#print axioms discriminant23_completion_factor

end
end FieldTarget
