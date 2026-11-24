import RelativeQuartic
import Mathlib.RingTheory.Localization.FractionRing

/-! Identify the Gaussian subfield of the quartic as the fraction field of
the embedded Gaussian integers, and use the two checked power bases. -/

namespace QuarticModel

open NumberField

theorem powerBasis_two_coordinates {F E : Type*} [CommRing F] [CommRing E]
    [Algebra F E] (pb : PowerBasis F E) (hdim : pb.dim = 2) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * pb.gen := by
  let e := (finCongr hdim).symm
  let c (i : Fin 2) := pb.basis.repr x (e i)
  have h : (∑ i : Fin 2, c i • pb.basis (e i)) = x :=
    (e.sum_comp (fun j => pb.basis.repr x j • pb.basis j)).trans (pb.basis.sum_repr x)
  refine ⟨c 0, c 1, ?_⟩
  rw [Fin.sum_univ_two, pb.basis_eq_pow, pb.basis_eq_pow] at h
  have he0 : (e 0).val = 0 := rfl
  have he1 : (e 1).val = 1 := rfl
  simpa only [he0, he1, pow_zero, pow_one, Algebra.smul_def, mul_one] using h.symm

private noncomputable def basePowerBasis : PowerBasis ℚ gaussianBase :=
  IntermediateField.adjoin.powerBasis gaussianI_integral

private theorem basePowerBasis_dim : basePowerBasis.dim = 2 :=
  basePowerBasis.finrank.symm.trans gaussianBase_finrank

noncomputable def baseI : gaussianBase := basePowerBasis.gen

private theorem baseI_mul_self : baseI * baseI = ((-1 : ℤ) : gaussianBase) := by
  apply Subtype.ext
  change gaussianI * gaussianI = ((-1 : ℤ) : K)
  simpa [pow_two] using gaussianI_sq

noncomputable def gaussianBaseMap : GaussianInt →+* gaussianBase :=
  Zsqrtd.lift ⟨baseI, baseI_mul_self⟩

theorem gaussianBaseMap_injective : Function.Injective gaussianBaseMap := by
  apply Zsqrtd.lift_injective
  intro n h
  nlinarith only [h, sq_nonneg n]

noncomputable instance : Algebra GaussianInt gaussianBase := gaussianBaseMap.toAlgebra

theorem gaussianBaseMap_coe (z : GaussianInt) :
    (algebraMap gaussianBase K) (gaussianBaseMap z) =
      (z.re : K) + (z.im : K) * gaussianI := by
  rw [gaussianBaseMap, Zsqrtd.lift_apply_apply, map_add, map_mul, map_intCast, map_intCast]
  rfl

theorem gaussian_maps_agree (z : GaussianInt) :
    algebraMap gaussianBase K (algebraMap GaussianInt gaussianBase z) =
      algebraMap (𝓞 K) K (gaussianOrderMap z) := by
  change algebraMap gaussianBase K (gaussianBaseMap z) = _
  rw [gaussianBaseMap_coe, gaussianOrderMap, Zsqrtd.lift_apply_apply, map_add,
    map_mul, map_intCast, map_intCast]
  rfl

private theorem base_exists_ratio (x : gaussianBase) :
    ∃ z d : GaussianInt, x = algebraMap GaussianInt gaussianBase z / algebraMap GaussianInt gaussianBase d := by
  obtain ⟨a, b, hx⟩ := powerBasis_two_coordinates basePowerBasis basePowerBasis_dim x
  refine ⟨⟨a.num * b.den, b.num * a.den⟩, ((a.den * b.den : ℕ) : GaussianInt), ?_⟩
  apply (algebraMap gaussianBase K).injective
  rw [hx, map_add, map_mul, map_div₀, map_natCast]
  change (a : K) + (b : K) * gaussianI =
    algebraMap gaussianBase K (gaussianBaseMap ⟨a.num * b.den, b.num * a.den⟩) /
      ((a.den * b.den : ℕ) : K)
  rw [gaussianBaseMap_coe, Rat.cast_def, Rat.cast_def]
  push_cast
  field_simp

instance gaussianBase_fraction : IsFractionRing GaussianInt gaussianBase := by
  let : FaithfulSMul GaussianInt gaussianBase :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr gaussianBaseMap_injective
  exact IsFractionRing.of_field GaussianInt gaussianBase base_exists_ratio

theorem relative_exists_coordinates (x : K) :
    ∃ a b : gaussianBase, x =
      algebraMap gaussianBase K a + algebraMap gaussianBase K b * (thetaHalf : K) := by
  simpa only [relativeFieldBasis_gen] using
    powerBasis_two_coordinates relativeFieldBasis relativeFieldBasis_dim x

#print axioms gaussian_maps_agree
#print axioms base_exists_ratio
#print axioms gaussianBase_fraction
#print axioms relative_exists_coordinates

end QuarticModel
