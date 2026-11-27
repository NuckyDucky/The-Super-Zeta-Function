import DedekindDiscriminant23NormForms
import DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions
import DedekindZetaZeroFree.Theta.Periods.CenteredLogarithmicIdealAverages

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding.fundamentalCone
open DedekindZetaZeroFree.AbelianQuotient.Theta
open MeasureTheory

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "I23" => (Ideal (𝓞 F23))⁰
local notation "v₀" => (w₀ : InfinitePlace F23)

theorem discriminant23_quadratic_place_count : Fintype.card (InfinitePlace F23) = 1 := by
  let : IsTotallyComplex F23 := discriminant23_quadratic_totallyComplex
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero F23, zero_add]
  have h := IsTotallyComplex.finrank F23
  rw [discriminant23QuadraticSubfield_finrank] at h
  omega

private theorem places_univ : (Finset.univ : Finset (InfinitePlace F23)) = {v₀} := by
  let : Subsingleton (InfinitePlace F23) :=
    Fintype.card_le_one_iff_subsingleton.mp discriminant23_quadratic_place_count.le
  ext v
  simp [Subsingleton.elim v v₀]

private theorem mult_v₀ : InfinitePlace.mult v₀ = 2 := by
  have h := InfinitePlace.sum_mult_eq (K := F23)
  rw [places_univ, Finset.sum_singleton, discriminant23QuadraticSubfield_finrank] at h
  exact h

private theorem angular_index_empty :
    IsEmpty {v : InfinitePlace F23 // v ≠ v₀} := by
  let : Subsingleton (InfinitePlace F23) :=
    Fintype.card_le_one_iff_subsingleton.mp discriminant23_quadratic_place_count.le
  exact ⟨fun v ↦ v.property (Subsingleton.elim _ _)⟩

private theorem norm_int_nonneg (x : 𝓞 F23) : 0 ≤ Algebra.norm ℤ x := by
  obtain ⟨m, n, hx⟩ : ∃ m n : ℤ, x = (m : 𝓞 F23) + n * discriminant23Omega :=
    ⟨_, _, discriminant23Integers_coordinates x⟩
  rw [hx, discriminant23_principal_norm_form]
  nlinarith only [discriminant23_principal_form_growth m n, sq_nonneg m, sq_nonneg n]

private theorem place_sq_eq_norm (x : 𝓞 F23) :
    v₀ (x : F23) ^ 2 = (Algebra.norm ℤ x : ℝ) := by
  have h := InfinitePlace.prod_eq_abs_norm (x : F23)
  rw [places_univ, Finset.prod_singleton, mult_v₀, ← Algebra.coe_norm_int] at h
  push_cast at h
  exact h.trans (abs_of_nonneg (by exact_mod_cast norm_int_nonneg x))

private theorem covolume_integral_ideal (J : I23) :
    mixedThetaCovolume F23 (FractionalIdeal.mk0 F23 J) =
      (J.val.absNorm : ℝ) * Real.sqrt 23 := by
  rw [mixedThetaCovolume, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
    discriminant23_quadratic_discriminant]
  norm_num

private theorem radial_shape_sq (I : (FractionalIdeal (𝓞 F23)⁰ F23)ˣ)
    (t : ℝ) (ht : 0 < t) (v : InfinitePlace F23) :
    (mixedThetaShape F23 I t (0 : Angular F23) v) ^ 2 = t / mixedThetaCovolume F23 I := by
  let : IsEmpty {v : InfinitePlace F23 // v ≠ v₀} := angular_index_empty
  have hc := DedekindZetaZeroFree.Hecke.Theta.mixedThetaCovolume_pos F23 I
  rw [mixedThetaShape, expMapBasis_apply']
  simp [angularLift, radialLift, discriminant23QuadraticSubfield_finrank]
  rw [← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * ((Real.log t - Real.log (mixedThetaCovolume F23 I)) / 2) =
      Real.log t - Real.log (mixedThetaCovolume F23 I) by ring,
    Real.exp_sub, Real.exp_log ht, Real.exp_log hc]

private def integralIdealEquiv (J : I23) :
    J.val ≃ ↥((FractionalIdeal.mk0 F23 J :
      FractionalIdeal (𝓞 F23)⁰ F23) : Submodule (𝓞 F23) F23) := by
  let f (x : J.val) : ↥((FractionalIdeal.mk0 F23 J :
      FractionalIdeal (𝓞 F23)⁰ F23) : Submodule (𝓞 F23) F23) :=
    ⟨algebraMap (𝓞 F23) F23 x.val, by
      change algebraMap (𝓞 F23) F23 x.val ∈ (FractionalIdeal.mk0 F23 J :
        FractionalIdeal (𝓞 F23)⁰ F23)
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.mem_coeIdeal_of_mem _ x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply FaithfulSMul.algebraMap_injective (𝓞 F23) F23
    exact congrArg (fun z ↦ (z.val : F23)) h
  · intro x
    have hx : x.val ∈ (J.val : FractionalIdeal (𝓞 F23)⁰ F23) := x.property
    obtain ⟨y, hy, hxy⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

/-- At discriminant `-23` the integral over unit directions is
zero-dimensional. The theta value is a sum of normalized norms over the
actual ideal, with the same scale as the Dottie disk. -/
theorem discriminant23_mixedAngularAverage_hasSum_idealNorm
    (J : I23) (t : ℝ) (ht : 0 < t) :
    HasSum (fun x : J.val ↦ Complex.exp (-(discriminant23ThetaScale : ℂ) * t *
        (Algebra.norm ℤ x.val : ℂ) / (J.val.absNorm : ℂ)))
      (mixedAngularAverage F23 (FractionalIdeal.mk0 F23 J) t) := by
  classical
  let : IsEmpty {v : InfinitePlace F23 // v ≠ v₀} := angular_index_empty
  let I := FractionalIdeal.mk0 F23 J
  have hConst : mixedRadialTheta F23 I t = fun _ ↦ mixedRadialTheta F23 I t 0 := by
    funext u
    congr 1
    funext v
    exact isEmptyElim v
  have hVol : volume (angularCube F23) = 1 := by
    simp [angularCube, Real.volume_pi_Ico]
  have hAvg : mixedAngularAverage F23 I t = mixedRadialTheta F23 I t 0 := by
    rw [mixedAngularAverage, hConst, setIntegral_const]
    simp [hVol, Measure.real]
  let q := mixedThetaShape F23 I t (0 : Angular F23)
  let hq' : ∀ v, q v ≠ 0 := fun v ↦ ne_of_gt (expMapBasis_pos _ v)
  let e := (integralIdealEquiv J).trans (fractionalIdealElementShapeEquiv F23 I q hq')
  have h := (summable_latticeGaussian (shapeIdealLattice F23 I q hq') Real.pi_pos).hasSum
  change HasSum _ (mixedAngularAverage F23 I t)
  rw [hAvg, mixedRadialTheta, fractionalShapeIdealTheta, latticeTheta]
  refine (e.hasSum_iff.mpr h).congr_fun ?_
  intro x
  symm
  change latticeGaussian Real.pi
    ((fractionalIdealElementShapeEquiv F23 I q hq' (integralIdealEquiv J x)) :
      NumberField.mixedEmbedding.euclidean.mixedSpace F23) = _
  rw [fractionalIdealElementShapeEquiv_coe, ← mixedGaussian_eq_latticeGaussian]
  change mixedGaussian F23 (x.val : F23) q = _
  unfold mixedGaussian
  rw [places_univ, Finset.sum_singleton, mult_v₀]
  have hq : (q v₀) ^ 2 = t / mixedThetaCovolume F23 (FractionalIdeal.mk0 F23 J) :=
    radial_shape_sq _ t ht v₀
  rw [hq, place_sq_eq_norm, covolume_integral_ideal]
  apply congrArg Complex.exp
  unfold discriminant23ThetaScale
  push_cast
  have hn : (J.val.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors J
  have hs : (Real.sqrt (23 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hn, hs]

#check @discriminant23_mixedAngularAverage_hasSum_idealNorm
#print axioms discriminant23_quadratic_place_count
#print axioms discriminant23_mixedAngularAverage_hasSum_idealNorm

theorem discriminant23_mixedAngularAverage_eq_idealNormSum
    (J : I23) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 (FractionalIdeal.mk0 F23 J) t =
      ∑' x : J.val, Complex.exp (-(discriminant23ThetaScale : ℂ) * t *
        (Algebra.norm ℤ x.val : ℂ) / (J.val.absNorm : ℂ)) :=
  (discriminant23_mixedAngularAverage_hasSum_idealNorm J t ht).tsum_eq.symm

#check @discriminant23_mixedAngularAverage_eq_idealNormSum
#print axioms discriminant23_mixedAngularAverage_eq_idealNormSum

end
end FieldTarget
