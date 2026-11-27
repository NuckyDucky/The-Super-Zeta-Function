import DedekindDiscriminant23ThetaForms
import DedekindIdealClassThetaPair
import DedekindZetaZeroFree.Theta.Periods.AngularAverageClassInvariance
import DedekindZetaZeroFree.Arithmetic.Ideals.TraceDualClassInvolution

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem
open DedekindZetaZeroFree.AbelianQuotient.Theta
open DedekindZetaZeroFree.Hecke

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "C23" => ClassGroup (𝓞 F23)
local notation "U23" => (FractionalIdeal (𝓞 F23)⁰ F23)ˣ

private theorem empty_angular_index : IsEmpty {v : InfinitePlace F23 // v ≠ (w₀ : InfinitePlace F23)} := by
  have hSub : Subsingleton (InfinitePlace F23) :=
    Fintype.card_le_one_iff_subsingleton.mp discriminant23_quadratic_place_count.le
  exact ⟨fun v ↦ v.property (@Subsingleton.elim _ hSub _ _)⟩

private theorem empty_matrix_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (he : IsEmpty ι) : A.det = 1 := by
  let : IsEmpty ι := he
  exact Matrix.det_isEmpty

private theorem regulator_eq_one : NumberField.Units.regulator F23 = 1 := by
  classical
  rw [NumberField.Units.regulator_eq_det', empty_matrix_det _ empty_angular_index, abs_one]

private theorem torsion_order_eq_two : NumberField.Units.torsionOrder F23 = 2 := by
  classical
  let : Fintype (NumberField.Units.torsion F23) := Fintype.ofFinite _
  have hNeg : (-1 : (𝓞 F23)ˣ) ∈ NumberField.Units.torsion F23 := by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by decide, by simp⟩
  let n : NumberField.Units.torsion F23 := ⟨-1, hNeg⟩
  have hne : (1 : NumberField.Units.torsion F23) ≠ n := by
    intro h
    have h' : (1 : 𝓞 F23) = -1 :=
      congrArg (fun u : NumberField.Units.torsion F23 ↦ (u.val : 𝓞 F23)) h
    have hInt : (1 : ℤ) = -1 := Int.cast_injective (α := 𝓞 F23) (by simpa using h')
    norm_num at hInt
  have hAll : (Finset.univ : Finset (NumberField.Units.torsion F23)) = {1, n} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases discriminant23_units_eq_one_or_neg_one u.val with h | h
    · exact Or.inl (Subtype.ext (Units.ext h))
    · exact Or.inr (Subtype.ext (Units.ext h))
  rw [NumberField.Units.torsionOrder, Nat.card_eq_fintype_card]
  change Finset.univ.card = 2
  rw [hAll]
  simp [hne]

theorem discriminant23_theta_alpha_eq_one : alpha F23 = 1 := by
  rw [alpha, ← card_eq_nrRealPlaces_add_nrComplexPlaces, discriminant23_quadratic_place_count,
    regulator_eq_one, torsion_order_eq_two]
  norm_num

/-- The centered theta kernel is the principal form at the identity class
and the other form at either nonprincipal class. -/
def discriminant23ClassKernel (C : C23) (t : ℝ) : ℂ := by
  classical
  exact if C = 1 then
    (classThetaStar discriminant23PrincipalForm (Real.exp (-discriminant23ThetaScale * t)) : ℂ)
  else
    (classThetaStar discriminant23OtherForm (Real.exp (-discriminant23ThetaScale * t)) : ℂ)

theorem discriminant23_classKernel_inv (C : C23) (t : ℝ) :
    discriminant23ClassKernel C⁻¹ t = discriminant23ClassKernel C t := by
  by_cases hc : C = 1
  · simp [hc]
  · have hi : C⁻¹ ≠ 1 := fun h ↦ hc (inv_eq_one.mp h)
    simp [discriminant23ClassKernel, hc, hi]

theorem discriminant23_centered_theta_eq_classKernel (I : U23) (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 I t - 1 = discriminant23ClassKernel (ClassGroup.mk F23 I) t := by
  rcases discriminant23_class_candidates (ClassGroup.mk F23 I) with h | h | h
  · have he : ClassGroup.mk F23 I = ClassGroup.mk F23 (FractionalIdeal.mk0 F23 1) := by
      simpa only [ClassGroup.mk_mk0, map_one] using h
    rw [mixedAngularAverage_class_invariant F23 I _ he t ht, h, discriminant23ClassKernel,
      ite_eq_left rfl]
    exact discriminant23_principal_theta_eq t ht
  · have he : ClassGroup.mk F23 I =
        ClassGroup.mk F23 (FractionalIdeal.mk0 F23 discriminant23NormTwoRepresentative) := by
      rw [ClassGroup.mk_mk0]
      exact h
    rw [mixedAngularAverage_class_invariant F23 I _ he t ht, h, discriminant23ClassKernel,
      ite_eq_right discriminant23_normTwoClass_ne_one]
    exact discriminant23_nonprincipal_theta_eq t ht
  · have he : ClassGroup.mk F23 I =
        ClassGroup.mk F23 (FractionalIdeal.mk0 F23 discriminant23NormTwoConjugateRepresentative) := by
      rwa [ClassGroup.mk_mk0, discriminant23_normTwoConjugate_class]
    have hn : discriminant23NormTwoClass⁻¹ ≠ 1 :=
      fun hi ↦ discriminant23_normTwoClass_ne_one (inv_eq_one.mp hi)
    rw [mixedAngularAverage_class_invariant F23 I _ he t ht, h, discriminant23ClassKernel,
      ite_eq_right hn]
    exact discriminant23_conjugate_theta_eq t ht

/-- At the self-dual input, Poisson summation preserves the principal
theta value. The strict gap there pins the trace-dual class to the identity. -/
theorem discriminant23_principalTraceDualClass_eq_one : principalTraceDualClass F23 = 1 := by
  have h := mixedAngularAverage_poisson F23 (1 : U23) 1 one_pos
  have he : mixedAngularAverage F23 (1 : U23) 1 =
      mixedAngularAverage F23 (traceDualIdealUnit F23 1) 1 := by
    simpa only [div_one, Complex.ofReal_one, one_mul,
      mixedNegAngularAverage_eq_mixedAngularAverage F23 _ 1 one_pos] using h
  have hsub := congrArg (fun a : ℂ ↦ a - 1) he
  change mixedAngularAverage F23 (1 : U23) 1 - 1 =
    mixedAngularAverage F23 (traceDualIdealUnit F23 1) 1 - 1 at hsub
  rw [discriminant23_centered_theta_eq_classKernel _ _ one_pos,
    discriminant23_centered_theta_eq_classKernel _ _ one_pos, map_one] at hsub
  change discriminant23ClassKernel 1 1 =
    discriminant23ClassKernel (principalTraceDualClass F23) 1 at hsub
  by_contra hn
  have hreal := congrArg Complex.re hsub
  simp [discriminant23ClassKernel, hn] at hreal
  have hq := Real.exp_pos (-discriminant23ThetaScale)
  have hb := discriminant23_classThetaStar_bounds hq.le discriminant23_thetaExp_interval.2
  linarith only [hreal, hq, hb.1, hb.2.2.2]

theorem discriminant23_classPair_primal (C : C23) (t : ℝ) (ht : 0 < t) :
    (idealClassThetaPair F23 C).f t - 1 = discriminant23ClassKernel C t := by
  change (alpha F23 : ℂ) * mixedAngularAverage F23
    (FractionalIdeal.mk0 F23 (inverseClassIdealRepresentative F23 C)) t - 1 = _
  rw [discriminant23_theta_alpha_eq_one, Complex.ofReal_one, one_mul,
    discriminant23_centered_theta_eq_classKernel _ _ ht, ClassGroup.mk_mk0,
    mk0_inverseClassIdealRepresentative]
  exact discriminant23_classKernel_inv C t

theorem discriminant23_classPair_dual (C : C23) (t : ℝ) (ht : 0 < t) :
    (idealClassThetaPair F23 C).g t - 1 = discriminant23ClassKernel C t := by
  change (alpha F23 : ℂ) * mixedNegAngularAverage F23
    (traceDualIdealUnit F23 (FractionalIdeal.mk0 F23 (inverseClassIdealRepresentative F23 C))) t -
      1 = _
  rw [discriminant23_theta_alpha_eq_one, Complex.ofReal_one, one_mul,
    mixedNegAngularAverage_eq_mixedAngularAverage F23 _ t ht,
    discriminant23_centered_theta_eq_classKernel _ _ ht, mk_traceDualIdealUnit,
    discriminant23_principalTraceDualClass_eq_one, one_mul, ClassGroup.mk_mk0,
    mk0_inverseClassIdealRepresentative, inv_inv]

#check @discriminant23_principalTraceDualClass_eq_one
#check @discriminant23_classPair_dual
#print axioms discriminant23_theta_alpha_eq_one
#print axioms discriminant23_centered_theta_eq_classKernel
#print axioms discriminant23_principalTraceDualClass_eq_one
#print axioms discriminant23_classPair_primal
#print axioms discriminant23_classPair_dual

end
end FieldTarget
