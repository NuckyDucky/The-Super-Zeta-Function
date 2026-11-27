import DedekindDiscriminant23ClassTheta
import DedekindDiscriminant23ClassNumber

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField
open DedekindZetaZeroFree.AbelianQuotient.Theta

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "I23" => (Ideal (𝓞 F23))⁰
local notation "ω23" => discriminant23Omega

private def omegaCoordinates (p : ℤ × ℤ) : 𝓞 F23 := (p.1 : 𝓞 F23) + p.2 * ω23

private theorem omegaCoordinates_injective : Function.Injective omegaCoordinates := by
  intro p q h
  apply Prod.ext
  · simpa only [omegaCoordinates, discriminant23Integers_repr, Matrix.cons_val_zero] using
      congrArg (fun x ↦ discriminant23IntegersBasis.repr x 0) h
  · simpa only [omegaCoordinates, discriminant23Integers_repr, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      congrArg (fun x ↦ discriminant23IntegersBasis.repr x 1) h

private def liftCoordinates (J : I23) (f : ℤ × ℤ → ℤ × ℤ) (hf : Function.Injective f)
    (hJ : ∀ x : 𝓞 F23, x ∈ J.val ↔ ∃ p, omegaCoordinates (f p) = x) :
    ℤ × ℤ ≃ J.val :=
  Equiv.ofBijective
    (fun p ↦ ⟨omegaCoordinates (f p), (hJ _).2 ⟨p, rfl⟩⟩)
    ⟨fun _ _ h ↦ hf (omegaCoordinates_injective (congrArg Subtype.val h)), by
      intro x
      obtain ⟨p, hp⟩ := (hJ x.val).1 x.property
      exact ⟨p, Subtype.ext hp⟩⟩

private def principalCoordinates : ℤ × ℤ ≃ (1 : I23).val :=
  liftCoordinates 1 id Function.injective_id (by
    intro x
    constructor
    · intro _
      exact ⟨(_, _), (discriminant23Integers_coordinates x).symm⟩
    · intro _
      change x ∈ (1 : Ideal (𝓞 F23))
      simp [Ideal.one_eq_top])

private def normTwoCoordinates : ℤ × ℤ ≃ discriminant23NormTwoRepresentative.val :=
  liftCoordinates discriminant23NormTwoRepresentative (fun p ↦ (2 * p.1, p.2))
    (by
      intro p q h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp at h₁ h₂
      exact Prod.ext (by omega) h₂)
    (by
      intro x
      change x ∈ discriminant23NormTwoIdeal ↔ _
      rw [discriminant23NormTwoIdeal_coordinates]
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨(a, b), h.symm⟩
      · rintro ⟨⟨a, b⟩, h⟩
        exact ⟨a, b, h.symm⟩)

private theorem conjugate_mem (a b : ℤ) :
    omegaCoordinates (a, b) ∈ discriminant23NormTwoConjugateIdeal ↔ (2 : ℤ) ∣ a + b := by
  change discriminant23ResidueHom (1 : ZMod 2) (by decide +kernel)
    ((a : 𝓞 F23) + b * ω23) = 0 ↔ _
  rw [discriminant23ResidueHom_apply, mul_one, ← Int.cast_add,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

private def normTwoConjugateCoordinates : ℤ × ℤ ≃ discriminant23NormTwoConjugateRepresentative.val :=
  liftCoordinates discriminant23NormTwoConjugateRepresentative (fun p ↦ (2 * p.1 + p.2, -p.2))
    (by
      intro p q h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp at h₁ h₂
      exact Prod.ext (by omega) (by omega))
    (by
      intro x
      change x ∈ discriminant23NormTwoConjugateIdeal ↔ _
      obtain ⟨a, b, hx⟩ : ∃ a b : ℤ, x = omegaCoordinates (a, b) :=
        ⟨_, _, discriminant23Integers_coordinates x⟩
      rw [hx, conjugate_mem]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨(m, -b), congrArg omegaCoordinates ?_⟩
        exact Prod.ext (by dsimp; omega) (by simp)
      · rintro ⟨⟨m, n⟩, h⟩
        have hh := omegaCoordinates_injective h
        have h₁ := congrArg Prod.fst hh
        have h₂ := congrArg Prod.snd hh
        dsimp at h₁ h₂
        exact ⟨m, by omega⟩)

private theorem form_nonneg (Q : ℤ → ℤ → ℤ) (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n)
    (m n : ℤ) : 0 ≤ Q m n := by
  nlinarith only [hQ m n, sq_nonneg m, sq_nonneg n]

private theorem centered_average_eq_form (J : I23) (e : ℤ × ℤ ≃ J.val)
    (Q : ℤ → ℤ → ℤ) (hQ : ∀ m n, 0 ≤ Q m n) (h0 : Q 0 0 = 0)
    (hNorm : ∀ p : ℤ × ℤ, Algebra.norm ℤ (e p).val = (J.val.absNorm : ℤ) * Q p.1 p.2)
    (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 (FractionalIdeal.mk0 F23 J) t - 1 =
      (classThetaStar Q (Real.exp (-discriminant23ThetaScale * t)) : ℂ) := by
  classical
  let q := Real.exp (-discriminant23ThetaScale * t)
  let g (p : ℤ × ℤ) : ℂ := (q ^ (Q p.1 p.2).toNat : ℝ)
  have hTerms (p : ℤ × ℤ) :
      Complex.exp (-(discriminant23ThetaScale : ℂ) * t *
        (Algebra.norm ℤ (e p).val : ℂ) / (J.val.absNorm : ℂ)) = g p := by
    rw [hNorm]
    dsimp [g, q]
    rw [← Real.exp_nat_mul, Complex.ofReal_exp]
    apply congrArg Complex.exp
    have hc : (((Q p.1 p.2).toNat : ℕ) : ℂ) = (Q p.1 p.2 : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg (hQ p.1 p.2)
    have hn : (J.val.absNorm : ℂ) ≠ 0 := by exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors J
    push_cast
    rw [hc]
    field_simp [hn]
  have h := ((e.hasSum_iff.mpr
    (discriminant23_mixedAngularAverage_hasSum_idealNorm J t ht)).congr_fun
      (fun p ↦ (hTerms p).symm))
  have horigin : g (0, 0) = 1 := by simp [g, h0]
  have hs := h.summable.tsum_eq_add_tsum_ite (0, 0)
  rw [h.tsum_eq, horigin] at hs
  rw [hs, add_sub_cancel_left, classThetaStar, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  by_cases hp : p = (0, 0) <;> simp [g, q, hp]

/-- The principal-class theta sum on the integer lattice, with its constant
term removed. -/
theorem discriminant23_principal_theta_eq (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 (FractionalIdeal.mk0 F23 (1 : I23)) t - 1 =
      (classThetaStar discriminant23PrincipalForm (Real.exp (-discriminant23ThetaScale * t)) : ℂ) := by
  apply centered_average_eq_form 1 principalCoordinates discriminant23PrincipalForm
    (form_nonneg _ discriminant23_principal_form_growth)
    (by norm_num [discriminant23PrincipalForm]) _ t ht
  intro p
  change Algebra.norm ℤ (omegaCoordinates p) = _
  rw [omegaCoordinates, discriminant23_principal_norm_form]
  simp [Ideal.one_eq_top]

/-- The theta sum of the norm-two ideal, with the same normalization. -/
theorem discriminant23_nonprincipal_theta_eq (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 (FractionalIdeal.mk0 F23 discriminant23NormTwoRepresentative) t - 1 =
      (classThetaStar discriminant23OtherForm (Real.exp (-discriminant23ThetaScale * t)) : ℂ) := by
  apply centered_average_eq_form _ normTwoCoordinates discriminant23OtherForm
    (form_nonneg _ discriminant23_other_form_growth)
    (by norm_num [discriminant23OtherForm]) _ t ht
  intro p
  exact discriminant23_norm_two_form p.1 p.2

/-- The other nonprincipal class has the same theta sum. The conjugate
basis uses the same normalized form. -/
theorem discriminant23_conjugate_theta_eq (t : ℝ) (ht : 0 < t) :
    mixedAngularAverage F23 (FractionalIdeal.mk0 F23 discriminant23NormTwoConjugateRepresentative) t - 1 =
      (classThetaStar discriminant23OtherForm (Real.exp (-discriminant23ThetaScale * t)) : ℂ) := by
  apply centered_average_eq_form _ normTwoConjugateCoordinates discriminant23OtherForm
    (form_nonneg _ discriminant23_other_form_growth)
    (by norm_num [discriminant23OtherForm]) _ t ht
  intro p
  change Algebra.norm ℤ (omegaCoordinates (2 * p.1 + p.2, -p.2)) =
    (discriminant23NormTwoConjugateIdeal.absNorm : ℤ) * _
  rw [omegaCoordinates, discriminant23_quadratic_norm, discriminant23NormTwoConjugateIdeal_absNorm]
  unfold discriminant23OtherForm
  push_cast
  ring

#check @discriminant23_principal_theta_eq
#check @discriminant23_nonprincipal_theta_eq
#check @discriminant23_conjugate_theta_eq
#print axioms discriminant23_principal_theta_eq
#print axioms discriminant23_nonprincipal_theta_eq
#print axioms discriminant23_conjugate_theta_eq

end
end FieldTarget
