import Discriminant23ThetaEnvelope

namespace FieldTarget

open Finset

/-- Integer coefficients of the difference of the two finite norm readings. -/
def discriminant23CharacterCoefficient (n : ℕ) : ℤ :=
  [0, 2, -2, -2, 0, 0, 2, 0, 2, 0, 0, 0, 0, -2, 0, 0, -2,
    0, 0, 0, 0, 0, 0, 2, -2, 2, 2, 2, 0, -2, 0, -2, 0].getD n 0

noncomputable def discriminant23CharacterPolynomial (q : ℝ) : ℝ :=
  ∑ n ∈ range 33, (discriminant23CharacterCoefficient n : ℝ) * q ^ n

private def classCoefficient (Q : ℤ → ℤ → ℤ) (n : ℕ) : ℕ :=
  ((characterThetaTerms Q).filter (fun p ↦ (Q p.1 p.2).toNat = n)).card

private theorem classThetaFinite_eq_coefficients (Q : ℤ → ℤ → ℤ) (q : ℝ) :
    classThetaFinite Q q = ∑ n ∈ range 33, (classCoefficient Q n : ℝ) * q ^ n := by
  have hn (p : ℤ × ℤ) (hp : p ∈ characterThetaTerms Q) :
      (Q p.1 p.2).toNat ∈ range 33 := by
    have hb : Q p.1 p.2 ≤ 32 := (mem_filter.mp hp).2.2
    exact mem_range.mpr (by omega)
  unfold classThetaFinite classCoefficient
  rw [← sum_fiberwise_of_maps_to' hn (fun n ↦ q ^ n)]
  simp only [sum_const, nsmul_eq_mul]

private theorem coefficient_table : ∀ n : Fin 33,
    (classCoefficient discriminant23PrincipalForm n : ℤ) -
      (classCoefficient discriminant23OtherForm n : ℤ) =
        discriminant23CharacterCoefficient n := by
  decide +kernel

theorem discriminant23_characterPolynomial_eq_finite (q : ℝ) :
    discriminant23CharacterPolynomial q =
      classThetaFinite discriminant23PrincipalForm q - classThetaFinite discriminant23OtherForm q := by
  rw [classThetaFinite_eq_coefficients, classThetaFinite_eq_coefficients,
    ← sum_sub_distrib, discriminant23CharacterPolynomial]
  apply sum_congr rfl
  intro n hn
  rw [← sub_mul]
  congr 1
  exact_mod_cast (coefficient_table ⟨n, mem_range.mp hn⟩).symm

theorem discriminant23_characterPolynomial_error {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    |classThetaStar discriminant23PrincipalForm q - classThetaStar discriminant23OtherForm q -
      discriminant23CharacterPolynomial q| ≤ q / 100000 := by
  obtain ⟨hp₀, hp₁⟩ := classThetaStar_sub_finite_bounds discriminant23PrincipalForm
    discriminant23_principal_form_growth hq hqu
  obtain ⟨hn₀, hn₁⟩ := classThetaStar_sub_finite_bounds discriminant23OtherForm
    discriminant23_other_form_growth hq hqu
  rw [discriminant23_characterPolynomial_eq_finite]
  exact abs_le.mpr ⟨by linarith, by linarith⟩


theorem discriminant23_characterPolynomial_error_sharp {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    |classThetaStar discriminant23PrincipalForm q - classThetaStar discriminant23OtherForm q -
      discriminant23CharacterPolynomial q| ≤ 16 * q ^ 23 := by
  have hPrincipal (m n : ℤ) :
      9 * (m ^ 2 + n ^ 2) ≤ 10 * discriminant23PrincipalForm m n := by
    unfold discriminant23PrincipalForm
    nlinarith only [sq_nonneg (m + 5 * n), sq_nonneg n]
  have hOther (m n : ℤ) :
      9 * (m ^ 2 + n ^ 2) ≤ 10 * discriminant23OtherForm m n := by
    unfold discriminant23OtherForm
    nlinarith only [sq_nonneg (m + n), sq_nonneg m, sq_nonneg n]
  obtain ⟨hp₀, hp₁⟩ := classThetaStar_sub_finite_bounds_sharp _ hPrincipal hq hqu
  obtain ⟨hn₀, hn₁⟩ := classThetaStar_sub_finite_bounds_sharp _ hOther hq hqu
  rw [discriminant23_characterPolynomial_eq_finite]
  exact abs_le.mpr ⟨by linarith only [hp₀, hn₁], by linarith only [hp₁, hn₀]⟩

#print axioms discriminant23_characterPolynomial_error_sharp
#check @discriminant23_characterPolynomial_error
#print axioms coefficient_table
#print axioms discriminant23_characterPolynomial_eq_finite
#print axioms discriminant23_characterPolynomial_error

end FieldTarget
