import DedekindDiscriminant23CharacterQuadrature
import DedekindDiscriminant23CharacterGridLower
import DedekindDiscriminant23CharacterGridUpper

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
private theorem gridSigns_checked :
    3 * scale ≤ 5000 * (discriminant23CharacterGridBox false).lo ∧
      1250 * (discriminant23CharacterGridBox true).hi ≤ -scale := by
  simp only [discriminant23CharacterGridBox,
    discriminant23_characterGridLower_exact, discriminant23_characterGridUpper_exact]
  decide +kernel

private theorem lower_trapezoid :
    (3 / 5000 : ℝ) ≤ trapezoidal_integral (discriminant23CharacterLogPolynomial 5) 1024 0 3 := by
  have hc := (discriminant23_characterGridBox_contains false).1
  norm_num [discriminant23EndpointHeight, discriminant23EndpointNumerator] at hc
  have hb : 3 * (scale : ℝ) ≤ 5000 * ((discriminant23CharacterGridBox false).lo : ℝ) := by
    exact_mod_cast gridSigns_checked.1
  apply le_of_mul_le_mul_left _ scale_pos
  linarith only [hb, hc]

private theorem upper_trapezoid :
    trapezoidal_integral (discriminant23CharacterLogPolynomial (11 / 2)) 1024 0 3 ≤
      -(1 / 1250 : ℝ) := by
  have hc := (discriminant23_characterGridBox_contains true).2
  norm_num [discriminant23EndpointHeight, discriminant23EndpointNumerator] at hc
  have hb : 1250 * ((discriminant23CharacterGridBox true).hi : ℝ) ≤ -(scale : ℝ) := by
    exact_mod_cast gridSigns_checked.2
  apply le_of_mul_le_mul_left _ scale_pos
  linarith only [hb, hc]

theorem discriminant23_characterFold_re_pos_at_five :
    0 < (discriminant23CharacterFold ⟨1 / 2, 5⟩).re := by
  have h := (abs_le.mp (discriminant23_characterFold_trapezoid_error
    (t := 5) (by norm_num))).1
  linarith only [h, lower_trapezoid]

theorem discriminant23_characterFold_re_neg_at_eleven_halves :
    (discriminant23CharacterFold ⟨1 / 2, 11 / 2⟩).re < 0 := by
  have h := (abs_le.mp (discriminant23_characterFold_trapezoid_error
    (t := 11 / 2) (by norm_num))).2
  linarith only [h, upper_trapezoid]

/-- A kernel-certified zero of the actual splitting-field Dedekind zeta on
the critical line in the open height interval (5, 11/2). -/
theorem discriminant23_dedekind_zero_between_five_and_eleven_halves :
    ∃ t ∈ Set.Ioo (5 : ℝ) (11 / 2),
      discriminant23CharacterFold ⟨1 / 2, t⟩ = 0 ∧
      mixedThetaContinuation Discriminant23GaloisField ⟨1 / 2, t⟩ = 0 :=
  discriminant23_dedekind_zero_between_character_signs (by norm_num)
    discriminant23_characterFold_re_pos_at_five discriminant23_characterFold_re_neg_at_eleven_halves

theorem discriminant23_dedekind_order_ge_two_between_five_and_eleven_halves :
    ∃ t ∈ Set.Ioo (5 : ℝ) (11 / 2),
      2 ≤ analyticOrderNatAt (mixedThetaContinuation Discriminant23GaloisField) ⟨1 / 2, t⟩ := by
  obtain ⟨t, ht, hC, _⟩ := discriminant23_dedekind_zero_between_five_and_eleven_halves
  let w : ℂ := ⟨1 / 2, t⟩
  refine ⟨t, ht, ?_⟩
  change 2 ≤ analyticOrderNatAt (mixedThetaContinuation Discriminant23GaloisField) w
  have hlo : 0 < w.re := by norm_num [w]
  have hhi : w.re < 1 := by norm_num [w]
  have hOrder : analyticOrderNatAt discriminant23CharacterFold w ≠ 0 := by
    intro h
    exact ((discriminant23CharacterCountingFunction.orderNat_eq_zero_iff w).mp h) hC
  rw [discriminant23_dedekind_orderNat_eq_base_add_character hlo hhi]
  omega

#check @discriminant23_dedekind_zero_between_five_and_eleven_halves
#check @discriminant23_dedekind_order_ge_two_between_five_and_eleven_halves
#print axioms gridSigns_checked
#print axioms discriminant23_characterFold_re_pos_at_five
#print axioms discriminant23_characterFold_re_neg_at_eleven_halves
#print axioms discriminant23_dedekind_zero_between_five_and_eleven_halves
#print axioms discriminant23_dedekind_order_ge_two_between_five_and_eleven_halves

end

end FieldTarget
