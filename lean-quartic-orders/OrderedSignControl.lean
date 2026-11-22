import QuarticOrderedTurns

/-! A positive three-atom bilateral Laplace transform tests the logical force
of the even reflection sign. Its coefficients are chosen explicitly and are
independent of the arithmetic of the quartic. -/

namespace SuperZeta.OrderedSignControl
noncomputable section
open Complex RingReversibility GaussianRingMidpoint QuarticOrderedTurns
open scoped ComplexConjugate

/-- The transform of symmetric masses of size 1/2 at ±b, together with
mass cosh(ba) at 0. The argument z measures displacement from 1/2. -/
def transform (a b : ℝ) (z : ℂ) : ℂ :=
  Complex.cosh ((b : ℂ) * z) + (Real.cosh (b * a) : ℂ)

theorem positive_center_mass (a b : ℝ) : 0 < Real.cosh (b * a) := Real.cosh_pos _

theorem three_masses (a b : ℝ) (z : ℂ) :
    transform a b z = Complex.exp ((b:ℂ)*z)/2 + Complex.exp (-((b:ℂ)*z))/2 +
      (Real.cosh (b*a) : ℂ) := by unfold transform Complex.cosh; ring

theorem transform_even (a b : ℝ) (z : ℂ) : transform a b (-z) = transform a b z := by
  simp [transform, mul_neg, Complex.cosh_neg]

theorem transform_mirror (a b : ℝ) (z : ℂ) :
    transform a b (-conj z) = conj (transform a b z) := by
  rw [transform_even]
  simp only [transform, map_add, ← Complex.cosh_conj, map_mul, Complex.conj_ofReal]

theorem transform_entire (a b : ℝ) : Differentiable ℂ (transform a b) := by
  unfold transform
  fun_prop

theorem positive_real_reading (a b x : ℝ) : 0 < (transform a b x).re := by
  simp only [transform, ← Complex.ofReal_mul, Complex.add_re, Complex.cosh_ofReal_re,
    Complex.ofReal_re]
  exact add_pos (Real.cosh_pos _) (Real.cosh_pos _)

/-- Up to the selected height T, this control passes the same qualitative
left-or-right sign test at every positive height. -/
theorem side_until_chosen_height (a x t T : ℝ) (ht : 0 < t) (htT : t < T) :
    (0 < (transform a (Real.pi/T) ((x:ℂ)+(t:ℂ)*I)).im ↔ 0 < x) ∧
    ((transform a (Real.pi/T) ((x:ℂ)+(t:ℂ)*I)).im < 0 ↔ x < 0) := by
  let b := Real.pi / T
  have hT := ht.trans htT
  have hb : 0 < b := div_pos Real.pi_pos hT
  have hp : 0 < Real.sin (b*t) := by
    apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hb ht)
    calc b*t < b*T := mul_lt_mul_of_pos_left htT hb
         _ = Real.pi := div_mul_cancel₀ _ hT.ne'
  have hi : (transform a b ((x:ℂ)+(t:ℂ)*I)).im =
      Real.sinh (b*x)*Real.sin (b*t) := by
    unfold transform
    rw [mul_add, ←mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero,
      zero_add, mul_one]
  change (0 < (transform a b _).im ↔ 0 < x) ∧ ((transform a b _).im < 0 ↔ x < 0)
  rw [hi, mul_pos_iff_of_pos_right hp, mul_neg_iff, Real.sinh_pos_iff,
    mul_pos_iff_of_pos_left hb]
  simp only [not_lt_of_ge hp.le, hp, and_false, and_true, false_or, Real.sinh_neg_iff,
    mul_neg_iff, hb, not_lt_of_ge hb.le, true_and, false_and, or_false]

theorem chosen_zero (a t : ℝ) (ht : t ≠ 0) :
    transform a (Real.pi/t) ((a:ℂ)+(t:ℂ)*I) = 0 := by
  have hphase : ((Real.pi / t : ℝ) : ℂ) * (t : ℂ) = (Real.pi : ℂ) := by
    exact_mod_cast div_mul_cancel₀ Real.pi ht
  unfold transform
  rw [mul_add, ← mul_assoc, hphase, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I, Complex.cos_pi, Complex.sin_pi, Complex.ofReal_cosh,
    Complex.ofReal_mul]
  ring

def displacement (w : ℂ) : ℂ := w - 1/2

theorem mirror_displacement (w : ℂ) : displacement (mirror w) = -conj (displacement w) := by
  simp only [displacement, mirror, map_sub, map_div₀, map_one, map_ofNat]
  ring

theorem pair_at_input (w : ℂ) (ht : w.im ≠ 0) :
    let f := transform (w.re-1/2) (Real.pi/w.im)
    f (displacement w) = 0 ∧ f (displacement (mirror w)) = 0 := by
  dsimp only
  have hw : displacement w = (((w.re-1/2 : ℝ) : ℂ) + (w.im:ℂ)*I) := by
    unfold displacement
    push_cast
    linear_combination -(Complex.re_add_im w)
  have hz := chosen_zero (w.re-1/2) w.im ht
  rw [←hw] at hz
  exact ⟨hz, by rw [mirror_displacement, transform_mirror, hz, map_zero]⟩

/-- At the actual super-zeta addresses of both ring inputs, the model
with the positive reflection sign can have equal Hamilton orders while
the spectral addresses remain distinguishable. -/
theorem sign_control_on_ring {w : ℂ} (hw : w ∈ rightRing) (D : ℂ → ℂ) :
    let f := transform (w.re-1/2) (Real.pi/w.im)
    let q (v : ℂ) := pack (f (displacement v)) (D v)
    jk (q w) = kj (q w) ∧ jk (q (mirror w)) = kj (q (mirror w)) ∧
      phi w ≠ phi (mirror w) := by
  have ht := (inputOfRing hw).property.2
  change 101 ≤ (w / 2).im at ht
  rw [Complex.div_ofNat_im] at ht
  have h := pair_at_input w (by linarith : w.im ≠ 0)
  exact ⟨(order_eq_iff _ _).mpr h.1, (order_eq_iff _ _).mpr h.2,
    addresses_separate hw⟩

#print axioms sign_control_on_ring
#print axioms three_masses
#print axioms positive_real_reading
#print axioms transform_entire
#print axioms side_until_chosen_height

end
end SuperZeta.OrderedSignControl
