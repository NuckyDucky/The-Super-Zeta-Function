import DottieFixedIntervals
import DottieSharpFactoredProjection

/-! Taylor enclosures used by the signed dyadic contour calculation. -/

namespace QuarticModel.DottieFixedIntervals

open Complex Finset
open private dottieHorner dottieHorner_eq_sum from DottieSharpFactoredProjection
set_option autoImplicit false

def Rect.horner (z : Rect) : ℕ → (ℕ → Rect) → Rect
  | 0, _ => Rect.zero
  | n+1, f => (f 0).add (z.mul (z.horner n (fun k => f (k+1))))

theorem Rect.horner_sound {b : Rect} {z : ℂ} (hz : b.Contains z)
    (n : ℕ) (f : ℕ → Rect) (g : ℕ → ℂ)
    (hf : ∀ k < n, (f k).Contains (g k)) :
    (b.horner n f).Contains (∑ k ∈ range n, g k*z^k) := by
  rw [← dottieHorner_eq_sum]
  induction n generalizing f g with
  | zero => exact Rect.zero_sound
  | succ n ih =>
    have htail := ih (fun k => f (k+1)) (fun k => g (k+1)) (fun k hk => hf (k+1) (by omega))
    exact Rect.add_sound (hf 0 (by omega)) (Rect.mul_sound hz htail)

private def factorialCoeff (k : ℕ) : Rect := Rect.rationalReal (1/(k.factorial : ℚ))

private theorem factorialCoeff_sound (k : ℕ) :
    (factorialCoeff k).Contains (1/(k.factorial : ℂ)) := by
  simpa only [factorialCoeff,Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_natCast] using Rect.rationalReal_sound (1/(k.factorial : ℚ))

def expTail : ℚ := 2*(2:ℚ)^24/(24 : ℕ).factorial

def dividedSinhTail : ℚ := 92*(2:ℚ)^24/(25 : ℕ).factorial

theorem Rect.norm_le_of_ticks {b : Rect} {z : ℂ} {k : ℤ} (hz : b.Contains z)
    (h : b.normUpperTicks ≤ k*scale) : ‖z‖ ≤ (k : ℝ) := by
  apply (mul_le_mul_iff_of_pos_right real_scale_pos).mp
  exact (Rect.normUpperTicks_sound hz).trans (by exact_mod_cast h)

def Rect.expBox (b : Rect) : Rect := (b.horner 24 factorialCoeff).pad expTail

theorem Rect.expBox_sound {b : Rect} {z : ℂ} (hz : b.Contains z)
    (h : b.normUpperTicks ≤ 2*scale) : b.expBox.Contains (exp z) := by
  have hd : ‖z‖ ≤ 2 := by simpa using Rect.norm_le_of_ticks hz h
  have hpoly := Rect.horner_sound hz 24 factorialCoeff (fun k => 1/(k.factorial : ℂ))
    (fun k _ => factorialCoeff_sound k)
  have hpoly' : (b.horner 24 factorialCoeff).Contains (∑ k ∈ range 24, z^k/k.factorial) := by
    convert hpoly using 2
    ring
  apply Rect.pad_sound hpoly'
  have htail := Complex.exp_bound' (x := z) (n := 24) (by norm_num; linarith only [hd])
  refine htail.trans ?_
  push_cast [expTail]
  rw [show 2*(2:ℝ)^24/(24 : ℕ).factorial = (2:ℝ)^24/(24 : ℕ).factorial*2 by ring]
  gcongr

private theorem even_power_sum (z : ℂ) (k : ℕ) (d : ℕ) :
    (1/(d.factorial : ℂ)) * (z*z)^k = z^(2*k)/d.factorial := by
  rw [← pow_two,← pow_mul]
  ring

def Rect.coshBox (b : Rect) : Rect :=
  ((b.mul b).horner 12 (fun k => factorialCoeff (2*k))).pad expTail

theorem Rect.coshBox_sound {b : Rect} {z : ℂ} (hz : b.Contains z)
    (h : b.normUpperTicks ≤ 2*scale) : b.coshBox.Contains (cosh z) := by
  have hd : ‖z‖ ≤ 2 := by simpa using Rect.norm_le_of_ticks hz h
  have hpoly := Rect.horner_sound (Rect.mul_sound hz hz) 12 (fun k => factorialCoeff (2*k))
    (fun k => 1/((2*k).factorial : ℂ)) (fun k _ => factorialCoeff_sound (2*k))
  simp only [even_power_sum] at hpoly
  apply Rect.pad_sound hpoly
  push_cast [expTail]
  exact dottie_cosh_taylor_radius hd

def Rect.dividedSinhBox (c z : Rect) : Rect :=
  (c.mul ((z.mul z).horner 12 (fun k => factorialCoeff (2*k+1)))).pad dividedSinhTail

theorem Rect.dividedSinhBox_sound {cb zb : Rect} {c x : ℂ} (hc : cb.Contains c)
    (hz : zb.Contains (x*c)) (hx : x ≠ 0)
    (hcB : cb.normUpperTicks ≤ 46*scale) (hzB : zb.normUpperTicks ≤ 2*scale) :
    (cb.dividedSinhBox zb).Contains (sinh (x*c)/x) := by
  have hd : ‖x*c‖ ≤ 2 := by simpa using Rect.norm_le_of_ticks hz hzB
  have hcd : ‖c‖ ≤ 46 := by simpa using Rect.norm_le_of_ticks hc hcB
  have hpoly := Rect.horner_sound (Rect.mul_sound hz hz) 12 (fun k => factorialCoeff (2*k+1))
    (fun k => 1/((2*k+1).factorial : ℂ)) (fun k _ => factorialCoeff_sound (2*k+1))
  simp only [even_power_sum] at hpoly
  have hb := Rect.mul_sound hc hpoly
  apply Rect.pad_sound hb
  push_cast [dividedSinhTail]
  exact dottie_divided_sinh_radius hx hcd hd

#print axioms Rect.horner_sound
#print axioms Rect.expBox_sound
#print axioms Rect.coshBox_sound
#print axioms Rect.dividedSinhBox_sound

end QuarticModel.DottieFixedIntervals
