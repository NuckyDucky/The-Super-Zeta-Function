import DottieFixedTaylor
import DottieSharpArcCaps
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact angular and unit phase boxes for the original measuring circle. -/

namespace QuarticModel.DottieFixedIntervals

open Complex SuperZeta.StirlingCorrection
set_option autoImplicit false

def piBox : Interval := Interval.rational 3.14159265358979323846 3.14159265358979323847

theorem piBox_sound : piBox.Contains Real.pi :=
  Interval.rational_sound Real.pi_gt_d20.le Real.pi_lt_d20.le

def imaginaryBox (b : Interval) : Rect := ⟨⟨0,0⟩,b⟩

theorem imaginaryBox_sound {b : Interval} {x : ℝ} (h : b.Contains x) :
    (imaginaryBox b).Contains ((x:ℂ)*I) := by
  constructor
  · simp [imaginaryBox,Interval.Contains,Complex.mul_re]
  · simpa only [imaginaryBox,Complex.mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_one,mul_zero,add_zero] using h

private def phaseBox : Interval := Interval.rational 3.92292369 3.92292670

def circleUnitBox : Rect := ((imaginaryBox (phaseBox.sub piBox)).expBox).neg

theorem circleUnitBox_sound : circleUnitBox.Contains dottieSharpReferenceUnit := by
  obtain ⟨φ,hlo,hhi,hEq⟩ := dottie_sharp_reference_unit_phase_interval
  have hφ : phaseBox.Contains φ := Interval.rational_sound hlo.le hhi.le
  have hx := imaginaryBox_sound (Interval.sub_sound hφ piBox_sound)
  have h := Rect.neg_sound (Rect.expBox_sound hx (by decide +kernel))
  rw [hEq,show ((φ:ℂ)*I) = (((φ-Real.pi:ℝ):ℂ)*I)+(Real.pi:ℂ)*I by push_cast; ring,
    Complex.exp_add,Complex.exp_pi_mul_I,mul_neg_one]
  exact h

private noncomputable def quarterAngle (q : ℕ) (t : ℝ) : ℝ := 2*Real.pi*(t-(q:ℝ)/4)

def quarterArgBox (q : ℕ) (t : ℚ) : Rect :=
  let r : ℚ := 2*(t-(q:ℚ)/4)
  imaginaryBox (piBox.mul (Interval.rational r r))

private theorem quarterArgBox_sound (q : ℕ) (t : ℚ) :
    (quarterArgBox q t).Contains ((quarterAngle q (t:ℝ):ℂ)*I) := by
  have h := imaginaryBox_sound (Interval.mul_sound piBox_sound
    (Interval.rational_sound (lo := 2*(t-(q:ℚ)/4)) le_rfl le_rfl))
  have he : quarterAngle q (t:ℝ) = Real.pi * ((2*(t-(q:ℚ)/4):ℚ):ℝ) := by
    unfold quarterAngle
    push_cast
    ring
  rw [he]
  exact h

private theorem quarterAngle_range {q : ℕ} {t : ℝ}
    (hlo : (q:ℝ)/4 ≤ t) (hhi : t ≤ ((q:ℝ)+1)/4) :
    0 ≤ quarterAngle q t ∧ quarterAngle q t ≤ Real.pi/2 := by
  have cp : 0 ≤ 2*Real.pi := by positivity
  refine ⟨mul_nonneg cp (sub_nonneg.mpr hlo),?_⟩
  calc
    _ ≤ (2*Real.pi)*(1/4) := mul_le_mul_of_nonneg_left (by linarith only [hhi]) cp
    _ = _ := by ring

private theorem quarterAngle_mono (q : ℕ) : Monotone (quarterAngle q) := by
  intro a b hab
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hab _) (by positivity)

private def firstQuadrantBox (q : ℕ) (lo hi : ℚ) : Rect :=
  let l := (quarterArgBox q lo).expBox
  let u := (quarterArgBox q hi).expBox
  ⟨⟨u.re.lo,l.re.hi⟩,⟨l.im.lo,u.im.hi⟩⟩

private theorem firstQuadrantBox_sound (q : ℕ) {lo hi : ℚ} {t : ℝ}
    (hlo : (q:ℚ)/4 ≤ lo) (hhi : hi ≤ ((q:ℚ)+1)/4)
    (ht : t ∈ Set.Icc (lo:ℝ) (hi:ℝ))
    (hlB : (quarterArgBox q lo).normUpperTicks ≤ 2*scale)
    (huB : (quarterArgBox q hi).normUpperTicks ≤ 2*scale) :
    (firstQuadrantBox q lo hi).Contains (exp ((quarterAngle q t:ℂ)*I)) := by
  have hloR : (q:ℝ)/4 ≤ (lo:ℝ) := by
    have h : ((((q:ℚ)/4):ℚ):ℝ) ≤ (lo:ℝ) := Rat.cast_le.mpr hlo
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using h
  have hhiR : (hi:ℝ) ≤ ((q:ℝ)+1)/4 := by
    have h : (hi:ℝ) ≤ (((((q:ℚ)+1)/4):ℚ):ℝ) := Rat.cast_le.mpr hhi
    simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using h
  obtain ⟨hL₀,hL₁⟩ := quarterAngle_range hloR (ht.1.trans (ht.2.trans hhiR))
  obtain ⟨hT₀,hT₁⟩ := quarterAngle_range (hloR.trans ht.1) (ht.2.trans hhiR)
  obtain ⟨hU₀,hU₁⟩ := quarterAngle_range (hloR.trans (ht.1.trans ht.2)) hhiR
  have hL := Rect.expBox_sound (quarterArgBox_sound q lo) hlB
  have hU := Rect.expBox_sound (quarterArgBox_sound q hi) huB
  rcases hL with ⟨hLc,hLs⟩
  rcases hU with ⟨hUc,hUs⟩
  rw [Complex.exp_ofReal_mul_I_re] at hLc hUc
  rw [Complex.exp_ofReal_mul_I_im] at hLs hUs
  have hlt : quarterAngle q (lo:ℝ) ≤ quarterAngle q t := quarterAngle_mono q ht.1
  have htu : quarterAngle q t ≤ quarterAngle q (hi:ℝ) := quarterAngle_mono q ht.2
  have hc (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ Real.pi/2) (hb : 0 ≤ b) (hb' : b ≤ Real.pi/2)
      (hab : a ≤ b) : Real.cos b ≤ Real.cos a :=
    Real.antitoneOn_cos ⟨ha,ha'.trans (by linarith [Real.pi_pos])⟩
      ⟨hb,hb'.trans (by linarith [Real.pi_pos])⟩ hab
  have hs (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ Real.pi/2) (hb : 0 ≤ b) (hb' : b ≤ Real.pi/2)
      (hab : a ≤ b) : Real.sin a ≤ Real.sin b :=
    Real.monotoneOn_sin ⟨by linarith [Real.pi_pos],ha'⟩ ⟨by linarith [Real.pi_pos],hb'⟩ hab
  constructor
  · rw [Complex.exp_ofReal_mul_I_re]
    exact ⟨hUc.1.trans (mul_le_mul_of_nonneg_right (hc _ _ hT₀ hT₁ hU₀ hU₁ htu) real_scale_pos.le),
      (mul_le_mul_of_nonneg_right (hc _ _ hL₀ hL₁ hT₀ hT₁ hlt) real_scale_pos.le).trans hLc.2⟩
  · rw [Complex.exp_ofReal_mul_I_im]
    exact ⟨hLs.1.trans (mul_le_mul_of_nonneg_right (hs _ _ hL₀ hL₁ hT₀ hT₁ hlt) real_scale_pos.le),
      (mul_le_mul_of_nonneg_right (hs _ _ hT₀ hT₁ hU₀ hU₁ htu) real_scale_pos.le).trans hUs.2⟩

private def rotateQuarter (q : ℕ) (b : Rect) : Rect :=
  match q with
  | 0 => b
  | 1 => ⟨b.im.neg,b.re⟩
  | 2 => ⟨b.re.neg,b.im.neg⟩
  | _ => ⟨b.im,b.re.neg⟩

private theorem rotateQuarter_sound {q : ℕ} {b : Rect} {z : ℂ} (hq : q < 4) (hz : b.Contains z) :
    (rotateQuarter q b).Contains (I^q*z) := by
  interval_cases q
  · simpa [rotateQuarter] using hz
  · exact ⟨by simpa [rotateQuarter,Complex.mul_re] using Interval.neg_sound hz.2,
      by simpa [rotateQuarter,Complex.mul_im] using hz.1⟩
  · simpa [rotateQuarter,Rect.neg,Complex.I_sq] using Rect.neg_sound hz
  · have he : I^3 = -I := by rw [pow_succ,Complex.I_sq]; ring
    rw [he,neg_mul]
    exact ⟨by simpa [rotateQuarter,Complex.mul_re] using hz.2,
      by simpa [rotateQuarter,Complex.mul_im] using Interval.neg_sound hz.1⟩

def circleTrigBox (q : ℕ) (lo hi : ℚ) : Rect := rotateQuarter q (firstQuadrantBox q lo hi)

theorem circleTrigBox_sound (q : ℕ) {lo hi : ℚ} {t : ℝ} (hq : q < 4)
    (hlo : (q:ℚ)/4 ≤ lo) (hhi : hi ≤ ((q:ℚ)+1)/4) (ht : t ∈ Set.Icc (lo:ℝ) (hi:ℝ))
    (hlB : (quarterArgBox q lo).normUpperTicks ≤ 2*scale)
    (huB : (quarterArgBox q hi).normUpperTicks ≤ 2*scale) :
    (circleTrigBox q lo hi).Contains (exp (((2*Real.pi*t:ℝ):ℂ)*I)) := by
  have ha : ((2*Real.pi*t:ℝ):ℂ)*I =
      (q:ℂ)*((Real.pi:ℂ)/2*I)+(quarterAngle q t:ℂ)*I := by
    unfold quarterAngle
    push_cast
    ring
  rw [ha,Complex.exp_add,Complex.exp_nat_mul,Complex.exp_pi_div_two_mul_I]
  exact rotateQuarter_sound hq (firstQuadrantBox_sound q hlo hhi ht hlB huB)

def circleXBox (trig : Rect) : Interval :=
  (Interval.rational (1/64) (1/64)).add ((Interval.rational (31/2048) (31/2048)).mul trig.re)

def circleYBox (trig : Rect) : Interval := (Interval.rational (31/2048) (31/2048)).mul trig.im

theorem circleXYBox_sound {b : Rect} {t : ℝ}
    (h : b.Contains (exp (((2*Real.pi*t:ℝ):ℂ)*I))) :
    (circleXBox b).Contains ((dottieSharpPointAtTurn t).re-1/2) ∧
      (circleYBox b).Contains ((dottieSharpPointAtTurn t).im-dottieReferencePoint.im) := by
  rcases h with ⟨hc,hs⟩
  rw [Complex.exp_ofReal_mul_I_re] at hc
  rw [Complex.exp_ofReal_mul_I_im] at hs
  have hr : (Interval.rational (31/2048) (31/2048)).Contains (31/2048) :=
    Interval.rational_sound (by norm_num) (by norm_num)
  have hx : (Interval.rational (1/64) (1/64)).Contains (1/64) :=
    Interval.rational_sound (by norm_num) (by norm_num)
  have hrw : (dottieSharpPointAtTurn t).re-1/2 = 1/64 + (31/2048)*Real.cos (2*Real.pi*t) := by
    unfold dottieSharpPointAtTurn circleMap
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [Complex.exp_ofReal_mul_I_re]
    norm_num [archivedRightCenter]
    ring
  have hiw : (dottieSharpPointAtTurn t).im-dottieReferencePoint.im = (31/2048)*Real.sin (2*Real.pi*t) := by
    unfold dottieSharpPointAtTurn circleMap
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    rw [Complex.exp_ofReal_mul_I_im]
    norm_num [archivedRightCenter,dottieReferencePoint,Complex.mul_im]
  constructor
  · rw [hrw]
    exact Interval.add_sound hx (Interval.mul_sound hr hc)
  · rw [hiw]
    exact Interval.mul_sound hr hs

#print axioms circleUnitBox_sound
#print axioms circleTrigBox_sound
#print axioms circleXYBox_sound

end QuarticModel.DottieFixedIntervals
