import DottieIntervalWidths
import DottieMomentWidthConstants
import DottieFixedMomentWeights

/-! A single Horner recurrence bounds the interval width of every reduced
phase. The argument remains in the same pure imaginary segment for all norms. -/

namespace QuarticModel.DottieFixedIntervals

open Complex
open private factorialCoeff factorialCoeff_sound from DottieFixedTaylor
open private ceilNat from DottieMomentWidthConstants
open private reducedHalfPhase reducedHalfPhase_ticks momentPhase momentPhaseBox momentPhaseBox_sound
  from DottieFixedMomentWeights
set_option autoImplicit false

private theorem real_scaleNat : (scale.toNat:ℝ) = (scale:ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg scale_pos.le

private theorem ceilNat_bound (a b : ℕ) (hb : 0 < b) :
    (a:ℝ)/(b:ℝ) ≤ (ceilNat a b:ℝ) := by
  let c := a+b-1
  have he := Nat.mod_add_div c b
  have hr := Nat.mod_lt c hb
  have hc : a ≤ b*(c/b) := by
    dsimp only [c] at he hr ⊢
    omega
  apply (div_le_iff₀ (by exact_mod_cast hb)).2
  rw [mul_comm]
  exact_mod_cast hc

private theorem ceil_scaled_factorial (k : ℕ) :
    ⌈(1/(k.factorial:ℚ))*(scale:ℚ)⌉ ≤ (ceilNat scale.toNat k.factorial:ℤ) := by
  apply Int.ceil_le.mpr
  have h := ceilNat_bound scale.toNat k.factorial (Nat.factorial_pos k)
  rw [real_scaleNat] at h
  have hr : (((1/(k.factorial:ℚ))*(scale:ℚ)):ℝ) ≤ ((ceilNat scale.toNat k.factorial:ℤ):ℝ) := by
    push_cast
    simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using h
  exact_mod_cast hr

private theorem factorial_box_caps (k : ℕ) :
    ((factorialCoeff k).normUpperTicks:ℝ) ≤ (ceilNat scale.toNat k.factorial:ℝ) ∧
      ((factorialCoeff k).widthTicks:ℝ) ≤ 1 := by
  have hm := Interval.rational_nonnegative_point_abs (by positivity : (0:ℚ) ≤ 1/k.factorial)
  have hw := Interval.rational_point_width_le_one (1/(k.factorial:ℚ))
  constructor
  · simp only [factorialCoeff,Rect.rationalReal,Rect.normUpperTicks,Interval.absTicks,abs_zero,max_self,add_zero] at ⊢
    unfold Interval.absTicks at hm
    rw [hm]
    exact_mod_cast ceil_scaled_factorial k
  · have hb : (factorialCoeff k).widthTicks ≤ 1 := by
      simpa [factorialCoeff,Rect.rationalReal,Rect.widthTicks,Interval.widthTicks] using hw
    exact_mod_cast hb

private theorem rect_absTicks_nonnegative (a : Rect) : 0 ≤ (a.normUpperTicks:ℝ) := by
  have h (x : Interval) : 0 ≤ x.absTicks := (abs_nonneg x.lo).trans (le_max_left _ _)
  exact_mod_cast add_nonneg (h a.re) (h a.im)

private theorem rect_width_nonnegative {b : Rect} {z : ℂ} (h : b.Contains z) :
    0 ≤ (b.widthTicks:ℝ) := by
  have h₁ := sub_nonneg.mpr (Interval.valid_of_contains h.1)
  have h₂ := sub_nonneg.mpr (Interval.valid_of_contains h.2)
  exact_mod_cast add_nonneg h₁ h₂

private theorem half_horner_cap {a : Interval} {v : ℝ} (harg : a.Contains v)
    (hA : (a.absTicks:ℝ) ≤ (8/5)*(scale:ℝ)) (hD : (a.widthTicks:ℝ) ≤ 1) (n k : ℕ) :
    let p := (imaginaryBox a).horner n (fun j => factorialCoeff (k+j))
    (p.normUpperTicks:ℝ) ≤ ((halfPhaseHornerCaps n k).1:ℝ) ∧
      (p.widthTicks:ℝ) ≤ ((halfPhaseHornerCaps n k).2:ℝ) := by
  induction n generalizing k with
  | zero => simp [Rect.horner,Rect.zero,Rect.normUpperTicks,Rect.widthTicks,
      Interval.widthTicks,Interval.absTicks,halfPhaseHornerCaps]
  | succ n ih =>
    let p := (imaginaryBox a).horner n (fun j => factorialCoeff (k+1+j))
    let caps := halfPhaseHornerCaps n (k+1)
    have hp := Rect.horner_sound (imaginaryBox_sound harg) n
      (fun j => factorialCoeff (k+1+j)) (fun j => 1/(((k+1+j).factorial):ℂ))
      (fun j _ => factorialCoeff_sound (k+1+j))
    have hm := Rect.pure_imaginary_mul_caps (Interval.valid_of_contains harg)
      (Interval.valid_of_contains hp.1) (Interval.valid_of_contains hp.2)
    change (((imaginaryBox a).mul p).normUpperTicks:ℝ) ≤
        (a.absTicks:ℝ)*(p.normUpperTicks:ℝ)/(scale:ℝ)+2 ∧
      (((imaginaryBox a).mul p).widthTicks:ℝ) ≤
        ((a.absTicks:ℝ)*(p.widthTicks:ℝ)+(p.normUpperTicks:ℝ)*(a.widthTicks:ℝ))/(scale:ℝ)+4 at hm
    have hcastA : (p.normUpperTicks:ℝ) ≤ (caps.1:ℝ) := (ih (k+1)).1
    have hcastD : (p.widthTicks:ℝ) ≤ (caps.2:ℝ) := (ih (k+1)).2
    have hpA : 0 ≤ (p.normUpperTicks:ℝ) := rect_absTicks_nonnegative p
    have hpD : 0 ≤ (p.widthTicks:ℝ) := rect_width_nonnegative hp
    have hS : 0 ≤ (scale:ℝ) := real_scale_pos.le
    have hAS : 0 ≤ (8/5:ℝ)*(scale:ℝ) := by positivity
    have haA : 0 ≤ (a.absTicks:ℝ) := by
      exact_mod_cast (abs_nonneg a.lo).trans (le_max_left |a.lo| |a.hi|)
    have haD : 0 ≤ (a.widthTicks:ℝ) := by
      exact_mod_cast sub_nonneg.mpr (Interval.valid_of_contains harg)
    have hcA := ceilNat_bound (8*caps.1) 5 (by norm_num)
    have hcD := ceilNat_bound (8*caps.2) 5 (by norm_num)
    have hcN := ceilNat_bound caps.1 scale.toNat (by decide +kernel)
    rw [real_scaleNat] at hcN
    have h₁ : (((imaginaryBox a).mul p).normUpperTicks:ℝ) ≤
        (ceilNat (8*caps.1) 5:ℝ)+2 := by
      calc
        _ ≤ ((8/5)*(scale:ℝ))*(caps.1:ℝ)/(scale:ℝ)+2 := hm.1.trans (by gcongr)
        _ ≤ _ := by
          rw [show ((8/5)*(scale:ℝ))*(caps.1:ℝ)/(scale:ℝ)+2 =
            (8/5)*(caps.1:ℝ)+2 by field_simp [real_scale_pos.ne']]
          push_cast at hcA
          linarith only [hcA]
    have h₂ : (((imaginaryBox a).mul p).widthTicks:ℝ) ≤
        (ceilNat (8*caps.2) 5:ℝ)+(ceilNat caps.1 scale.toNat:ℝ)+4 := by
      calc
        _ ≤ (((8/5)*(scale:ℝ))*(caps.2:ℝ)+(caps.1:ℝ)*1)/(scale:ℝ)+4 := hm.2.trans (by gcongr)
        _ ≤ _ := by
          rw [add_div, mul_one,show ((8/5)*(scale:ℝ))*(caps.2:ℝ)/(scale:ℝ) =
            (8/5)*(caps.2:ℝ) by field_simp [real_scale_pos.ne']]
          push_cast at hcD
          linarith only [hcD,hcN]
    have hAdd := Rect.normUpperTicks_add_le (factorialCoeff k) ((imaginaryBox a).mul p)
    have hAdd' : (((factorialCoeff k).add ((imaginaryBox a).mul p)).normUpperTicks:ℝ) ≤
        ((factorialCoeff k).normUpperTicks:ℝ)+(((imaginaryBox a).mul p).normUpperTicks:ℝ) := by exact_mod_cast hAdd
    have eqArgs : (fun j : ℕ => factorialCoeff (k+(j+1))) = (fun j => factorialCoeff (k+1+j)) := by
      funext j
      congr 1
      omega
    simp only [Rect.horner,Nat.add_zero,eqArgs,halfPhaseHornerCaps]
    change (((factorialCoeff k).add ((imaginaryBox a).mul p)).normUpperTicks:ℝ) ≤ _ ∧
      (((factorialCoeff k).add ((imaginaryBox a).mul p)).widthTicks:ℝ) ≤ _
    have hf := factorial_box_caps k
    constructor
    · push_cast
      change _ ≤ (ceilNat (8*caps.1) 5:ℝ)+2+(ceilNat scale.toNat k.factorial:ℝ)
      linarith only [hAdd',hf.1,h₁]
    · rw [Rect.width_add]
      push_cast
      change _ ≤ (ceilNat (8*caps.2) 5:ℝ)+(ceilNat caps.1 scale.toNat:ℝ)+5
      linarith only [hf.2,h₂]

private theorem half_phase_box_caps (n : ℕ) :
    (((reducedHalfPhase n).expBox).normUpperTicks:ℝ) ≤ 91367321521602237405 ∧
      (((reducedHalfPhase n).expBox).widthTicks:ℝ) ≤ 772516 := by
  let θ := dottieMomentReducedAngle n/2
  let a := Interval.rational θ θ
  have harg : a.Contains (θ:ℝ) := Interval.rational_sound le_rfl le_rfl
  obtain ⟨hl,hh⟩ := dottie_moment_reduced_angle_bounds n
  have hπ : dottieMomentPiRat ≤ 318/100 := by norm_num [dottieMomentPiRat]
  have hr : |(θ:ℝ)| ≤ 159/100 := by
    have habs : |θ| ≤ 159/100 := by
      apply abs_le.mpr
      dsimp only [θ]
      constructor <;> linarith only [hl,hh,hπ]
    have hcast : ((|θ|:ℚ):ℝ) ≤ ((159/100:ℚ):ℝ) := Rat.cast_le.mpr habs
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using hcast
  have hA : (a.absTicks:ℝ) ≤ (8/5)*(scale:ℝ) :=
    (Interval.rational_abs_le hr hr).trans (by norm_num [scale])
  have hD : (a.widthTicks:ℝ) ≤ 1 := by exact_mod_cast Interval.rational_point_width_le_one θ
  have hH := half_horner_cap harg hA hD 24 0
  have hCaps : halfPhaseHornerCaps 24 0 = (91367321521602235409,768524) := by decide +kernel
  rw [hCaps] at hH
  simp only [zero_add] at hH
  let p := (imaginaryBox a).horner 24 factorialCoeff
  have hP : (p.normUpperTicks:ℝ) ≤ 91367321521602235409 ∧
      (p.widthTicks:ℝ) ≤ 768524 := by simpa only [Nat.cast_ofNat] using hH
  have hPad : ⌈expTail*(scale:ℚ)⌉ = 998 := by decide +kernel
  change (((p.pad expTail).normUpperTicks:ℝ) ≤ _) ∧ (((p.pad expTail).widthTicks:ℝ) ≤ _)
  have hm := Rect.pad_magnitude (b := p) (e := expTail) (by norm_num [expTail])
  have hw := Rect.pad_width p expTail
  rw [hPad] at hm hw
  have hm' : ((p.pad expTail).normUpperTicks:ℝ) ≤ (p.normUpperTicks:ℝ)+2*998 := by exact_mod_cast hm
  have hw' : ((p.pad expTail).widthTicks:ℝ) = (p.widthTicks:ℝ)+4*998 := by exact_mod_cast hw
  exact ⟨hm'.trans (by linarith only [hP.1]),hw'.le.trans (by linarith only [hP.2])⟩

theorem dottie_uniform_phase_width (n : ℕ) :
    ((momentPhaseBox n).widthTicks:ℝ) ≤ 15100000 := by
  let p := (reducedHalfPhase n).expBox
  let θ := dottieMomentReducedAngle n/2
  have hArg : (reducedHalfPhase n).Contains (((θ:ℝ):ℂ)*I) :=
    imaginaryBox_sound (Interval.rational_sound le_rfl le_rfl)
  have hp := Rect.expBox_sound hArg (reducedHalfPhase_ticks n)
  have h₁ := Interval.valid_of_contains hp.1
  have h₂ := Interval.valid_of_contains hp.2
  have hm : (p.normUpperTicks:ℝ) ≤ 91367321521602237405 := (half_phase_box_caps n).1
  have hw : (p.widthTicks:ℝ) ≤ 772516 := (half_phase_box_caps n).2
  have hD : 0 ≤ (p.widthTicks:ℝ) := rect_width_nonnegative hp
  have hProduct := Rect.mul_width_bound h₁ h₂ h₁ h₂
  change ((p.mul p).widthTicks:ℝ) ≤
    ((p.normUpperTicks:ℝ)*(p.widthTicks:ℝ)+(p.normUpperTicks:ℝ)*(p.widthTicks:ℝ))/(scale:ℝ)+8
    at hProduct
  have hPad : ⌈(1/10^13:ℚ)*(scale:ℚ)⌉ = 1844675 := by decide +kernel
  change (((p.mul p).pad (1/10^13)).widthTicks:ℝ) ≤ _
  rw [Rect.pad_width,hPad]
  push_cast
  calc
    _ ≤ (2*91367321521602237405*772516)/(scale:ℝ)+8+4*1844675 := by
      have hpw := mul_le_mul hm hw hD (by norm_num : (0:ℝ) ≤ 91367321521602237405)
      have hpw' := div_le_div_of_nonneg_right (add_le_add hpw hpw) real_scale_pos.le
      have hb := hProduct.trans (add_le_add hpw' (le_refl (8:ℝ)))
      linarith only [hb]
    _ ≤ _ := by norm_num [scale]

theorem dottie_uniform_phase_magnitude {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) :
    ((momentPhaseBox n).normUpperTicks:ℝ) ≤ 3*(scale:ℝ) := by
  have h := momentPhaseBox_sound hn hN
  have hUnit : ‖momentPhase n‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have hr := (Complex.abs_re_le_norm (momentPhase n)).trans_eq hUnit
  have hi := (Complex.abs_im_le_norm (momentPhase n)).trans_eq hUnit
  calc
    _ ≤ (|(momentPhase n).re| + |(momentPhase n).im|)*(scale:ℝ)+
        ((momentPhaseBox n).widthTicks:ℝ) := Rect.absTicks_le_of_contains h
    _ ≤ (1+1)*(scale:ℝ)+15100000 := add_le_add
      (mul_le_mul_of_nonneg_right (add_le_add hr hi) real_scale_pos.le) (dottie_uniform_phase_width n)
    _ ≤ _ := by norm_num [scale]

#print axioms dottie_uniform_phase_width
#print axioms dottie_uniform_phase_magnitude

end QuarticModel.DottieFixedIntervals
