import DottieUniformPhaseWidth
import DottieNormalizedMomentScore

/-! Rounding applies uniformly to all moment weights at the original Dottie
height. The integer sums can then be checked in blocks without repeating the
analytic enclosure proof for each norm. -/

namespace QuarticModel.DottieFixedIntervals

open Complex
open private normalizedLogBox normalizedLogBox_sound inverseSqrtBox inverseSqrtBox_sound
  Interval.power Interval.power_sound momentPhaseBox momentPhaseBox_sound from DottieFixedMomentWeights
set_option autoImplicit false

private theorem int_le_of_real_lt_succ {a b : ℤ} (h : (a:ℝ) < (b:ℝ)+1) : a ≤ b := by
  have h' : (a:ℝ) < ((b+1:ℤ):ℝ) := by push_cast; exact h
  have hi : a < b+1 := by exact_mod_cast h'
  omega

private theorem log_box_caps {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) :
    ((normalizedLogBox n).absTicks:ℝ) ≤ (3/4)*(scale:ℝ) ∧
    ((normalizedLogBox n).widthTicks:ℝ) ≤ 2 := by
  let l : ℚ := dottieQuickLogLowerTicks n
  have hw := Interval.rational_width_lt (-(l+128)/2^101) (-l/2^101)
  have he : ((-l/2^101:ℚ):ℝ)-((-(l+128)/2^101:ℚ):ℝ) = 128/2^101 := by
    push_cast
    ring
  rw [he] at hw
  have hW : (normalizedLogBox n).widthTicks ≤ 2 := int_le_of_real_lt_succ
    (hw.trans (by norm_num [scale]))
  have hWr : ((normalizedLogBox n).widthTicks:ℝ) ≤ 2 := by exact_mod_cast hW
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hN' : (n:ℝ) ≤ (2:ℝ)^31 := by
    exact_mod_cast hN.trans (show dottiePrefixEnd ≤ 2^31 by decide +kernel)
  have hl : Real.log n ≤ 22 := calc
    _ ≤ Real.log ((2:ℝ)^31) := Real.log_le_log (by linarith) hN'
    _ = 31*Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ _ := by linarith only [Real.log_two_lt_d9]
  have hl₀ := Real.log_nonneg hn'
  have hval : |(-Real.log n/32)| ≤ 22/32 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have habs := Interval.absTicks_le_of_contains (normalizedLogBox_sound hn hN)
  refine ⟨habs.trans ?_,hWr⟩
  calc
    _ ≤ (22/32)*(scale:ℝ)+2 :=
      add_le_add (mul_le_mul_of_nonneg_right hval real_scale_pos.le) hWr
    _ ≤ _ := by norm_num [scale]

private theorem power_box_caps {b : Interval} {v : ℝ} (hb : b.Contains v)
    (ha : (b.absTicks:ℝ) ≤ (3/4)*(scale:ℝ)) (hd : (b.widthTicks:ℝ) ≤ 2) (k : ℕ) :
    ((Interval.power b k).absTicks:ℝ) ≤ (scale:ℝ) ∧
    ((Interval.power b k).widthTicks:ℝ) ≤ 16 := by
  have hB := Interval.valid_of_contains hb
  have hD : 0 ≤ (b.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr hB
  have hS := real_scale_pos.le
  have hS' : 0 ≤ (3/4:ℝ)*(scale:ℝ) := by positivity
  induction k with
  | zero => simp [Interval.power, Interval.absTicks, Interval.widthTicks, abs_of_pos scale_pos]
  | succ k ih =>
    let p := Interval.power b k
    have hP := Interval.valid_of_contains (Interval.power_sound hb k)
    have hPd : 0 ≤ (p.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr hP
    change ((p.mul b).absTicks:ℝ) ≤ (scale:ℝ) ∧ ((p.mul b).widthTicks:ℝ) ≤ 16
    constructor
    · refine (Interval.mul_magnitude_bound hP hB).trans ?_
      have h := mul_le_mul ih.1 ha
        (show 0 ≤ (b.absTicks:ℝ) by exact_mod_cast (abs_nonneg b.lo).trans (le_max_left _ _)) hS
      refine (add_le_add (div_le_div_of_nonneg_right h hS) (le_refl (1:ℝ))).trans ?_
      norm_num [scale]
    · refine (Interval.mul_width_bound hP hB).trans ?_
      have h₁ := mul_le_mul ih.1 hd hD hS
      have h₂ := mul_le_mul ha ih.2 hPd hS'
      refine (add_le_add (div_le_div_of_nonneg_right (add_le_add h₁ h₂) hS) (le_refl (2:ℝ))).trans ?_
      norm_num [scale]

private theorem inverse_root_tick_caps {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) :
    inverseRootTickLower ≤ inverseSqrtTicks scale.toNat n ∧
      inverseSqrtTicks scale.toNat n ≤ scale.toNat := by
  unfold inverseSqrtTicks
  constructor
  · apply Nat.le_sqrt'.mpr
    apply (Nat.le_div_iff_mul_le hn).2
    exact (Nat.mul_le_mul_left _ hN).trans inverseRootTickLower_sq_le
  · exact (Nat.sqrt_le_sqrt (Nat.div_le_self _ _)).trans_eq (Nat.sqrt_eq' _)

private theorem inverse_box_caps (n : ℕ) :
    (inverseSqrtBox n).absTicks = (inverseSqrtTicks scale.toNat n:ℤ)+1 ∧
      (inverseSqrtBox n).widthTicks = 1 := by
  let m : ℤ := inverseSqrtTicks scale.toNat n
  have hm : 0 ≤ m := by positivity
  change max |m| |m+1| = m+1 ∧ m+1-m = 1
  rw [abs_of_nonneg hm, abs_of_nonneg (by omega : 0 ≤ m+1),max_eq_right (by omega : m ≤ m+1)]
  exact ⟨rfl,by omega⟩

private theorem factorial_box_caps (k : ℕ) :
    let f : ℚ := 1/(k.factorial:ℚ)
    (Interval.rational f f).absTicks ≤ scale ∧ (Interval.rational f f).widthTicks ≤ 1 := by
  intro f
  have hf : f ≤ 1 := (div_le_iff₀ (by positivity)).2 (by
    rw [one_mul]
    exact_mod_cast (show 1 ≤ k.factorial by have hp := Nat.factorial_pos k; omega))
  have hS : 0 ≤ (scale:ℚ) := by exact_mod_cast scale_pos.le
  refine ⟨?_,Interval.rational_point_width_le_one f⟩
  rw [Interval.rational_nonnegative_point_abs (by positivity : 0 ≤ f)]
  exact Int.ceil_le.mpr (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hf hS)

private theorem box_radius_le_width {a : Interval} (ha : a.lo ≤ a.hi) :
    a.radiusTicks ≤ a.widthTicks := by
  unfold Interval.radiusTicks Interval.midpointTicks Interval.widthTicks
  apply max_le <;> omega

private theorem moment_magnitude_caps {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) (k : ℕ) :
    let f : ℚ := 1/(k.factorial:ℚ)
    let a := ((inverseSqrtBox n).mul (Interval.power (normalizedLogBox n) k)).mul (Interval.rational f f)
    (a.absTicks:ℝ) ≤ (inverseSqrtTicks scale.toNat n:ℝ)+3 ∧ a.widthTicks ≤ 22 := by
  let m := inverseSqrtTicks scale.toNat n
  let b := inverseSqrtBox n
  let p := Interval.power (normalizedLogBox n) k
  let a := b.mul p
  let f : ℚ := 1/(k.factorial:ℚ)
  let c := Interval.rational f f
  change ((a.mul c).absTicks:ℝ) ≤ (m:ℝ)+3 ∧ (a.mul c).widthTicks ≤ 22
  have hB := inverseSqrtBox_sound hn
  have hP := Interval.power_sound (normalizedLogBox_sound hn hN) k
  have hA := Interval.mul_sound hB hP
  have hC : c.Contains (f:ℝ) := Interval.rational_sound le_rfl le_rfl
  have hBv := Interval.valid_of_contains hB
  have hPv := Interval.valid_of_contains hP
  have hAv := Interval.valid_of_contains hA
  have hCv := Interval.valid_of_contains hC
  have hS := real_scale_pos.le
  have hmr : (m:ℝ) ≤ (scale:ℝ) := by
    have hm : (m:ℤ) ≤ (scale.toNat:ℤ) := by exact_mod_cast (inverse_root_tick_caps hn hN).2
    rw [Int.toNat_of_nonneg scale_pos.le] at hm
    exact_mod_cast hm
  have hm₀ : 0 ≤ (m:ℝ) := by positivity
  obtain ⟨hpA,hpD⟩ := power_box_caps (normalizedLogBox_sound hn hN)
    (log_box_caps hn hN).1 (log_box_caps hn hN).2 k
  have hpD₀ : 0 ≤ (p.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr hPv
  have hcD₀ : 0 ≤ (c.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr hCv
  have hbA : (b.absTicks:ℝ) = (m:ℝ)+1 := by exact_mod_cast (inverse_box_caps n).1
  have hbD : (b.widthTicks:ℝ) = 1 := by exact_mod_cast (inverse_box_caps n).2
  have hcA : (c.absTicks:ℝ) ≤ (scale:ℝ) := by exact_mod_cast (factorial_box_caps k).1
  have hcD : (c.widthTicks:ℝ) ≤ 1 := by exact_mod_cast (factorial_box_caps k).2
  have haA : (a.absTicks:ℝ) ≤ (m:ℝ)+2 := by
    have h := Interval.mul_magnitude_bound hBv hPv
    rw [hbA] at h
    refine h.trans ((add_le_add (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpA (by positivity)) hS) (le_refl (1:ℝ))).trans_eq ?_)
    rw [mul_div_cancel_right₀ _ real_scale_pos.ne']
    ring
  have haD : a.widthTicks ≤ 19 := by
    apply int_le_of_real_lt_succ
    have h := Interval.mul_width_bound hBv hPv
    rw [hbA,hbD,mul_one] at h
    refine h.trans_lt ?_
    have hh := add_le_add (mul_le_mul (add_le_add_left hmr 1) hpD hpD₀ (by positivity)) hpA
    refine (add_le_add (div_le_div_of_nonneg_right hh hS) (le_refl (2:ℝ))).trans_lt ?_
    norm_num [scale]
  have haDr : (a.widthTicks:ℝ) ≤ 19 := by exact_mod_cast haD
  have haD₀ : 0 ≤ (a.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr hAv
  constructor
  · refine (Interval.mul_magnitude_bound hAv hCv).trans ?_
    have hcA₀ : 0 ≤ (c.absTicks:ℝ) := by exact_mod_cast (abs_nonneg c.lo).trans (le_max_left _ _)
    refine (add_le_add (div_le_div_of_nonneg_right
      (mul_le_mul haA hcA hcA₀ (by positivity)) hS) (le_refl (1:ℝ))).trans_eq ?_
    rw [mul_div_cancel_right₀ _ real_scale_pos.ne']
    ring
  · apply int_le_of_real_lt_succ
    refine (Interval.mul_width_bound hAv hCv).trans_lt ?_
    have hh₁ := mul_le_mul (haA.trans (add_le_add_left hmr 2)) hcD hcD₀ (by positivity)
    have hh₂ := mul_le_mul hcA haDr haD₀ hS
    refine (add_le_add (div_le_div_of_nonneg_right (add_le_add hh₁ hh₂) hS) (le_refl (2:ℝ))).trans_lt ?_
    norm_num [scale]

/-- A single kernel proof supplies the width premise for every norm and
degree used in the archived moment enclosures. -/
theorem dottie_uniform_moment_width {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) (k : ℕ) :
    10^12*momentWeightRadiusTicks n k ≤ (inverseSqrtTicks scale.toNat n:ℤ) := by
  let m := inverseSqrtTicks scale.toNat n
  let f : ℚ := 1/(k.factorial:ℚ)
  let a := ((inverseSqrtBox n).mul (Interval.power (normalizedLogBox n) k)).mul (Interval.rational f f)
  let p := momentPhaseBox n
  let b := a.scaleBy p
  have hp := momentPhaseBox_sound hn hN
  have hAr := Interval.mul_sound (Interval.mul_sound (inverseSqrtBox_sound hn)
    (Interval.power_sound (normalizedLogBox_sound hn hN) k))
    (show (Interval.rational f f).Contains (f:ℝ) from Interval.rational_sound le_rfl le_rfl)
  have hb := Rect.scale_sound hAr hp
  have haV := Interval.valid_of_contains hAr
  obtain ⟨haA,haD⟩ := moment_magnitude_caps hn hN k
  have haDr : (a.widthTicks:ℝ) ≤ 22 := by exact_mod_cast haD
  have haD₀ : 0 ≤ (a.widthTicks:ℝ) := by exact_mod_cast sub_nonneg.mpr haV
  have hpD₀ : 0 ≤ (p.widthTicks:ℝ) := by
    exact_mod_cast add_nonneg (sub_nonneg.mpr (Interval.valid_of_contains hp.1))
      (sub_nonneg.mpr (Interval.valid_of_contains hp.2))
  have hm₀ : 0 ≤ (m:ℝ) := by positivity
  have hS := real_scale_pos.le
  have hwidth : (b.widthTicks:ℝ) ≤ ((m:ℝ)+3)*15100000/(scale:ℝ)+70 := by
    refine (Rect.scale_width_bound haV (Interval.valid_of_contains hp.1) (Interval.valid_of_contains hp.2)).trans ?_
    have hr := mul_le_mul haA (dottie_uniform_phase_width n) hpD₀ (by positivity : 0 ≤ (m:ℝ)+3)
    have hi := mul_le_mul (dottie_uniform_phase_magnitude hn hN) haDr haD₀ (by positivity)
    refine (add_le_add (div_le_div_of_nonneg_right (add_le_add hr hi) hS) (le_refl (4:ℝ))).trans_eq ?_
    field_simp [real_scale_pos.ne']
    dsimp only [m]
    ring
  have hrad : (momentWeightRadiusTicks n k:ℝ) ≤ (b.widthTicks:ℝ) := by
    exact_mod_cast add_le_add (box_radius_le_width (Interval.valid_of_contains hb.1))
      (box_radius_le_width (Interval.valid_of_contains hb.2))
  have hNat := phaseWidth_budget_scalar.trans (Nat.mul_le_mul_left _ (inverse_root_tick_caps hn hN).1)
  have hbig : ((10^12*(3*15100000+70*scale.toNat):ℕ):ℝ) ≤
      (((scale.toNat-10^12*15100000)*m:ℕ):ℝ) := by exact_mod_cast hNat
  have hsc : (scale.toNat:ℝ) = (scale:ℝ) := by exact_mod_cast Int.toNat_of_nonneg scale_pos.le
  have hsub : 10^12*15100000 ≤ scale.toNat := by decide +kernel
  have hsubEq : ((scale.toNat-10^12*15100000:ℕ):ℝ) = (scale:ℝ)-(10:ℝ)^12*15100000 := by
    rw [Nat.cast_sub hsub, hsc]
    push_cast
    norm_num
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,hsc,hsubEq] at hbig
  have hfinal : (10^12:ℝ)*(((m:ℝ)+3)*15100000/(scale:ℝ)+70) ≤ (m:ℝ) := by
    apply (mul_le_mul_iff_of_pos_right real_scale_pos).1
    rw [mul_assoc,add_mul,div_mul_cancel₀ _ real_scale_pos.ne']
    nlinarith only [hbig]
  have hr := (mul_le_mul_of_nonneg_left (hrad.trans hwidth) (by norm_num : (0:ℝ) ≤ 10^12)).trans hfinal
  exact_mod_cast hr

theorem archivedMomentBox_of_uniform_scores {N k : ℕ} {r i : ℤ} {target : Rect}
    (hN : N ≤ dottiePrefixEnd)
    (hr : dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) 0 N.sqrt = r)
    (hi : dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) 0 N.sqrt = i)
    (hfit : (momentScoreRect r i k (8/10^8)).fits target = true) :
    target.Contains (signedMoment archivedLatticeCoeff N dottieSharpCenter k) :=
  archivedMomentBox_of_scores hN
    (fun n hn hnN => dottie_uniform_moment_width (n := n) hn (hnN.trans hN) k) hr hi hfit

#print axioms dottie_uniform_moment_width
#print axioms archivedMomentBox_of_uniform_scores

end QuarticModel.DottieFixedIntervals
