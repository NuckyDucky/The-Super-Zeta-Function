import DottieFixedIntervals

/-! Bounds on the width added by the fixed-point operations. These let a
single error bound cover the weights for all norms at a given cutoff. -/

namespace QuarticModel.DottieFixedIntervals

open private ceilDiv floor_div_lower ceil_div_upper from DottieFixedIntervals
set_option autoImplicit false

def Interval.widthTicks (a : Interval) : ℤ := a.hi-a.lo

private theorem floor_div_loss (a : ℤ) :
    (a:ℝ)/(scale:ℝ)-1 ≤ ((a/scale:ℤ):ℝ) := by
  have hr := Int.emod_lt_of_pos a scale_pos
  have he := Int.ediv_mul_add_emod a scale
  have hr' : ((a%scale:ℤ):ℝ) < (scale:ℝ) := by exact_mod_cast hr
  have he' : ((a/scale:ℤ):ℝ)*(scale:ℝ)+((a%scale:ℤ):ℝ) = (a:ℝ) := by
    exact_mod_cast he
  rw [sub_le_iff_le_add]
  apply (div_le_iff₀ real_scale_pos).2
  rw [add_mul,one_mul]
  linarith only [he',hr']

private theorem ceil_div_loss (a : ℤ) :
    (ceilDiv a scale:ℝ) ≤ (a:ℝ)/(scale:ℝ)+1 := by
  have h := neg_le_neg (floor_div_loss (-a))
  simp only [ceilDiv, Int.cast_neg, neg_div, neg_sub] at h ⊢
  linarith only [h]

private def productLo (a b : Interval) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))

private def productHi (a b : Interval) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))

private theorem abs_mem_bound {a : Interval} {x : ℤ} (hx : x ∈ Set.Icc a.lo a.hi) :
    |x| ≤ a.absTicks := by
  have h₀ : -a.absTicks ≤ a.lo :=
    (neg_le_neg (le_max_left |a.lo| |a.hi|)).trans (neg_abs_le a.lo)
  have h₁ : a.hi ≤ a.absTicks := (le_abs_self a.hi).trans (le_max_right |a.lo| |a.hi|)
  exact abs_le.mpr ⟨h₀.trans hx.1,hx.2.trans h₁⟩

private theorem abs_difference_bound {a : Interval} {x y : ℤ}
    (hx : x ∈ Set.Icc a.lo a.hi) (hy : y ∈ Set.Icc a.lo a.hi) :
    |x-y| ≤ a.widthTicks := by
  obtain ⟨hxl,hxh⟩ := hx
  obtain ⟨hyl,hyh⟩ := hy
  apply abs_le.mpr
  unfold Interval.widthTicks
  constructor <;> omega

private theorem difference_of_products_bound {a b : Interval} {x x' y y' : ℤ}
    (hx : x ∈ Set.Icc a.lo a.hi) (hx' : x' ∈ Set.Icc a.lo a.hi)
    (hy : y ∈ Set.Icc b.lo b.hi) (hy' : y' ∈ Set.Icc b.lo b.hi) :
    x*y ≤ x'*y' + (a.absTicks*b.widthTicks+b.absTicks*a.widthTicks) := by
  apply (sub_le_iff_le_add').1
  rw [show x*y-x'*y' = x*(y-y')+(x-x')*y' by ring]
  have ha := abs_mem_bound hx
  have hb := abs_mem_bound hy'
  have hda := abs_difference_bound hx hx'
  have hdb := abs_difference_bound hy hy'
  calc
    _ ≤ |x*(y-y')+(x-x')*y'| := le_abs_self _
    _ ≤ |x*(y-y')| + |(x-x')*y'| := abs_add_le _ _
    _ = |x| * |y-y'| + |y'| * |x-x'| := by rw [abs_mul, abs_mul, mul_comm |x-x'|]
    _ ≤ _ := add_le_add
      (mul_le_mul ha hdb (abs_nonneg _) ((abs_nonneg _).trans ha))
      (mul_le_mul hb hda (abs_nonneg _) ((abs_nonneg _).trans hb))

private theorem product_diameter_bound {a b : Interval} (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    productHi a b-productLo a b ≤ a.absTicks*b.widthTicks+b.absTicks*a.widthTicks := by
  apply (sub_le_iff_le_add').2
  simp only [productHi,productLo,← min_add_add_right,max_le_iff,le_min_iff]
  repeat' constructor
  all_goals apply difference_of_products_bound <;> simp [Set.mem_Icc,ha,hb]

private theorem product_magnitude_bound {a b : Interval} (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    -(a.absTicks*b.absTicks) ≤ productLo a b ∧ productHi a b ≤ a.absTicks*b.absTicks := by
  have h (x y : ℤ) (hx : x ∈ Set.Icc a.lo a.hi) (hy : y ∈ Set.Icc b.lo b.hi) :
      |x*y| ≤ a.absTicks*b.absTicks := by
    rw [abs_mul]
    exact mul_le_mul (abs_mem_bound hx) (abs_mem_bound hy) (abs_nonneg _)
      ((abs_nonneg _).trans (abs_mem_bound hx))
  constructor
  · simp only [productLo,le_min_iff]
    repeat' constructor
    all_goals exact (abs_le.mp (h _ _ (by simp [Set.mem_Icc,ha]) (by simp [Set.mem_Icc,hb]))).1
  · simp only [productHi,max_le_iff]
    repeat' constructor
    all_goals exact (abs_le.mp (h _ _ (by simp [Set.mem_Icc,ha]) (by simp [Set.mem_Icc,hb]))).2

private theorem productLo_le_productHi (a b : Interval) : productLo a b ≤ productHi a b := by
  unfold productLo productHi
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans
    ((le_max_left _ _).trans (le_max_left _ _))

theorem Interval.mul_width_bound {a b : Interval} (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    ((a.mul b).widthTicks:ℝ) ≤
      ((a.absTicks:ℝ)*(b.widthTicks:ℝ)+(b.absTicks:ℝ)*(a.widthTicks:ℝ))/(scale:ℝ)+2 := by
  let l := productLo a b
  let u := productHi a b
  have h := product_diameter_bound ha hb
  change (u-l:ℤ) ≤ _ at h
  have h' : (u:ℝ)-(l:ℝ) ≤
      (a.absTicks:ℝ)*(b.widthTicks:ℝ)+(b.absTicks:ℝ)*(a.widthTicks:ℝ) := by exact_mod_cast h
  have h₁ := floor_div_loss l
  have h₂ := ceil_div_loss u
  have h₃ := div_le_div_of_nonneg_right h' real_scale_pos.le
  rw [sub_div] at h₃
  change ((ceilDiv u scale-(l/scale):ℤ):ℝ) ≤ _
  push_cast
  linarith only [h₁,h₂,h₃]

theorem Interval.mul_magnitude_bound {a b : Interval} (ha : a.lo ≤ a.hi) (hb : b.lo ≤ b.hi) :
    ((a.mul b).absTicks:ℝ) ≤ (a.absTicks:ℝ)*(b.absTicks:ℝ)/(scale:ℝ)+1 := by
  let l := productLo a b
  let u := productHi a b
  let cap := (a.absTicks:ℝ)*(b.absTicks:ℝ)/(scale:ℝ)
  obtain ⟨hl,hu⟩ := product_magnitude_bound ha hb
  have hl' : -(a.absTicks:ℝ)*(b.absTicks:ℝ) ≤ (l:ℝ) := by
    rw [neg_mul]
    exact_mod_cast hl
  have hu' : (u:ℝ) ≤ (a.absTicks:ℝ)*(b.absTicks:ℝ) := by exact_mod_cast hu
  have hlu : (l:ℝ) ≤ (u:ℝ) := by exact_mod_cast productLo_le_productHi a b
  have hL : -cap ≤ (l:ℝ)/(scale:ℝ) := by
    rw [show -cap = (-(a.absTicks:ℝ)*(b.absTicks:ℝ))/(scale:ℝ) by unfold cap; ring]
    exact div_le_div_of_nonneg_right hl' real_scale_pos.le
  have hU : (u:ℝ)/(scale:ℝ) ≤ cap := div_le_div_of_nonneg_right hu' real_scale_pos.le
  have hLU := div_le_div_of_nonneg_right hlu real_scale_pos.le
  have h₁ := floor_div_lower l scale_pos
  have h₂ := floor_div_loss l
  have h₃ := ceil_div_upper u scale_pos
  have h₄ := ceil_div_loss u
  change ((max |l/scale| |ceilDiv u scale|:ℤ):ℝ) ≤ cap+1
  push_cast
  exact max_le (abs_le.mpr ⟨by linarith only [hL,h₂],by linarith only [h₁,hLU,hU]⟩)
    (abs_le.mpr ⟨by linarith only [hL,hLU,h₃],by linarith only [h₄,hU]⟩)

theorem Interval.width_add (a b : Interval) : (a.add b).widthTicks = a.widthTicks+b.widthTicks := by
  unfold Interval.add Interval.widthTicks
  simp
  ring

theorem Interval.width_sub (a b : Interval) : (a.sub b).widthTicks = a.widthTicks+b.widthTicks := by
  unfold Interval.sub Interval.neg Interval.add Interval.widthTicks
  simp
  ring

theorem Interval.width_neg (a : Interval) : a.neg.widthTicks = a.widthTicks := by
  simp [Interval.neg, Interval.widthTicks, sub_eq_add_neg, add_comm]

theorem Interval.absTicks_neg (a : Interval) : a.neg.absTicks = a.absTicks := by
  simp only [Interval.neg,Interval.absTicks,abs_neg,max_comm]

theorem Interval.absTicks_add_le (a b : Interval) : (a.add b).absTicks ≤ a.absTicks+b.absTicks := by
  apply max_le
  · exact (abs_add_le a.lo b.lo).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_add_le a.hi b.hi).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem Interval.valid_of_contains {a : Interval} {x : ℝ} (h : a.Contains x) : a.lo ≤ a.hi := by
  exact_mod_cast h.1.trans h.2

theorem Interval.rational_width_lt (lo hi : ℚ) :
    ((Interval.rational lo hi).widthTicks:ℝ) < ((hi:ℝ)-(lo:ℝ))*(scale:ℝ)+2 := by
  have hLow := Int.lt_floor_add_one ((lo*(scale:ℚ):ℚ):ℝ)
  have hHigh := Int.ceil_lt_add_one ((hi*(scale:ℚ):ℚ):ℝ)
  rw [Rat.floor_cast] at hLow
  rw [Rat.ceil_cast] at hHigh
  unfold Interval.rational Interval.widthTicks
  push_cast at hLow hHigh ⊢
  rw [sub_mul]
  linarith only [hLow,hHigh]

theorem Interval.rational_point_width_le_one (v : ℚ) :
    (Interval.rational v v).widthTicks ≤ 1 :=
  sub_le_iff_le_add'.2 (Int.ceil_le_floor_add_one (v*(scale:ℚ)))

theorem Interval.rational_abs_le {lo hi : ℚ} {B : ℝ}
    (hl : |(lo:ℝ)| ≤ B) (hh : |(hi:ℝ)| ≤ B) :
    ((Interval.rational lo hi).absTicks:ℝ) ≤ B*(scale:ℝ)+1 := by
  let L := lo*(scale:ℚ)
  let H := hi*(scale:ℚ)
  have h₁ := Int.floor_le (L:ℝ)
  have h₂ := Int.lt_floor_add_one (L:ℝ)
  have h₃ := Int.le_ceil (H:ℝ)
  have h₄ := Int.ceil_lt_add_one (H:ℝ)
  rw [Rat.floor_cast] at h₁ h₂
  rw [Rat.ceil_cast] at h₃ h₄
  have low₀ : -(B*(scale:ℝ)) ≤ (L:ℝ) := by
    push_cast [L]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (abs_le.mp hl).1 real_scale_pos.le
  have low₁ : (L:ℝ) ≤ B*(scale:ℝ) := by
    push_cast [L]
    exact mul_le_mul_of_nonneg_right (abs_le.mp hl).2 real_scale_pos.le
  have high₀ : -(B*(scale:ℝ)) ≤ (H:ℝ) := by
    push_cast [H]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (abs_le.mp hh).1 real_scale_pos.le
  have high₁ : (H:ℝ) ≤ B*(scale:ℝ) := by
    push_cast [H]
    exact mul_le_mul_of_nonneg_right (abs_le.mp hh).2 real_scale_pos.le
  change ((max |⌊L⌋| |⌈H⌉|:ℤ):ℝ) ≤ _
  push_cast
  exact max_le (abs_le.mpr ⟨by linarith only [h₂,low₀],by linarith only [h₁,low₁]⟩)
    (abs_le.mpr ⟨by linarith only [h₃,high₀],by linarith only [h₄,high₁]⟩)

theorem Interval.rational_nonnegative_point_abs {v : ℚ} (h : 0 ≤ v) :
    (Interval.rational v v).absTicks = ⌈v*(scale:ℚ)⌉ := by
  have hS : (0:ℚ) ≤ (scale:ℚ) := by exact_mod_cast scale_pos.le
  have hf := Int.floor_nonneg.mpr (mul_nonneg h hS)
  have hc := Int.floor_le_ceil (v*(scale:ℚ))
  change max |⌊v*(scale:ℚ)⌋| |⌈v*(scale:ℚ)⌉| = _
  rw [abs_of_nonneg hf,abs_of_nonneg (hf.trans hc),max_eq_right hc]

theorem Interval.absTicks_le_of_contains {a : Interval} {x : ℝ}
    (hx : a.Contains x) : (a.absTicks:ℝ) ≤ |x| * (scale:ℝ)+(a.widthTicks:ℝ) := by
  have hxl := hx.1
  have hxh := hx.2
  have hlow : -(|x| * (scale:ℝ)) ≤ x*(scale:ℝ) := by
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le x) real_scale_pos.le
  have hhigh := mul_le_mul_of_nonneg_right (le_abs_self x) real_scale_pos.le
  unfold Interval.absTicks Interval.widthTicks
  push_cast
  exact max_le (abs_le.mpr ⟨by linarith only [hxh,hlow],by linarith only [hxl,hxh,hhigh]⟩)
    (abs_le.mpr ⟨by linarith only [hxl,hxh,hlow],by linarith only [hxl,hhigh]⟩)

def Rect.widthTicks (r : Rect) : ℤ := r.re.widthTicks + r.im.widthTicks

theorem Rect.width_add (a b : Rect) : (a.add b).widthTicks = a.widthTicks+b.widthTicks := by
  simp only [Rect.widthTicks,Rect.add,Interval.width_add]
  ring

theorem Rect.normUpperTicks_add_le (a b : Rect) : (a.add b).normUpperTicks ≤ a.normUpperTicks+b.normUpperTicks := by
  refine (add_le_add (Interval.absTicks_add_le a.re b.re) (Interval.absTicks_add_le a.im b.im)).trans_eq ?_
  unfold Rect.normUpperTicks
  ring

theorem Rect.pad_width (b : Rect) (e : ℚ) :
    (b.pad e).widthTicks = b.widthTicks+4*⌈e*(scale:ℚ)⌉ := by
  unfold Rect.pad
  rw [Rect.width_add]
  simp only [Rect.widthTicks,Interval.rational,Interval.widthTicks,neg_mul,Int.floor_neg]
  ring

theorem Rect.pad_magnitude {b : Rect} {e : ℚ} (he : 0 ≤ e) :
    (b.pad e).normUpperTicks ≤ b.normUpperTicks+2*⌈e*(scale:ℚ)⌉ := by
  have hs : (0:ℚ) ≤ (scale:ℚ) := by exact_mod_cast scale_pos.le
  have hp := Int.ceil_nonneg (mul_nonneg he hs)
  unfold Rect.pad
  refine (Rect.normUpperTicks_add_le _ _).trans_eq ?_
  simp only [Rect.normUpperTicks,Interval.absTicks,Interval.rational,neg_mul,Int.floor_neg,
    abs_neg,abs_of_nonneg hp,max_self,two_mul]

theorem Rect.absTicks_le_of_contains {a : Rect} {z : ℂ} (hz : a.Contains z) :
    (a.normUpperTicks:ℝ) ≤ (|z.re| + |z.im|)*(scale:ℝ)+(a.widthTicks:ℝ) := by
  simp only [Rect.normUpperTicks,Rect.widthTicks,Int.cast_add]
  exact (add_le_add (Interval.absTicks_le_of_contains hz.1) (Interval.absTicks_le_of_contains hz.2)).trans_eq (by ring)

theorem Rect.mul_width_bound {a b : Rect} (har : a.re.lo ≤ a.re.hi) (hai : a.im.lo ≤ a.im.hi)
    (hbr : b.re.lo ≤ b.re.hi) (hbi : b.im.lo ≤ b.im.hi) :
    ((a.mul b).widthTicks:ℝ) ≤
      ((a.normUpperTicks:ℝ)*(b.widthTicks:ℝ)+(b.normUpperTicks:ℝ)*(a.widthTicks:ℝ))/(scale:ℝ)+8 := by
  simp only [Rect.mul,Rect.widthTicks,Interval.width_add,Interval.width_sub,
    Rect.normUpperTicks,Int.cast_add]
  refine (add_le_add (add_le_add (Interval.mul_width_bound har hbr) (Interval.mul_width_bound hai hbi))
    (add_le_add (Interval.mul_width_bound har hbi) (Interval.mul_width_bound hai hbr))).trans_eq ?_
  ring

theorem Rect.scale_width_bound {a : Interval} {b : Rect}
    (ha : a.lo ≤ a.hi) (hbr : b.re.lo ≤ b.re.hi) (hbi : b.im.lo ≤ b.im.hi) :
    ((a.scaleBy b).widthTicks:ℝ) ≤
      ((a.absTicks:ℝ)*(b.widthTicks:ℝ)+(b.normUpperTicks:ℝ)*(a.widthTicks:ℝ))/(scale:ℝ)+4 := by
  simp only [Interval.scaleBy,Rect.widthTicks,Rect.normUpperTicks,Int.cast_add]
  refine (add_le_add (Interval.mul_width_bound ha hbr) (Interval.mul_width_bound ha hbi)).trans_eq ?_
  ring

private theorem interval_zero_mul (a : Interval) : (⟨0,0⟩:Interval).mul a = ⟨0,0⟩ := by
  simp [Interval.mul,ceilDiv]

private theorem pure_imaginary_mul (a : Interval) (b : Rect) :
    (⟨⟨0,0⟩,a⟩:Rect).mul b = ⟨(a.mul b.im).neg,a.mul b.re⟩ := by
  simp only [Rect.mul,interval_zero_mul,Interval.sub,Interval.add,Interval.neg,zero_add]

theorem Rect.pure_imaginary_mul_caps {a : Interval} {b : Rect}
    (ha : a.lo ≤ a.hi) (hbr : b.re.lo ≤ b.re.hi) (hbi : b.im.lo ≤ b.im.hi) :
    (((⟨⟨0,0⟩,a⟩:Rect).mul b).normUpperTicks:ℝ) ≤
      (a.absTicks:ℝ)*(b.normUpperTicks:ℝ)/(scale:ℝ)+2 ∧
    (((⟨⟨0,0⟩,a⟩:Rect).mul b).widthTicks:ℝ) ≤
      ((a.absTicks:ℝ)*(b.widthTicks:ℝ)+(b.normUpperTicks:ℝ)*(a.widthTicks:ℝ))/(scale:ℝ)+4 := by
  rw [pure_imaginary_mul]
  constructor
  · simp only [Rect.normUpperTicks,Interval.absTicks_neg,Int.cast_add]
    refine (add_le_add (Interval.mul_magnitude_bound ha hbi) (Interval.mul_magnitude_bound ha hbr)).trans_eq ?_
    ring
  · simp only [Rect.widthTicks,Interval.width_neg,Int.cast_add,Rect.normUpperTicks]
    refine (add_le_add (Interval.mul_width_bound ha hbi) (Interval.mul_width_bound ha hbr)).trans_eq ?_
    ring

#print axioms Interval.mul_width_bound
#print axioms Interval.mul_magnitude_bound
#print axioms Rect.mul_width_bound
#print axioms Rect.pure_imaginary_mul_caps
#print axioms Interval.rational_width_lt
#print axioms Rect.pad_width
#print axioms Interval.rational_abs_le
#print axioms Rect.absTicks_le_of_contains

end QuarticModel.DottieFixedIntervals
