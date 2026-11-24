import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! Signed dyadic intervals for the Dottie contour replay. Computable
endpoints are integers in units of `2⁻⁶⁴`, with outward rounding. -/

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false

def scale : ℤ := 18446744073709551616

theorem scale_pos : 0 < scale := by decide +kernel

theorem real_scale_pos : 0 < (scale : ℝ) := by exact_mod_cast scale_pos

private def ceilDiv (a b : ℤ) : ℤ := -((-a)/b)

private theorem floor_div_lower (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ((a/b : ℤ) : ℝ) ≤ (a : ℝ)/(b : ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hb : 0 < (b : ℝ))).2
  exact_mod_cast (Int.ediv_mul_le a hb.ne')

private theorem ceil_div_upper (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a : ℝ)/(b : ℝ) ≤ (ceilDiv a b : ℝ) := by
  have h := neg_le_neg (floor_div_lower (-a) hb)
  simpa only [ceilDiv,Int.cast_neg,neg_div,neg_neg] using h

structure Interval where
  lo : ℤ
  hi : ℤ
  deriving Inhabited

def Interval.Contains (b : Interval) (x : ℝ) : Prop :=
  (b.lo : ℝ) ≤ x*(scale : ℝ) ∧ x*(scale : ℝ) ≤ (b.hi : ℝ)

def Interval.rational (lo hi : ℚ) : Interval :=
  ⟨⌊lo*(scale : ℚ)⌋,⌈hi*(scale : ℚ)⌉⟩

theorem Interval.rational_sound {lo hi : ℚ} {x : ℝ} (hl : (lo : ℝ) ≤ x) (hh : x ≤ (hi : ℝ)) :
    (Interval.rational lo hi).Contains x := by
  have h₁ := Int.floor_le (((lo*(scale : ℚ)) : ℚ) : ℝ)
  have h₂ := Int.le_ceil (((hi*(scale : ℚ)) : ℚ) : ℝ)
  rw [Rat.floor_cast] at h₁
  rw [Rat.ceil_cast] at h₂
  push_cast at h₁ h₂
  exact ⟨h₁.trans (mul_le_mul_of_nonneg_right hl real_scale_pos.le),
    (mul_le_mul_of_nonneg_right hh real_scale_pos.le).trans h₂⟩

def Interval.add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩

def Interval.neg (a : Interval) : Interval := ⟨-a.hi,-a.lo⟩

def Interval.sub (a b : Interval) : Interval := a.add b.neg

theorem Interval.add_sound {a b : Interval} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.add b).Contains (x+y) := by
  simpa only [Interval.Contains,Interval.add,Int.cast_add,add_mul] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem Interval.neg_sound {a : Interval} {x : ℝ} (hx : a.Contains x) : (a.neg).Contains (-x) := by
  simpa only [Interval.Contains,Interval.neg,Int.cast_neg,neg_mul] using
    And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem Interval.sub_sound {a b : Interval} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.sub b).Contains (x-y) := by
  simpa only [Interval.sub,sub_eq_add_neg] using Interval.add_sound hx (Interval.neg_sound hy)

def Interval.mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))/scale,
    ceilDiv (max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))) scale⟩

private theorem endpoint_products {a b x : ℝ} (y : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (a*y) (b*y) ≤ x*y ∧ x*y ≤ max (a*y) (b*y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hy),
      (mul_le_mul_of_nonneg_right hb hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb (le_of_not_ge hy)),
      (mul_le_mul_of_nonpos_right ha (le_of_not_ge hy)).trans (le_max_left _ _)⟩

private theorem corner_products {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b)
    (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hy₁ : min (a*c) (a*d) ≤ a*y ∧ a*y ≤ max (a*c) (a*d) :=
    by simpa only [mul_comm a] using endpoint_products a hc hd
  have hy₂ : min (b*c) (b*d) ≤ b*y ∧ b*y ≤ max (b*c) (b*d) :=
    by simpa only [mul_comm b] using endpoint_products b hc hd
  obtain ⟨h₁,h₂⟩ := endpoint_products y ha hb
  exact ⟨(le_min ((min_le_left _ _).trans hy₁.1) ((min_le_right _ _).trans hy₂.1)).trans h₁,
    h₂.trans (max_le (hy₁.2.trans (le_max_left _ _)) (hy₂.2.trans (le_max_right _ _)))⟩

theorem Interval.mul_sound {a b : Interval} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (a.mul b).Contains (x*y) := by
  let l := min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
  let u := max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
  obtain ⟨hl,hu⟩ := corner_products hx.1 hx.2 hy.1 hy.2
  have hl' : (l : ℝ) ≤ (x*(scale : ℝ))*(y*(scale : ℝ)) := by
    simpa only [l,Int.cast_min,Int.cast_mul] using hl
  have hu' : (x*(scale : ℝ))*(y*(scale : ℝ)) ≤ (u : ℝ) := by
    simpa only [u,Int.cast_max,Int.cast_mul] using hu
  have he : (x*(scale : ℝ))*(y*(scale : ℝ))/(scale : ℝ) = (x*y)*(scale : ℝ) := by
    field_simp [real_scale_pos.ne']
  refine ⟨?_,?_⟩
  · change ((l/scale : ℤ) : ℝ) ≤ _
    exact (floor_div_lower l scale_pos).trans
      ((div_le_div_of_nonneg_right hl' real_scale_pos.le).trans_eq he)
  · change _ ≤ (ceilDiv u scale : ℝ)
    rw [← he]
    exact (div_le_div_of_nonneg_right hu' real_scale_pos.le).trans (ceil_div_upper u scale_pos)

def Interval.inv (a : Interval) : Interval := ⟨scale^2/a.hi,ceilDiv (scale^2) a.lo⟩

theorem Interval.inv_sound {a : Interval} {x : ℝ} (hx : a.Contains x) (ha : 0 < a.lo) :
    a.inv.Contains x⁻¹ := by
  have hal : 0 < (a.lo : ℝ) := by exact_mod_cast ha
  have hxp : 0 < x*(scale : ℝ) := hal.trans_le hx.1
  have hax : 0 < x := pos_of_mul_pos_left hxp real_scale_pos.le
  have hau : 0 < a.hi := by exact_mod_cast (hxp.trans_le hx.2)
  have he : ((scale : ℝ)^2)/(x*(scale : ℝ)) = x⁻¹*(scale : ℝ) := by
    field_simp [hax.ne',real_scale_pos.ne']
  have hn : (0:ℝ) ≤ ((scale^2:ℤ):ℝ) := by exact_mod_cast (sq_nonneg scale)
  have h₁ := (floor_div_lower (scale^2) hau).trans
    (div_le_div_of_nonneg_left hn hxp hx.2)
  have h₂ := (div_le_div_of_nonneg_left hn hal hx.1).trans
    (ceil_div_upper (scale^2) ha)
  exact ⟨by simpa only [Interval.inv,Int.cast_pow,he] using h₁,
    by simpa only [Interval.inv,Int.cast_pow,he] using h₂⟩

def Interval.absTicks (a : Interval) : ℤ := max |a.lo| |a.hi|

theorem Interval.absTicks_sound {a : Interval} {x : ℝ} (hx : a.Contains x) :
    |x| * (scale : ℝ) ≤ (a.absTicks : ℝ) := by
  rw [← abs_of_pos real_scale_pos,← abs_mul]
  apply abs_le.mpr
  simp only [Interval.absTicks,Int.cast_max,Int.cast_abs]
  exact ⟨(neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le (a.lo : ℝ)).trans hx.1),
    hx.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

structure Rect where
  re : Interval
  im : Interval
  deriving Inhabited

def Rect.Contains (b : Rect) (z : ℂ) : Prop := b.re.Contains z.re ∧ b.im.Contains z.im

def Rect.zero : Rect := ⟨⟨0,0⟩,⟨0,0⟩⟩
theorem Rect.zero_sound : Rect.zero.Contains 0 := by simp [Rect.Contains,Rect.zero,Interval.Contains]

def Rect.rationalReal (v : ℚ) : Rect := ⟨Interval.rational v v,⟨0,0⟩⟩

theorem Rect.rationalReal_sound (v : ℚ) : (Rect.rationalReal v).Contains (v : ℝ) :=
  ⟨Interval.rational_sound le_rfl le_rfl,by simp [Rect.rationalReal,Interval.Contains]⟩

def Rect.add (a b : Rect) : Rect := ⟨a.re.add b.re,a.im.add b.im⟩
def Rect.neg (a : Rect) : Rect := ⟨a.re.neg,a.im.neg⟩
def Rect.sub (a b : Rect) : Rect := a.add b.neg
def Rect.mul (a b : Rect) : Rect := ⟨(a.re.mul b.re).sub (a.im.mul b.im),
  (a.re.mul b.im).add (a.im.mul b.re)⟩
def Interval.scaleBy (a : Interval) (b : Rect) : Rect := ⟨a.mul b.re,a.mul b.im⟩

theorem Rect.add_sound {a b : Rect} {z w : ℂ} (hz : a.Contains z) (hw : b.Contains w) :
    (a.add b).Contains (z+w) := ⟨Interval.add_sound hz.1 hw.1,Interval.add_sound hz.2 hw.2⟩

theorem Rect.neg_sound {a : Rect} {z : ℂ} (hz : a.Contains z) : (a.neg).Contains (-z) :=
  ⟨Interval.neg_sound hz.1,Interval.neg_sound hz.2⟩

theorem Rect.sub_sound {a b : Rect} {z w : ℂ} (hz : a.Contains z) (hw : b.Contains w) :
    (a.sub b).Contains (z-w) := by
  simpa only [Rect.sub,sub_eq_add_neg] using Rect.add_sound hz (Rect.neg_sound hw)

theorem Rect.mul_sound {a b : Rect} {z w : ℂ} (hz : a.Contains z) (hw : b.Contains w) :
    (a.mul b).Contains (z*w) :=
  ⟨Interval.sub_sound (Interval.mul_sound hz.1 hw.1) (Interval.mul_sound hz.2 hw.2),
    Interval.add_sound (Interval.mul_sound hz.1 hw.2) (Interval.mul_sound hz.2 hw.1)⟩

theorem Rect.scale_sound {a : Interval} {b : Rect} {x : ℝ} {z : ℂ}
    (hx : a.Contains x) (hz : b.Contains z) : (a.scaleBy b).Contains ((x : ℂ)*z) := by
  refine ⟨?_,?_⟩
  · simpa only [Interval.scaleBy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      using Interval.mul_sound hx hz.1
  · simpa only [Interval.scaleBy,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using Interval.mul_sound hx hz.2

def Rect.normUpperTicks (a : Rect) : ℤ := a.re.absTicks+a.im.absTicks

theorem Rect.normUpperTicks_sound {a : Rect} {z : ℂ} (hz : a.Contains z) :
    ‖z‖*(scale : ℝ) ≤ (a.normUpperTicks : ℝ) := by
  refine (mul_le_mul_of_nonneg_right (Complex.norm_le_abs_re_add_abs_im z) real_scale_pos.le).trans ?_
  simp only [add_mul,Rect.normUpperTicks,Int.cast_add]
  exact add_le_add (Interval.absTicks_sound hz.1) (Interval.absTicks_sound hz.2)

def Rect.pad (a : Rect) (e : ℚ) : Rect :=
  let error := Interval.rational (-e) e
  a.add ⟨error,error⟩

theorem Rect.pad_sound {a : Rect} {z w : ℂ} {e : ℚ} (hz : a.Contains z)
    (he : ‖w-z‖ ≤ (e : ℝ)) : (a.pad e).Contains w := by
  have hr := abs_le.mp ((Complex.abs_re_le_norm (w-z)).trans he)
  have hi := abs_le.mp ((Complex.abs_im_le_norm (w-z)).trans he)
  have h : (⟨Interval.rational (-e) e,Interval.rational (-e) e⟩ : Rect).Contains (w-z) :=
    ⟨Interval.rational_sound (by simpa only [Rat.cast_neg] using hr.1) hr.2,
      Interval.rational_sound (by simpa only [Rat.cast_neg] using hi.1) hi.2⟩
  have heq : z+(w-z) = w := by ring
  rw [← heq]
  exact Rect.add_sound hz h

#print axioms Interval.mul_sound
#print axioms Interval.inv_sound
#print axioms Rect.mul_sound
#print axioms Rect.pad_sound

end QuarticModel.DottieFixedIntervals
