import DottieSharpRelativeCircle

/-! Check scalar margins and exact angular coverage from rational caps.
The cap inputs connect separately to the original reflected model. -/

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open scoped ComplexConjugate
set_option autoImplicit false

/-- Turn endpoints and upward-rounded bounds in units of 2⁻⁶⁴. -/
structure DottieSharpArcCaps where
  lo : ℚ
  hi : ℚ
  xTicks : ℤ
  projectionTicks : ℤ
  normTicks : ℤ

def dottieSharpArcScale : ℤ := 18446744073709551616

def dottieSharpArcPass (refTicks : ℤ) (a : DottieSharpArcCaps) : Bool :=
  decide (0 ≤ a.xTicks ∧ 0 ≤ refTicks ∧ 0 ≤ a.normTicks ∧
    100*10^11*dottieSharpArcScale*a.projectionTicks +
      100*dottieSharpArcScale*a.normTicks + 2*19037*10^11*a.xTicks*refTicks ≤ 0)

def dottieSharpArcCover : ℚ → List DottieSharpArcCaps → Bool
  | cursor, [] => decide (cursor = 1)
  | cursor, a::as =>
    decide (a.lo = cursor ∧ a.lo < a.hi) && dottieSharpArcCover a.hi as

theorem dottie_sharp_arc_cover_sound {arcs : List DottieSharpArcCaps} {cursor : ℚ}
    (h : dottieSharpArcCover cursor arcs = true) {t : ℝ}
    (ht : t ∈ Set.Ioc (cursor : ℝ) 1) :
    ∃ a ∈ arcs, t ∈ Set.Ioc (a.lo : ℝ) (a.hi : ℝ) := by
  induction arcs generalizing cursor with
  | nil =>
    have he : cursor = 1 := of_decide_eq_true h
    simp [he] at ht
  | cons a as ih =>
    simp only [dottieSharpArcCover,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨ha,_⟩,hrest⟩ := h
    by_cases ht_hi : t ≤ (a.hi : ℝ)
    · exact ⟨a,List.mem_cons_self,by rw [ha]; exact ⟨ht.1,ht_hi⟩⟩
    · obtain ⟨b,hb,hmem⟩ := ih hrest ⟨lt_of_not_ge ht_hi,ht.2⟩
      exact ⟨b,List.mem_cons_of_mem _ hb,hmem⟩

noncomputable def dottieSharpPointAtTurn (t : ℝ) : ℂ :=
  circleMap (archivedRightCenter dottieHeight) (31/2048) (2*Real.pi*t)

def DottieSharpArcCapsAt (a : DottieSharpArcCaps) (w : ℂ) : Prop :=
  w.re-1/2 ≤ (a.xTicks : ℝ)/(dottieSharpArcScale : ℝ) ∧
  dottieRelativeSharpModelIm w ≤ (a.projectionTicks : ℝ)/(dottieSharpArcScale : ℝ) ∧
  ‖dottieSharpRelativeFactor w‖+‖dottieSharpRelativeFactor (1-conj w)‖ ≤
    (a.normTicks : ℝ)/(dottieSharpArcScale : ℝ)

theorem dottie_sharp_arc_pass_sound {refTicks : ℤ} {a : DottieSharpArcCaps} {w : ℂ}
    (h : dottieSharpArcPass refTicks a = true) (ha : DottieSharpArcCapsAt a w)
    (hr : dottieRelativeReferenceProjection ≤ (refTicks : ℝ)/(dottieSharpArcScale : ℝ)) :
    dottieRelativeSharpModelIm w +
        (‖dottieSharpRelativeFactor w‖+‖dottieSharpRelativeFactor (1-conj w)‖)/10^11 ≤
      -(2*190.37*(w.re-1/2)*dottieRelativeReferenceProjection) := by
  simp only [dottieSharpArcPass,decide_eq_true_eq] at h
  obtain ⟨hx₀,_,_,hc⟩ := h
  obtain ⟨hx,hp,hn⟩ := ha
  let S : ℝ := dottieSharpArcScale
  let X : ℝ := (a.xTicks : ℝ)/S
  let Y : ℝ := (a.projectionTicks : ℝ)/S
  let N : ℝ := (a.normTicks : ℝ)/S
  let R : ℝ := (refTicks : ℝ)/S
  have hS : 0 < S := by norm_num [S,dottieSharpArcScale]
  have hXR : (w.re-1/2)*dottieRelativeReferenceProjection ≤ X*R :=
    mul_le_mul hx hr (abs_nonneg _) (div_nonneg (by exact_mod_cast hx₀) hS.le)
  have hscalar : Y+N/10^11 ≤ -(2*190.37*X*R) := by
    have hc' : (100 : ℝ)*10^11*S*(a.projectionTicks : ℝ) +
        100*S*(a.normTicks : ℝ) + 2*19037*10^11*(a.xTicks : ℝ)*(refTicks : ℝ) ≤ 0 := by
      dsimp only [S]
      exact_mod_cast hc
    have hScale : S = 18446744073709551616 := by norm_num [S,dottieSharpArcScale]
    dsimp only [X,Y,N,R]
    rw [hScale] at hc' ⊢
    linarith only [hc']
  calc
    _ ≤ Y+N/10^11 := add_le_add hp (div_le_div_of_nonneg_right hn (by norm_num))
    _ ≤ _ := hscalar
    _ ≤ _ := by linarith only [hXR]

/-- A passing rational cover and valid caps on its arcs give the original
sharp-circle margin, including the Taylor error on both reflected sides. -/
theorem dottie_sharp_margin_of_checked_arc_caps (arcs : List DottieSharpArcCaps) (refTicks : ℤ)
    (hcover : dottieSharpArcCover 0 arcs = true)
    (hpass : arcs.all (dottieSharpArcPass refTicks) = true)
    (href : dottieRelativeReferenceProjection ≤ (refTicks : ℝ)/(dottieSharpArcScale : ℝ))
    (hcaps : ∀ a ∈ arcs, ∀ t : ℝ, t ∈ Set.Ioc (a.lo : ℝ) (a.hi : ℝ) →
      DottieSharpArcCapsAt a (dottieSharpPointAtTurn t)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_sphere_margin_of_angle_model
  intro θ hθ
  let t := θ/(2*Real.pi)
  have hp := Real.two_pi_pos
  have ht : t ∈ Set.Ioc ((0 : ℚ) : ℝ) 1 := by
    exact ⟨by simpa only [Rat.cast_zero] using div_pos hθ.1 hp,(div_le_one hp).2 hθ.2⟩
  obtain ⟨a,ha,hm⟩ := dottie_sharp_arc_cover_sound hcover ht
  have h := dottie_sharp_arc_pass_sound (List.all_eq_true.mp hpass a ha) (hcaps a ha t hm) href
  have he : 2*Real.pi*t = θ := by
    dsimp only [t]
    rw [mul_comm,div_mul_cancel₀ _ hp.ne']
  simpa only [dottieSharpPointAtTurn,he] using h

#print axioms dottie_sharp_arc_cover_sound
#print axioms dottie_sharp_arc_pass_sound
#print axioms dottie_sharp_margin_of_checked_arc_caps

end QuarticModel
