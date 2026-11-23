import DottieSharpArcCaps
import DottieSharpFactoredProjection

/-! Rational acceptance and coverage for the factored sharp-circle reading. -/

namespace QuarticModel

open SuperZeta.StirlingCorrection
set_option autoImplicit false

structure DottieSharpFactoredArc where
  lo : ℚ
  hi : ℚ
  lowerTicks : ℤ

def dottieSharpFactoredArcCover (arcs : List DottieSharpFactoredArc) : Bool :=
  dottieSharpArcCover 0 (arcs.map fun a => ⟨a.lo,a.hi,0,0,0⟩)

def dottieSharpFactoredArcPass (a : DottieSharpFactoredArc) : Bool :=
  decide (19037*dottieSharpArcScale ≤ 100*a.lowerTicks)

theorem dottie_sharp_margin_of_factored_arc_bounds (arcs : List DottieSharpFactoredArc) (refTicks : ℤ)
    (hcover : dottieSharpFactoredArcCover arcs = true)
    (hpass : arcs.all dottieSharpFactoredArcPass = true)
    (href : dottieRelativeReferenceProjection ≤ (refTicks : ℝ)/(dottieSharpArcScale : ℝ))
    (hreading : ∀ a ∈ arcs, ∀ t : ℝ, t ∈ Set.Ioc (a.lo : ℝ) (a.hi : ℝ) →
      dottieSharpFactoredUpper (dottieSharpPointAtTurn t) ≤
        -((a.lowerTicks : ℝ)/(dottieSharpArcScale : ℝ)) *
          ((refTicks : ℝ)/(dottieSharpArcScale : ℝ))) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  intro w hw
  apply dottie_sharp_margin_of_factored_projection hw
  have himage : circleMap (archivedRightCenter dottieHeight) (31/2048) ''
      Set.Ioc (0 : ℝ) (2*Real.pi) =
      Metric.sphere (archivedRightCenter dottieHeight) (31/2048) := by
    rw [image_circleMap_Ioc,abs_of_nonneg (by norm_num)]
  have ⟨θ,hθ,he⟩ : w ∈ circleMap (archivedRightCenter dottieHeight) (31/2048) ''
      Set.Ioc (0 : ℝ) (2*Real.pi) := himage ▸ hw
  let t := θ/(2*Real.pi)
  have ht : t ∈ Set.Ioc ((0 : ℚ) : ℝ) 1 :=
    ⟨by simpa only [Rat.cast_zero] using div_pos hθ.1 Real.two_pi_pos,
      (div_le_one Real.two_pi_pos).2 hθ.2⟩
  unfold dottieSharpFactoredArcCover at hcover
  obtain ⟨b,hb,hbt⟩ := dottie_sharp_arc_cover_sound hcover ht
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  have hscalar : (19037 : ℤ)*dottieSharpArcScale ≤ 100*a.lowerTicks :=
    of_decide_eq_true (List.all_eq_true.mp hpass a ha)
  have hscalar' : (19037:ℝ)*(dottieSharpArcScale : ℝ) ≤ 100*(a.lowerTicks : ℝ) :=
    by exact_mod_cast hscalar
  have hS : (0:ℝ) < (dottieSharpArcScale : ℝ) := by norm_num [dottieSharpArcScale]
  have hm : (190.37 : ℝ) ≤ (a.lowerTicks : ℝ)/(dottieSharpArcScale : ℝ) :=
    (le_div_iff₀ hS).2 (by linarith only [hscalar'])
  have hprod : 190.37*dottieRelativeReferenceProjection ≤
      ((a.lowerTicks : ℝ)/(dottieSharpArcScale : ℝ))*((refTicks : ℝ)/(dottieSharpArcScale : ℝ)) :=
    mul_le_mul hm href (abs_nonneg _) (by linarith only [hm])
  have hangle : 2*Real.pi*t = θ := by
    dsimp only [t]
    rw [mul_comm,div_mul_cancel₀ _ Real.two_pi_pos.ne']
  have hpoint : dottieSharpPointAtTurn t = w := by
    unfold dottieSharpPointAtTurn
    rwa [hangle]
  rw [← hpoint]
  exact (hreading a ha t hbt).trans (by linarith only [hprod])

#print axioms dottie_sharp_margin_of_factored_arc_bounds

end QuarticModel
