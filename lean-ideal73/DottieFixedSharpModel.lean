import DottieFixedSharpEvaluation

/-! Assemble the exact dyadic predicates for the sharp-circle model. Only
the original signed moment enclosures enter as analytic data inputs. -/

namespace QuarticModel.DottieFixedIntervals

open Complex SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private dottie_reference_taylor_error from DottieCompletedReferencePhase
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem shiftBox_sound : shiftBox.Contains (1/512) := Interval.rational_sound (by norm_num) (by norm_num)

theorem slopeBox_sound : slopeBox.Contains dottieSharpExponentSlope :=
  ⟨Interval.rational_sound (by norm_num [dottieSharpExponentSlope]) (by norm_num [dottieSharpExponentSlope]),
    Interval.rational_sound (by norm_num [dottieSharpExponentSlope]) (by norm_num [dottieSharpExponentSlope])⟩

theorem reflectedBoxHorner_sound {vb : Rect} {xs : Interval} {v : ℂ} {x : ℝ}
    (hv : vb.Contains v) (hx : xs.Contains (x*x)) (n : ℕ) (f : ℕ → Rect) (g : ℕ → ℂ)
    (hf : ∀ k < n, (f k).Contains (g k)) :
    let b := reflectedBoxHorner vb xs n f
    let p := dottieReflectedHorner v (x:ℂ) n g
    b.1.Contains p.1 ∧ b.2.Contains p.2 := by
  induction n generalizing f g with
  | zero => exact ⟨Rect.zero_sound,Rect.zero_sound⟩
  | succ n ih =>
    have h := ih (fun k => f (k+1)) (fun k => g (k+1)) (fun k hk => hf (k+1) (by omega))
    have hx' := Rect.scale_sound hx h.2
    have h₀ := Rect.add_sound (Rect.add_sound (hf 0 (by omega)) (Rect.mul_sound hv h.1)) hx'
    have h₁ := Rect.add_sound h.1 (Rect.mul_sound hv h.2)
    exact ⟨by simpa only [reflectedBoxHorner,dottieReflectedHorner,Complex.ofReal_mul,pow_two] using h₀,h₁⟩

theorem referenceProjectionBox_sound {reference : ℕ → Rect}
    (hRef : ∀ k < 17, (reference k).Contains
      (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k)) :
    (referenceProjectionBox reference).Contains
      (dottieSharpReferenceUnit * signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re := by
  have hz := imaginaryBox_sound (Interval.neg_sound shiftBox_sound)
  have h := Rect.horner_sound hz 17 reference
    (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter) hRef
  have h' : ((imaginaryBox shiftBox.neg).horner 17 reference).Contains dottieReferenceTaylorPolynomial := by
    simpa only [dottieReferenceTaylorPolynomial,dottieSharpCenter,Complex.ofReal_neg,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_ofNat] using h
  have hp := Rect.pad_sound h' (e := (3:ℚ)/10^30) (by push_cast; exact dottie_reference_taylor_error.le)
  exact (Rect.mul_sound circleUnitBox_sound hp).1

theorem fixedReferenceUpper_sound {reference : ℕ → Rect}
    (hRef : ∀ k < 17, (reference k).Contains
      (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k)) :
    dottieRelativeReferenceProjection ≤ (fixedReferenceUpper reference : ℝ)/(scale : ℝ) :=
  (le_div_iff₀ real_scale_pos).2 (Interval.absTicks_sound (referenceProjectionBox_sound hRef))

private theorem factoredHorizontal_pos {xb : Interval} {x : ℝ}
    (hx : xb.Contains x) (hpositive : 0 < (xb.add xb).lo) : 0 < x := by
  have hLo : 0 < ((xb.add xb).lo:ℝ) := by exact_mod_cast hpositive
  have h := pos_of_mul_pos_left (hLo.trans_le (Interval.add_sound hx hx).1) real_scale_pos.le
  linarith only [h]

private theorem factoredVerticalShift (w : ℂ) :
    w.im-dottieReferencePoint.im-1/512 = w.im-dottieHeight := by
  have h : dottieReferencePoint.im = dottieHeight-1/512 := by
    norm_num [dottieReferencePoint,Complex.mul_im]
  rw [h]
  ring

private abbrev factoredPairBox (sharp : ℕ → Rect) (xb yb : Interval) : Rect × Rect :=
  reflectedBoxHorner (imaginaryBox (yb.sub shiftBox)) (xb.mul xb) 17 sharp

private noncomputable abbrev factoredPair (w : ℂ) : ℂ × ℂ :=
  dottieReflectedHorner (((w.im-dottieHeight:ℝ):ℂ)*I) ((w.re-1/2:ℝ):ℂ) 17
    (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter)

private theorem factoredPairBox_sound {sharp : ℕ → Rect} {xb yb : Interval} {w : ℂ}
    (hSharp : ∀ k < 17, (sharp k).Contains
      (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k))
    (hx : xb.Contains (w.re-1/2)) (hy : yb.Contains (w.im-dottieReferencePoint.im)) :
    (factoredPairBox sharp xb yb).1.Contains (factoredPair w).1 ∧
      (factoredPairBox sharp xb yb).2.Contains (factoredPair w).2 := by
  have hIm := Interval.sub_sound hy shiftBox_sound
  rw [factoredVerticalShift w] at hIm
  exact reflectedBoxHorner_sound (imaginaryBox_sound hIm)
    (Interval.mul_sound hx hx) 17 sharp _ hSharp

private abbrev factoredProjectionBox (p : Rect × Rect) (xb yb : Interval) : Interval :=
  let z := xb.scaleBy slopeBox
  ((circleUnitBox.mul ((slopeBox.mul (imaginaryBox yb)).expBox)).mul
    ((z.coshBox.mul p.2).add ((slopeBox.dividedSinhBox z).mul p.1))).im

private theorem factoredProjectionBox_sound {p : Rect × Rect} {xb yb : Interval} {w : ℂ}
    (ha : p.1.Contains (factoredPair w).1) (hb : p.2.Contains (factoredPair w).2)
    (hx : xb.Contains (w.re-1/2)) (hy : yb.Contains (w.im-dottieReferencePoint.im))
    (hxPos : 0 < w.re-1/2)
    (hHyperbolic : (xb.scaleBy slopeBox).normUpperTicks ≤ 2*scale)
    (hExponential : (slopeBox.mul (imaginaryBox yb)).normUpperTicks ≤ 2*scale) :
    (factoredProjectionBox p xb yb).Contains (dottieSharpFactoredProjection w) := by
  let x := ((w.re-1/2:ℝ):ℂ)
  let y := ((w.im-dottieReferencePoint.im:ℝ):ℂ)*I
  let c := dottieSharpExponentSlope
  have hz := Rect.scale_sound hx slopeBox_sound
  have hc := Rect.coshBox_sound hz hHyperbolic
  have hs := Rect.dividedSinhBox_sound slopeBox_sound hz (ofReal_ne_zero.mpr hxPos.ne')
    (by decide +kernel) hHyperbolic
  have he := Rect.expBox_sound (Rect.mul_sound slopeBox_sound (imaginaryBox_sound hy)) hExponential
  have h := Rect.mul_sound (Rect.mul_sound circleUnitBox_sound he)
    (Rect.add_sound (Rect.mul_sound hc hb) (Rect.mul_sound hs ha))
  change (factoredProjectionBox p xb yb).Contains
    (dottieSharpReferenceUnit * (exp (y*c)*
      (cosh (x*c)*(factoredPair w).2+(sinh (x*c)/x)*(factoredPair w).1))).im
  rw [mul_comm y c, ← mul_assoc]
  exact h.2

private abbrev factoredMassBox (p : Rect × Rect) (xb : Interval) : Interval :=
  let odd := xb.scaleBy p.2
  ⟨0,(p.1.add odd).normUpperTicks+(p.1.sub odd).normUpperTicks⟩

private noncomputable def factoredMass (w : ℂ) : ℝ :=
  ‖dottieSharpMomentsPolynomial w‖ + ‖dottieSharpMomentsPolynomial (1-conj w)‖

private theorem factoredMassBox_generic {p : Rect × Rect} {xb : Interval}
    {a b : ℂ} {x : ℝ} (ha : p.1.Contains a) (hb : p.2.Contains b) (hx : xb.Contains x) :
    (factoredMassBox p xb).Contains (‖a+(x:ℂ)*b‖ + ‖a-(x:ℂ)*b‖) := by
  have hOdd := Rect.scale_sound hx hb
  have hPos := Rect.normUpperTicks_sound (Rect.add_sound ha hOdd)
  have hNeg := Rect.normUpperTicks_sound (Rect.sub_sound ha hOdd)
  refine ⟨?_,?_⟩
  · change (↑(0:ℤ):ℝ) ≤ (‖a+(x:ℂ)*b‖ + ‖a-(x:ℂ)*b‖)*(scale:ℝ)
    rw [Int.cast_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) real_scale_pos.le
  · simpa only [factoredMassBox,Int.cast_add,add_mul] using add_le_add hPos hNeg

private theorem factoredMassBox_of_polynomials {p : Rect × Rect} {xb : Interval}
    {v z₁ z₂ : ℂ} {x : ℝ} {n : ℕ} {f : ℕ → ℂ}
    (h₁ : z₁ = v + (x : ℂ)) (h₂ : z₂ = v - (x : ℂ))
    (ha : p.1.Contains (dottieReflectedHorner v (x:ℂ) n f).1)
    (hb : p.2.Contains (dottieReflectedHorner v (x:ℂ) n f).2) (hx : xb.Contains x) :
    (factoredMassBox p xb).Contains
      (‖∑ k ∈ Finset.range n, f k*z₁^k‖ + ‖∑ k ∈ Finset.range n, f k*z₂^k‖) := by
  rw [h₁, h₂]
  obtain ⟨hp, hn⟩ := dottie_reflected_horner_spec v (x:ℂ) n f
  rw [hp, hn]
  exact factoredMassBox_generic ha hb hx

private theorem factoredMassBox_sound {p : Rect × Rect} {xb : Interval} {w : ℂ}
    (ha : p.1.Contains (factoredPair w).1) (hb : p.2.Contains (factoredPair w).2)
    (hx : xb.Contains (w.re-1/2)) : (factoredMassBox p xb).Contains (factoredMass w) := by
  let x : ℝ := w.re-1/2
  let v := ((w.im-dottieHeight:ℝ):ℂ)*I
  have h₁ : w-dottieSharpCenter = v+(x:ℂ) := by
    apply Complex.ext <;> norm_num [x,v,dottieSharpCenter,Complex.mul_im,Complex.mul_re]
  have h₂ : (1-conj w)-dottieSharpCenter = v-(x:ℂ) := by
    apply Complex.ext <;> norm_num [x,v,dottieSharpCenter,Complex.mul_im,Complex.mul_re]
    ring
  exact factoredMassBox_of_polynomials h₁ h₂ ha hb hx

private abbrev factoredTailBox (mass xb : Interval) : Interval :=
  (((Interval.rational (18/10^12) (18/10^12)).mul mass).add
    (Interval.rational (18/10^11) (18/10^11))).mul ((xb.add xb).inv)

private theorem factoredTailBox_sound {mass xb : Interval} {m x : ℝ}
    (hm : mass.Contains m) (hx : xb.Contains x) (hpositive : 0 < (xb.add xb).lo) :
    (factoredTailBox mass xb).Contains (((18/10^12)*m+18/10^11)/(2*x)) := by
  have h₁ : (Interval.rational (18/10^12) (18/10^12)).Contains (18/10^12) :=
    Interval.rational_sound (by norm_num) (by norm_num)
  have h₂ : (Interval.rational (18/10^11) (18/10^11)).Contains (18/10^11) :=
    Interval.rational_sound (by norm_num) (by norm_num)
  rw [div_eq_mul_inv,two_mul]
  exact Interval.mul_sound (Interval.add_sound (Interval.mul_sound h₁ hm) h₂)
    (Interval.inv_sound (Interval.add_sound hx hx) hpositive)

theorem fixedFactoredReading_sound {sharp : ℕ → Rect} {xb yb : Interval} {w : ℂ}
    (hSharp : ∀ k < 17, (sharp k).Contains
      (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k))
    (hx : xb.Contains (w.re-1/2)) (hy : yb.Contains (w.im-dottieReferencePoint.im))
    (hpositive : 0 < (xb.add xb).lo)
    (hHyperbolic : (xb.scaleBy slopeBox).normUpperTicks ≤ 2*scale)
    (hExponential : (slopeBox.mul (imaginaryBox yb)).normUpperTicks ≤ 2*scale) :
    (fixedFactoredReading sharp xb yb).Contains (dottieSharpFactoredUpper w) := by
  obtain ⟨ha,hb⟩ := factoredPairBox_sound hSharp hx hy
  have hProjection := factoredProjectionBox_sound ha hb hx hy
    (factoredHorizontal_pos hx hpositive) hHyperbolic hExponential
  have hMass := factoredMassBox_sound ha hb hx
  have hTail := factoredTailBox_sound hMass hx hpositive
  exact Interval.add_sound hProjection hTail

theorem fixedArcPass_sound {sharp : ℕ → Rect} {refTicks : ℤ} {a : DottieSharpFactoredArc} {t : ℝ}
    (hpass : fixedArcPass sharp refTicks a = true)
    (hSharp : ∀ k < 17, (sharp k).Contains
      (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k))
    (ht : t ∈ Set.Ioc (a.lo:ℝ) (a.hi:ℝ)) :
    dottieSharpFactoredUpper (dottieSharpPointAtTurn t) ≤
      -((a.lowerTicks:ℝ)/(dottieSharpArcScale:ℝ))*((refTicks:ℝ)/(dottieSharpArcScale:ℝ)) := by
  simp only [fixedArcPass,decide_eq_true_eq] at hpass
  obtain ⟨hq,hlo,hhi,hL,hU,hx₀,hH,hE,hbound⟩ := hpass
  have hTrig := circleTrigBox_sound (fixedArcQuadrant a) hq hlo hhi ⟨ht.1.le,ht.2⟩ hL hU
  obtain ⟨hx,hy⟩ := circleXYBox_sound hTrig
  have hb := (fixedFactoredReading_sound hSharp hx hy hx₀ hH hE).2
  have hb' := mul_le_mul_of_nonneg_right hb real_scale_pos.le
  have hcast : ((fixedFactoredReading sharp (circleXBox (circleTrigBox (fixedArcQuadrant a) a.lo a.hi))
      (circleYBox (circleTrigBox (fixedArcQuadrant a) a.lo a.hi))).hi : ℝ)*(scale:ℝ) ≤
      -(a.lowerTicks:ℝ)*(refTicks:ℝ) := by exact_mod_cast hbound
  have hs : (scale:ℝ) = (dottieSharpArcScale:ℝ) := rfl
  rw [← hs]
  apply (mul_le_mul_iff_of_pos_right real_scale_pos).mp
  apply (mul_le_mul_iff_of_pos_right real_scale_pos).mp
  refine (hb'.trans hcast).trans_eq ?_
  field_simp [real_scale_pos.ne']

theorem sharp_margin_of_fixed_moment_rectangles (sharp reference : ℕ → Rect)
    (arcs : List DottieSharpFactoredArc) (hCover : dottieSharpFactoredArcCover arcs = true)
    (hScalar : arcs.all dottieSharpFactoredArcPass = true)
    (hChecked : arcs.all (fixedArcPass sharp (fixedReferenceUpper reference)) = true)
    (hSharp : ∀ k < 17, (sharp k).Contains
      (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k))
    (hRef : ∀ k < 17, (reference k).Contains
      (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_margin_of_factored_arc_bounds arcs (fixedReferenceUpper reference) hCover hScalar
  · exact fixedReferenceUpper_sound hRef
  · intro a ha t ht
    exact fixedArcPass_sound (List.all_eq_true.mp hChecked a ha) hSharp ht

#print axioms referenceProjectionBox_sound
#print axioms fixedFactoredReading_sound
#print axioms fixedArcPass_sound
#print axioms sharp_margin_of_fixed_moment_rectangles

end QuarticModel.DottieFixedIntervals
