import DottieSharpReferenceProjection

namespace QuarticModel.DottieFixedIntervals

open Complex Finset SuperZeta.StirlingCorrection
open private signedTerm from DottieSignedMoments
open private dottie_reference_taylor_error from DottieCompletedReferencePhase
open private dottie_sharp_reference_factor_ne_zero from DottieSharpRelativeCircle

set_option autoImplicit false

private theorem projectedDirichlet_eq_cosine_sum (a : ℕ → ℤ) (N : ℕ) (t phase : ℝ) :
    (Complex.exp ((phase : ℂ) * I) * signedDirichletPolynomial a N
      (1 / 2 + (t : ℂ) * I)).re =
    ∑ j ∈ range N,
      ((a (j + 1) : ℝ) / Real.sqrt (j + 1)) * Real.cos (phase - t * Real.log (j + 1)) := by
  unfold signedDirichletPolynomial
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  let l : ℝ := Real.log (j + 1)
  have he : (phase : ℂ) * I + (l : ℂ) * -(1 / 2 + (t : ℂ) * I) =
      ((-l / 2 : ℝ) : ℂ) + ((phase - t * l : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hn : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  unfold signedTerm
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.natCast_log, mul_left_comm, ← Complex.exp_add]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [he, Complex.exp_add]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Real.cos_zero, Real.sin_zero, mul_one,
    mul_zero, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, Complex.I_re,
    Complex.I_im, sub_zero, zero_mul, add_zero, Real.exp_zero, one_mul, Complex.intCast_re,
    Complex.intCast_im]
  have hr : Real.exp (-l / 2) = 1 / Real.sqrt (j + 1) := by
    have hj : 0 < (j + 1 : ℝ) := by positivity
    rw [show -l / 2 = Real.log (j + 1) * (-(1 / 2) : ℝ) by dsimp [l]; ring,
      ← Real.rpow_def_of_pos hj, Real.rpow_neg hj.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hr]
  ring

/-- The actual projected reference value in real cosine form at the original height. -/
theorem dottie_reference_projection_eq_cosine_sum :
    dottieRelativeReferenceProjection =
      |∑ j ∈ range 276824064,
        ((archivedLatticeCoeff (j + 1) : ℝ) / Real.sqrt (j + 1)) *
          Real.cos (Complex.arg (dottieSharpFactor dottieReferencePoint) -
            (dottieHeight - 1 / 512) * Real.log (j + 1))| := by
  have hunit : dottieSharpReferenceUnit =
      Complex.exp ((Complex.arg (dottieSharpFactor dottieReferencePoint) : ℂ) * I) := by
    unfold dottieSharpReferenceUnit dottieSharpReferenceAmplitude
    apply (div_eq_iff (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr dottie_sharp_reference_factor_ne_zero))).2
    rw [mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I _).symm
  unfold dottieRelativeReferenceProjection
  rw [hunit, dottieReferencePoint, projectedDirichlet_eq_cosine_sum]

private def referenceTurnLo : ℚ := 624352696635798 / 10^15

private def referenceTurnHi : ℚ := 624353175692177 / 10^15

private def referenceEndpointUnitBox : Rect := circleTrigBox 2 referenceTurnLo referenceTurnHi

private theorem referenceEndpointUnitBox_sound :
    referenceEndpointUnitBox.Contains dottieSharpReferenceUnit := by
  obtain ⟨phase, hlo, hhi, he⟩ := dottie_sharp_reference_unit_phase_interval
  let t := phase / (2 * Real.pi)
  have ht : t ∈ Set.Icc (referenceTurnLo : ℝ) (referenceTurnHi : ℝ) := by
    constructor
    · apply (le_div_iff₀ Real.two_pi_pos).2
      norm_num [referenceTurnLo]
      linarith only [hlo, Real.pi_lt_d20]
    · apply (div_le_iff₀ Real.two_pi_pos).2
      norm_num [referenceTurnHi]
      linarith only [hhi, Real.pi_gt_d20]
  have hbox := circleTrigBox_sound 2 (lo := referenceTurnLo) (hi := referenceTurnHi) (t := t)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) ht
    (by decide +kernel) (by decide +kernel)
  have hphase : 2 * Real.pi * t = phase := by
    dsimp only [t]
    rw [mul_comm, div_mul_cancel₀ _ Real.two_pi_pos.ne']
  rw [hphase] at hbox
  rw [he]
  exact hbox

/-- The first six archived moment balls, padded by (2/10^7) after division
by (32^k). The later degrees use the checked mass and logarithm bounds. -/
def decimalReferenceMomentBox (k : ℕ) : Rect :=
  if k < 6 then ([
  ⟨⟨14912503316050249521, 14912510694747879006⟩, ⟨19146400482459098575, 19146407861156728060⟩⟩,
  ⟨⟨-5651959922210916136, -5651723803886772651⟩, ⟨-192351034805787161032, -192350798687463017547⟩⟩,
  ⟨⟨107005562083592875256, 107013117869965466691⟩, ⟨1343997155772330564515, 1344004711558703155950⟩⟩,
  ⟨⟨-1236646852122536569793, -1236405066958613643956⟩, ⟨-7026651529081595873287, -7026409743917672947450⟩⟩,
  ⟨⟨8504254812155526577273, 8511991937401060203994⟩, ⟨29323961389295574312552, 29331698514541107939273⟩⟩,
  ⟨⟨-41133616384764283077937, -40886028376907207022956⟩, ⟨-101160047292118229077417, -100912459284261153022436⟩⟩
  ] : List Rect).getD k Rect.zero else tailMomentBox 33276 20 k

private def decimalReferenceProjectionBox : Interval :=
  let P := ((imaginaryBox shiftBox.neg).horner 17 decimalReferenceMomentBox).pad (3 / 10^30)
  (referenceEndpointUnitBox.mul P).re

/-- With the six supplied moment enclosures, the direct reference value is
at most 0.1716868. The unit is bounded at the angle endpoints. -/
theorem dottie_reference_projection_le_decimal_of_moments
    (hmom : ∀ k < 6, (decimalReferenceMomentBox k).Contains
      (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k)) :
    dottieRelativeReferenceProjection ≤ 1716868 / 10^7 := by
  have hmoment (k : ℕ) (hk : k < 17) :
      (decimalReferenceMomentBox k).Contains
        (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k) := by
    by_cases h : k < 6
    · exact hmom k h
    · simpa only [decimalReferenceMomentBox, if_neg h] using referenceTailMomentBox_sound k
  have hz := imaginaryBox_sound (Interval.neg_sound shiftBox_sound)
  have h := Rect.horner_sound hz 17 decimalReferenceMomentBox
    (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter) hmoment
  have hpoly : ((imaginaryBox shiftBox.neg).horner 17 decimalReferenceMomentBox).Contains
      dottieReferenceTaylorPolynomial := by
    simpa only [dottieReferenceTaylorPolynomial, dottieSharpCenter, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h
  have hp := Rect.pad_sound hpoly (e := (3 : ℚ) / 10^30)
    (by push_cast; exact dottie_reference_taylor_error.le)
  have hbox := (Rect.mul_sound referenceEndpointUnitBox_sound hp).1
  have hproj : dottieRelativeReferenceProjection ≤
      (decimalReferenceProjectionBox.absTicks : ℝ) / scale :=
    (le_div_iff₀ real_scale_pos).2 (Interval.absTicks_sound hbox)
  have hticks : (10^7 : ℤ) * decimalReferenceProjectionBox.absTicks ≤ 1716868 * scale := by
    decide +kernel
  have hreal : (10^7 : ℝ) * (decimalReferenceProjectionBox.absTicks : ℝ) ≤ 1716868 * scale := by
    exact_mod_cast hticks
  refine hproj.trans ((div_le_iff₀ real_scale_pos).2 ?_)
  have hpos : (0 : ℝ) < 10^7 := by norm_num
  have hb := (le_div_iff₀ hpos).2 (by simpa only [mul_comm] using hreal :
    (decimalReferenceProjectionBox.absTicks : ℝ) * 10^7 ≤ 1716868 * scale)
  exact hb.trans_eq (by ring)

/-- The same decimal bound can be supplied by scores for the six archived moments. -/
theorem dottie_reference_projection_le_decimal_of_scores
    (href : ∀ k < 6, (archivedScoredMomentBox 276824064 k).fits
      (decimalReferenceMomentBox k) = true) :
    dottieRelativeReferenceProjection ≤ 1716868 / 10^7 := by
  apply dottie_reference_projection_le_decimal_of_moments
  intro k hk
  exact archivedMomentBox_of_uniform_scores (N := 276824064) (by decide +kernel) rfl rfl (href k hk)

/-- The original sharp-circle check accepts the exact decimal 0.171687. -/
theorem dottie_sharp_margin_of_decimal_reference
    (hsharp : ∀ k < 11, (archivedScoredMomentBox dottiePrefixEnd k).fits (fixedSharpInput k) = true)
    (href : dottieRelativeReferenceProjection ≤ 171687 / 10^6) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048),
      (dottieSharpPrefix w).im ≤ -(190.37 * ((w.re - 1 / 2) * dottieCircleReference)) :=
  dottie_sharp_margin_of_reference_projection hsharp
    (href.trans (by norm_num [fixedReferenceTicks, dottieSharpArcScale]))

#print axioms dottie_reference_projection_eq_cosine_sum
#print axioms dottie_reference_projection_le_decimal_of_moments
#print axioms dottie_reference_projection_le_decimal_of_scores
#print axioms dottie_sharp_margin_of_decimal_reference

end QuarticModel.DottieFixedIntervals
