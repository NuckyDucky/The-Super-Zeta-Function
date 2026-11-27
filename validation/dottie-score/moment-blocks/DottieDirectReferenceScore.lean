import DottieDirectReference
import DottiePreciseReferencePhase
import DottieCachedLog

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open private quarticCosine cos_four quarticCosine_distance from DottieReferenceWeights
open private log_lt_twenty_two from DottiePreciseMomentHeight
open private dottie_pi_lower dottie_pi_upper from DottiePreciseHeight
open private projectedDirichlet_eq_cosine_sum from DottieDirectReference
open private reference_mass_le from DottieHeightPerturbation

set_option autoImplicit false
set_option maxHeartbeats 1250000

private def referencePhaseRat : ℚ := 3.92292489981824

private def referenceLog (n : ℕ) : ℚ := (dottieCachedLogLowerTicks n : ℚ) / 2^96

private def referenceAngleBeforeWrap (n : ℕ) : ℚ :=
  let l := referenceLog n
  let angle := -dottieMomentHeightRat * l
  let q := ⌊(angle + dottieMomentPiRat) / (2 * dottieMomentPiRat)⌋
  (angle - 2 * dottieMomentPiRat * q) + (referencePhaseRat + l / 512)

private theorem referenceAngleBeforeWrap_eq {n : ℕ} (hn : 0 < n) :
    referenceAngleBeforeWrap n =
      dottieMomentReducedAngle n + (referencePhaseRat + referenceLog n / 512) := by
  simp only [referenceAngleBeforeWrap, referenceLog, dottieCachedLogLowerTicks_eq n hn,
    dottieMomentReducedAngle, dottieMomentAngleTurn, dottieMomentAngle]

private def directReferenceAngle (n : ℕ) : ℚ :=
  let a := referenceAngleBeforeWrap n
  if a ≤ dottieMomentPiRat then a else a - 2 * dottieMomentPiRat

private theorem referenceLog_enclosure {n : ℕ} (hn : 0 < n) (hN : n ≤ 276824064) :
    0 ≤ (referenceLog n : ℝ) ∧
    (referenceLog n : ℝ) ≤ Real.log n ∧
    Real.log n - (referenceLog n : ℝ) ≤ 128 / (2 : ℝ)^96 := by
  have h := dottieCachedLogLowerTicks_spec n hn hN
  have hs : (0 : ℝ) < 2^96 := by positivity
  unfold referenceLog
  push_cast
  refine ⟨by positivity, (div_le_iff₀ hs).2 (by linarith only [h.1]), ?_⟩
  rw [sub_le_iff_le_add, ← add_div]
  exact (le_div_iff₀ hs).2 (by linarith only [h.2])

private theorem directReferenceAngle_bounds {n : ℕ} (hn : 0 < n) (hN : n ≤ 276824064) :
    -dottieMomentPiRat ≤ directReferenceAngle n ∧ directReferenceAngle n ≤ dottieMomentPiRat := by
  obtain ⟨hlo, hhi⟩ := dottie_moment_reduced_angle_bounds n
  obtain ⟨hl, huh, _⟩ := referenceLog_enclosure hn hN
  have hl' : 0 ≤ referenceLog n := by exact_mod_cast hl
  have hhi' : referenceLog n ≤ 22 := by
    exact_mod_cast huh.trans (log_lt_twenty_two hn (hN.trans (by decide +kernel))).le
  have hp : (3 : ℚ) ≤ dottieMomentPiRat := by norm_num [dottieMomentPiRat]
  have hphase : 0 ≤ referencePhaseRat ∧ referencePhaseRat ≤ 4 := by norm_num [referencePhaseRat]
  unfold directReferenceAngle
  dsimp only
  rw [referenceAngleBeforeWrap_eq hn]
  split
  · rename_i h
    exact ⟨by linarith only [hlo, hl', hphase.1], h⟩
  · rename_i h
    have ha := lt_of_not_ge h
    constructor <;> linarith only [ha, hhi, hhi', hp, hphase.2]

private noncomputable def unitPhase (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * I)

private theorem unitPhase_add_distance (a b c d : ℝ) :
    ‖unitPhase (a + b) - unitPhase (c + d)‖ ≤
      ‖unitPhase a - unitPhase c‖ + ‖unitPhase b - unitPhase d‖ := by
  have hadd (x y : ℝ) : unitPhase (x + y) = unitPhase x * unitPhase y := by
    unfold unitPhase
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have hnorm (x : ℝ) : ‖unitPhase x‖ = 1 := by
    simp [unitPhase, Complex.norm_exp, Complex.mul_re]
  rw [hadd, hadd, show unitPhase a * unitPhase b - unitPhase c * unitPhase d =
    (unitPhase a - unitPhase c) * unitPhase b + unitPhase c * (unitPhase b - unitPhase d) by ring]
  refine (norm_add_le _ _).trans_eq ?_
  rw [norm_mul, norm_mul, hnorm b, hnorm c, mul_one, one_mul]

private theorem cosine_distance_le_unitPhase (a b : ℝ) :
    |Real.cos a - Real.cos b| ≤ ‖unitPhase a - unitPhase b‖ := by
  simpa [unitPhase, Complex.sub_re, Complex.exp_re, Complex.mul_re, Complex.mul_im]
    using Complex.abs_re_le_norm (unitPhase a - unitPhase b)

private theorem directReferenceUnwrapped_error {n : ℕ} (hn : 0 < n) (hN : n ≤ 276824064)
    {phase : ℝ} (hphase : |phase - 3.92292489981824| ≤ 1 / (2 * 10^12)) :
    |Real.cos (phase - (dottieHeight - 1/512) * Real.log n) -
      Real.cos (referenceAngleBeforeWrap n : ℝ)| ≤ 7 / 10^13 := by
  let T := dottieMomentRationalHeight
  let l := Real.log (n : ℝ)
  let L : ℝ := referenceLog n
  let b := phase + (T - dottieHeight + 1/512) * l
  let d := (referencePhaseRat : ℝ) + L / 512
  obtain ⟨hL₀, hL₁, hL₂⟩ := referenceLog_enclosure hn hN
  have hl₀ : 0 ≤ l := hL₀.trans hL₁
  have hcap : n ≤ dottiePrefixEnd := hN.trans (by decide +kernel)
  have hl₁ : l ≤ 22 := (log_lt_twenty_two hn hcap).le
  have hT : |T - dottieHeight| ≤ 1/10^19 := by
    rw [abs_sub_comm]
    exact dottieMomentRationalHeight_error
  have hShift : |b - d| ≤ 6/10^13 := by
    have e : b - d = (phase - (referencePhaseRat : ℝ)) +
        ((T - dottieHeight) * l + (l - L) / 512) := by
      dsimp only [b, d]
      ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _) |>.trans ?_)
    rw [abs_mul, abs_of_nonneg hl₀, abs_div, abs_of_nonneg (sub_nonneg.mpr hL₁),
      abs_of_pos (by norm_num : (0 : ℝ) < 512)]
    have h1 := mul_le_mul hT hl₁ hl₀ (by norm_num)
    have h2 := div_le_div_of_nonneg_right hL₂ (by norm_num : (0 : ℝ) ≤ 512)
    have h3 : |phase - (referencePhaseRat : ℝ)| ≤ 1 / (2 * 10^12) := by
      norm_num [referencePhaseRat] at hphase ⊢
      exact hphase
    linarith only [h1, h2, h3]
  have hw := unitPhase_add_distance (-T*l) b (dottieMomentReducedAngle n : ℝ) d
  have h1 : ‖unitPhase (-T*l) - unitPhase (dottieMomentReducedAngle n : ℝ)‖ ≤ 1/10^13 := by
    simpa only [unitPhase, T, l, neg_mul] using dottie_moment_rational_phase_error n hn hcap
  have h2 : ‖unitPhase b - unitPhase d‖ ≤ 6/10^13 :=
    (dottie_unit_phase_distance b d).trans hShift
  have e : -T*l + b = phase - (dottieHeight - 1/512) * Real.log n := by
    dsimp only [b, l]
    ring
  have e' : (dottieMomentReducedAngle n : ℝ) + d = (referenceAngleBeforeWrap n : ℝ) := by
    simp [d, L, referenceAngleBeforeWrap_eq hn]
  rw [e, e'] at hw
  exact (cosine_distance_le_unitPhase _ _).trans
    (hw.trans ((add_le_add h1 h2).trans_eq (by norm_num)))

private theorem directReferenceWrap_error (n : ℕ) :
    |Real.cos (referenceAngleBeforeWrap n : ℝ) -
      Real.cos (directReferenceAngle n : ℝ)| ≤ 2/10^32 := by
  have hpi : |(dottieMomentPiRat : ℝ) - Real.pi| ≤ 1/10^32 := by
    apply abs_le.mpr
    norm_num [dottieMomentPiRat]
    constructor <;> linarith only [dottie_pi_lower, dottie_pi_upper]
  unfold directReferenceAngle
  dsimp only
  split
  · norm_num
  · push_cast
    let a : ℝ := referenceAngleBeforeWrap n
    change |Real.cos a - Real.cos (a - 2 * (dottieMomentPiRat : ℝ))| ≤ _
    calc
      _ = |Real.cos (a - 2*Real.pi) - Real.cos (a - 2*(dottieMomentPiRat : ℝ))| := by rw [Real.cos_sub_two_pi]
      _ ≤ |(a - 2*Real.pi) - (a - 2*(dottieMomentPiRat : ℝ))| :=
        (cosine_distance_le_unitPhase _ _).trans (dottie_unit_phase_distance _ _)
      _ ≤ 2/10^32 := by
        rw [show (a - 2*Real.pi) - (a - 2*(dottieMomentPiRat : ℝ)) =
          2*((dottieMomentPiRat : ℝ) - Real.pi) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact (mul_le_mul_of_nonneg_left hpi (by norm_num)).trans_eq (by ring)

private def directReferenceQuarter (n : ℕ) : ℚ := directReferenceAngle n / 4

private def directReferenceCosineTicks (n : ℕ) : ℤ :=
  let q := directReferenceQuarter n
  let c := (fixedCosBounds q.num q.den).1
  let scale := (fixedCosScale : ℤ)
  8*c^4 - 8*scale^2*c^2 + scale^4

private theorem directReferenceCosine_error {n : ℕ} (hn : 0 < n) (hN : n ≤ 276824064)
    {phase : ℝ} (hphase : |phase - 3.92292489981824| ≤ 1 / (2 * 10^12)) :
    |(directReferenceCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 -
      Real.cos (phase - (dottieHeight - 1/512) * Real.log n)| ≤ 8/10^12 := by
  let q := directReferenceQuarter n
  have hq : |q| ≤ 1 := by
    obtain ⟨hl, hh⟩ := directReferenceAngle_bounds hn hN
    have hpi : dottieMomentPiRat ≤ 4 := by norm_num [dottieMomentPiRat]
    exact abs_le.mpr ⟨by dsimp [q, directReferenceQuarter]; linarith only [hl, hpi],
      by dsimp [q, directReferenceQuarter]; linarith only [hh, hpi]⟩
  have hcast : (q : ℝ) = (q.num : ℝ)/q.den := Rat.cast_def q
  have hab : q.num.natAbs ≤ q.den := by
    have h : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
    rw [hcast, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q.den)] at h
    have hs : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have he := (div_le_one hs).mp h
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] at he
    exact_mod_cast he
  let c := ((fixedCosBounds q.num q.den).1 : ℝ)/fixedCosScale
  have hb := fixedCosBounds_spec q.num q.den q.den_pos hab
  rw [← hcast] at hb
  have hwidth := fixedCosBounds_width q.num q.den
  have hd : |c - Real.cos q| ≤ 6/2^48 := by
    dsimp only [c]
    exact abs_le.mpr ⟨by linarith only [hb.2, hwidth], by linarith only [hb.1]⟩
  have hc : |c| ≤ 2 := by
    calc
      |c| = |c - Real.cos q + Real.cos q| := by rw [sub_add_cancel]
      _ ≤ |c - Real.cos q| + |Real.cos q| := abs_add_le _ _
      _ ≤ 2 := by linarith only [hd, Real.abs_cos_le_one (q : ℝ)]
  have hqcos := quarticCosine_distance c (Real.cos q) hc
    ((Real.abs_cos_le_one (q : ℝ)).trans (by norm_num))
  have hre : (directReferenceCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 = quarticCosine c := by
    simp only [directReferenceCosineTicks, c, q, quarticCosine, Int.cast_sub, Int.cast_add,
      Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    field [show (fixedCosScale : ℝ) ≠ 0 by norm_num [fixedCosScale]]
  have h4 : 4 * (q : ℝ) = (directReferenceAngle n : ℝ) := by
    dsimp [q, directReferenceQuarter]
    push_cast
    ring
  rw [← cos_four, h4, ← hre] at hqcos
  have h0 := hqcos.trans (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 288))
  let x := (directReferenceCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4
  let y := Real.cos (directReferenceAngle n : ℝ)
  let z := Real.cos (referenceAngleBeforeWrap n : ℝ)
  let w := Real.cos (phase - (dottieHeight - 1/512) * Real.log n)
  change |x - w| ≤ _
  rw [show x - w = (x - y) + ((y - z) + (z - w)) by ring]
  have h1 : |y - z| ≤ 2/10^32 := by rw [abs_sub_comm]; exact directReferenceWrap_error n
  have h2 : |z - w| ≤ 7/10^13 := by
    rw [abs_sub_comm]
    exact directReferenceUnwrapped_error hn hN hphase
  exact (abs_add_le _ _).trans ((add_le_add h0
    ((abs_add_le _ _).trans (add_le_add h1 h2))).trans (by norm_num))

/-- One integer weight for the original projected reference reading. -/
def dottieDirectReferenceWeight (n : ℕ) : ℤ :=
  (inverseSqrtTicks (2^64) n : ℤ) * directReferenceCosineTicks n

def dottieDirectReferenceDenominator : ℕ := (2^64) * fixedCosScale^4

private theorem directReferenceWeight_error {n : ℕ} (hn : 0 < n) (hN : n ≤ 276824064)
    {phase : ℝ} (hphase : |phase - 3.92292489981824| ≤ 1 / (2 * 10^12)) :
    |(dottieDirectReferenceWeight n : ℝ)/(dottieDirectReferenceDenominator : ℝ) -
      (1/Real.sqrt n) * Real.cos (phase - (dottieHeight - 1/512) * Real.log n)| ≤
        (1/10^11)/Real.sqrt n := by
  let scale : ℕ := 2^64
  let x : ℝ := (inverseSqrtTicks scale n : ℝ)/(scale : ℝ)
  let y : ℝ := (directReferenceCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4
  let a : ℝ := 1/Real.sqrt n
  let b := Real.cos (phase - (dottieHeight - 1/512) * Real.log n)
  have hcos : |y - b| ≤ 8/10^12 := directReferenceCosine_error hn hN hphase
  obtain ⟨hx, hx'⟩ := inverseSqrtTicks_spec scale n (by decide +kernel) hn
  change x ≤ a at hx
  rw [add_div] at hx'
  change a < x + 1/(scale : ℝ) at hx'
  rw [show (scale : ℝ) = 2^64 by norm_num [scale]] at hx'
  have hxp : 0 ≤ x := by dsimp [x]; positivity
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hcap : Real.sqrt n ≤ (2:ℝ)^16 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have h : (n : ℝ) ≤ 276824064 := by exact_mod_cast hN
    exact h.trans (by norm_num)
  have he : |x - a| ≤ (1/10^13)*a := by
    rw [abs_of_nonpos (sub_nonpos.mpr hx)]
    calc
      _ ≤ 1/(2:ℝ)^64 := by linarith only [hx']
      _ ≤ (1/10^13)*(1/(2:ℝ)^16) := by norm_num
      _ ≤ (1/10^13)*a := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hsqrt hcap) (by norm_num)
  have h1 : |x*(y - b)| ≤ a*(8/10^12) := by
    rw [abs_mul, abs_of_nonneg hxp]
    exact mul_le_mul hx hcos (abs_nonneg _) (hxp.trans hx)
  have h2 : |(x - a)*b| ≤ (1/10^13)*a := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
      (mul_one _)).trans he
  have hs : (dottieDirectReferenceWeight n : ℝ)/(dottieDirectReferenceDenominator : ℝ) = x*y := by
    simp [dottieDirectReferenceWeight, dottieDirectReferenceDenominator, x, y, scale, div_mul_div_comm]
  rw [hs]
  change |x*y - a*b| ≤ _
  rw [show x*y - a*b = x*(y - b) + (x - a)*b by ring]
  rw [show (1:ℝ)/10^11/Real.sqrt n = (1/10^11)*a by dsimp only [a]; ring]
  exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans (by linarith only [hxp.trans hx]))

/-- The full reference calculation uses one signed integer total. -/
def dottieDirectReferenceScore : ℤ :=
  dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 (276824064 : ℕ).sqrt

theorem dottie_reference_projection_direct_score_error :
    abs (dottieRelativeReferenceProjection -
      abs ((dottieDirectReferenceScore : ℝ)/(dottieDirectReferenceDenominator : ℝ))) ≤
        33276 / 10^11 := by
  obtain ⟨phase, hphase, hunit⟩ := dottie_sharp_reference_unit_precise_phase
  let val := (dottieDirectReferenceScore : ℝ)/(dottieDirectReferenceDenominator : ℝ)
  let f (n : ℕ) := Real.cos (phase - (dottieHeight - 1/512) * Real.log n)
  let S := ∑ n ∈ range 276824064, ((archivedLatticeCoeff (n+1) : ℝ)/Real.sqrt (n+1))*f (n+1)
  have hR : dottieRelativeReferenceProjection = |S| := by
    unfold dottieRelativeReferenceProjection S f
    rw [hunit, dottieReferencePoint, projectedDirichlet_eq_cosine_sum]
    simp only [Nat.cast_add, Nat.cast_one]
  have hval : val = ∑ n ∈ range 276824064,
      (archivedLatticeCoeff (n+1) : ℝ) *
        ((dottieDirectReferenceWeight (n+1) : ℝ)/(dottieDirectReferenceDenominator : ℝ)) := by
    dsimp only [val, dottieDirectReferenceScore]
    rw [DottieFixedIntervals.dottie_paired_row_score_eq_archived, Int.cast_sum, Finset.sum_div]
    simp only [Int.cast_mul, mul_div_assoc]
  have herr : |val - S| ≤ 33276 / 10^11 := by
    rw [hval]
    dsimp only [S]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ (1/10^11) * signedMomentMass archivedLatticeCoeff 276824064 := by
        rw [signedMomentMass, Finset.mul_sum]
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn' : n+1 ≤ 276824064 := Nat.succ_le_of_lt (mem_range.mp hn)
        have hw := directReferenceWeight_error (Nat.succ_pos n) hn' hphase
        let c : ℝ := archivedLatticeCoeff (n+1)
        let q := (dottieDirectReferenceWeight (n+1) : ℝ)/(dottieDirectReferenceDenominator : ℝ)
        have hw' : |q - (1/Real.sqrt (n+1))*f (n+1)| ≤ (1/10^11)/Real.sqrt (n+1) := by
          simpa only [q, f, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hw
        change |c*q - c/Real.sqrt (n+1)*f (n+1)| ≤ (1/10^11)*(|c|/Real.sqrt (n+1))
        rw [show c*q - c/Real.sqrt (n+1)*f (n+1) =
          c*(q - (1/Real.sqrt (n+1))*f (n+1)) by ring, abs_mul]
        calc
          _ ≤ |c| * ((1/10^11)/Real.sqrt (n+1)) := mul_le_mul_of_nonneg_left hw' (abs_nonneg c)
          _ = _ := by ring
      _ ≤ (1/10^11)*33276 := mul_le_mul_of_nonneg_left reference_mass_le (by norm_num)
      _ = _ := by ring
  change abs (dottieRelativeReferenceProjection - abs val) ≤ _
  rw [hR]
  exact (abs_abs_sub_abs_le_abs_sub S val).trans (by rwa [abs_sub_comm])

/-- A single integer comparison supplies the clean reference bound. -/
theorem dottie_reference_decimal_of_direct_score_bound
    (hscore : (10^7 : ℤ) * |dottieDirectReferenceScore| ≤
      1716866 * (dottieDirectReferenceDenominator : ℤ)) :
    dottieRelativeReferenceProjection ≤ 171687/10^6 := by
  have hreal : (10^7 : ℝ) * |(dottieDirectReferenceScore : ℝ)| ≤
      1716866 * (dottieDirectReferenceDenominator : ℝ) := by exact_mod_cast hscore
  have hd : (0 : ℝ) < (dottieDirectReferenceDenominator : ℝ) := by
    norm_num [dottieDirectReferenceDenominator, fixedCosScale]
  have hval : |(dottieDirectReferenceScore : ℝ)/(dottieDirectReferenceDenominator : ℝ)| ≤
      1716866/10^7 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10^7)).2
      (by simpa only [mul_comm] using hreal :
        |(dottieDirectReferenceScore : ℝ)| * 10^7 ≤
          1716866 * (dottieDirectReferenceDenominator : ℝ))
    exact h.trans_eq (by ring)
  have herr := (abs_le.mp dottie_reference_projection_direct_score_error).2
  linarith only [hval, herr]

#print axioms dottie_reference_projection_direct_score_error
#print axioms dottie_reference_decimal_of_direct_score_bound

end QuarticModel
