import DottieJointSharpCircle

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection
open private ceilDiv from DottieFixedIntervals

set_option autoImplicit false

private def scorePadTicks : ℤ := 1475739525897

private theorem scorePad_eq :
    Interval.rational (-(8/10^8)) (8/10^8) = ⟨-scorePadTicks,scorePadTicks⟩ := by
  have h : ⌈(8/10^8 : ℚ)*(scale : ℚ)⌉ = scorePadTicks := by decide +kernel
  unfold Interval.rational
  rw [neg_mul, Int.floor_neg, h]

private theorem degreeScale_eq (k : ℕ) :
    Interval.rational (32^k) (32^k) = ⟨(32:ℤ)^k*scale,(32:ℤ)^k*scale⟩ := by
  have h : (32:ℚ)^k * (scale:ℚ) = ((((32:ℤ)^k)*scale : ℤ) : ℚ) := by
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  simp only [Interval.rational, h, Int.floor_intCast, Int.ceil_intCast]

private theorem mulScale_eq (m lo hi : ℤ) (hm : 0 ≤ m) (h : lo ≤ hi) :
    (⟨m*scale,m*scale⟩ : Interval).mul ⟨lo,hi⟩ = ⟨m*lo,m*hi⟩ := by
  have hOrder : m*scale*lo ≤ m*scale*hi :=
    mul_le_mul_of_nonneg_left h (mul_nonneg hm scale_pos.le)
  have hCeil (a : ℤ) : ceilDiv (a*scale) scale = a := by
    rw [ceilDiv, ← neg_mul, Int.mul_ediv_cancel _ scale_pos.ne', neg_neg]
  simp only [Interval.mul, min_eq_left hOrder, max_eq_right hOrder, min_self, max_self]
  rw [show m*scale*lo = (m*lo)*scale by ring, show m*scale*hi = (m*hi)*scale by ring,
    Int.mul_ediv_cancel _ scale_pos.ne', hCeil]

private theorem momentScoreRect_endpoints (r i : ℤ) (k : ℕ) :
    momentScoreRect r i k (8/10^8) =
      ⟨⟨(32:ℤ)^k*(r-scorePadTicks), (32:ℤ)^k*(r+scorePadTicks)⟩,
       ⟨(32:ℤ)^k*(i-scorePadTicks), (32:ℤ)^k*(i+scorePadTicks)⟩⟩ := by
  have hm : (0:ℤ) ≤ 32^k := by positivity
  have hr : r + -scorePadTicks ≤ r+scorePadTicks := by unfold scorePadTicks; omega
  have hi : i + -scorePadTicks ≤ i+scorePadTicks := by unfold scorePadTicks; omega
  simp only [momentScoreRect, degreeScale_eq, Rect.pad, scorePad_eq, Rect.add, Interval.add,
    Interval.scaleBy, mulScale_eq _ _ _ hm hr, mulScale_eq _ _ _ hm hi, sub_eq_add_neg]

private theorem ceilDiv_le_iff (target upper m : ℤ) (hm : 0 < m) :
    ceilDiv target m ≤ upper ↔ target ≤ upper*m := by
  constructor
  · intro h
    have hNeg : -upper ≤ (-target)/m := by unfold ceilDiv at h; omega
    have hMul := (Int.le_ediv_iff_mul_le hm).1 hNeg
    rw [neg_mul] at hMul
    omega
  · intro h
    have hMul : (-upper)*m ≤ -target := by rw [neg_mul]; omega
    have hNeg := (Int.le_ediv_iff_mul_le hm).2 hMul
    unfold ceilDiv
    omega

/-- An original score interval expressed in the integer units before multiplying by the degree scale. -/
def dottieAdmissibleScoreTicks (k : ℕ) (target : Interval) : Interval :=
  ⟨ceilDiv target.lo ((32:ℤ)^k)+scorePadTicks, target.hi/((32:ℤ)^k)-scorePadTicks⟩

private theorem scoreComponent_fits (x : ℤ) (k : ℕ) (target : Interval) :
    (target.lo ≤ (32:ℤ)^k*(x-scorePadTicks) ∧ (32:ℤ)^k*(x+scorePadTicks) ≤ target.hi) ↔
      (dottieAdmissibleScoreTicks k target).lo ≤ x ∧ x ≤ (dottieAdmissibleScoreTicks k target).hi := by
  have hm : (0:ℤ) < 32^k := by positivity
  rw [mul_comm ((32:ℤ)^k) (x-scorePadTicks), mul_comm ((32:ℤ)^k) (x+scorePadTicks),
    ← ceilDiv_le_iff _ _ _ hm, ← Int.le_ediv_iff_mul_le hm]
  dsimp only [dottieAdmissibleScoreTicks]
  omega

/-- The original sharp box check is exactly membership in two integer intervals. -/
theorem dottie_moment_score_fit_iff (r i : ℤ) (k : ℕ) (target : Rect) :
    (momentScoreRect r i k (8/10^8)).fits target = true ↔
      ((dottieAdmissibleScoreTicks k target.re).lo ≤ r ∧ r ≤ (dottieAdmissibleScoreTicks k target.re).hi) ∧
      ((dottieAdmissibleScoreTicks k target.im).lo ≤ i ∧ i ≤ (dottieAdmissibleScoreTicks k target.im).hi) := by
  rw [Rect.fits, decide_eq_true_eq, momentScoreRect_endpoints]
  exact and_assoc.symm.trans (and_congr (scoreComponent_fits r k target.re)
    (scoreComponent_fits i k target.im))

def dottieSharpAdmissibleTicks (k : ℕ) : Rect :=
  ⟨dottieAdmissibleScoreTicks k (fixedSharpInput k).re,
   dottieAdmissibleScoreTicks k (fixedSharpInput k).im⟩

theorem dottie_sharp_admissible_ticks_nonempty (k : Fin 11) :
    (dottieSharpAdmissibleTicks k).re.lo ≤ (dottieSharpAdmissibleTicks k).re.hi ∧
    (dottieSharpAdmissibleTicks k).im.lo ≤ (dottieSharpAdmissibleTicks k).im.hi := by
  fin_cases k <;> decide +kernel

/-- Bounds on the full integer sums are sufficient for the same sharp-circle conclusion. -/
theorem dottie_sharp_margin_of_score_ranges
    (hScores : ∀ k < 11,
      let r := dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightRealTicks n k) 0 dottiePrefixEnd.sqrt
      let i := dottiePairedRowSpan dottiePrefixEnd (fun n => momentWeightImagTicks n k) 0 dottiePrefixEnd.sqrt
      let box := dottieSharpAdmissibleTicks k
      (box.re.lo ≤ r ∧ r ≤ box.re.hi) ∧ (box.im.lo ≤ i ∧ i ≤ box.im.hi))
    (hReference : dottieRelativeReferenceProjection ≤ 171687/10^6) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_margin_of_decimal_reference _ hReference
  intro k hk
  rw [archivedScoredMomentBox, dottie_moment_score_fit_iff]
  exact hScores k hk

#print axioms dottie_moment_score_fit_iff
#print axioms dottie_sharp_admissible_ticks_nonempty
#print axioms dottie_sharp_margin_of_score_ranges

end QuarticModel.DottieFixedIntervals
