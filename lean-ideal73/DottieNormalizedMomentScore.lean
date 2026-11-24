import DottieFixedMomentWeights
import DottiePairedRows

/-! Transport integer lattice scores into the two components of an exact
Dottie moment. Weights are evaluated at the rational height. The final
rectangle includes the separately proved error in the exact height. -/

namespace QuarticModel.DottieFixedIntervals

open Complex Finset
set_option autoImplicit false

/-- An integer pair in the shared fixed-point denominator. -/
noncomputable def momentScorePoint (r i : ℤ) : ℂ :=
  ⟨(r:ℝ)/(scale:ℝ), (i:ℝ)/(scale:ℝ)⟩

private theorem momentScorePoint_mul (a r i : ℤ) :
    (a:ℂ)*momentScorePoint r i = momentScorePoint (a*r) (a*i) := by
  apply Complex.ext <;>
    simp [momentScorePoint,Complex.mul_re,Complex.mul_im,Int.cast_mul,mul_div_assoc]

private theorem momentScorePoint_sum {ι : Type*} (s : Finset ι) (f g : ι → ℤ) :
    momentScorePoint (∑ n ∈ s, f n) (∑ n ∈ s, g n) =
      ∑ n ∈ s, momentScorePoint (f n) (g n) := by
  apply Complex.ext <;>
    simp [momentScorePoint,Complex.re_sum,Complex.im_sum,Int.cast_sum,Finset.sum_div]

def Interval.midpointTicks (a : Interval) : ℤ := (a.lo+a.hi)/2

def Interval.radiusTicks (a : Interval) : ℤ :=
  max (a.midpointTicks-a.lo) (a.hi-a.midpointTicks)

private theorem Interval.midpoint_error {a : Interval} {x : ℝ} (hx : a.Contains x) :
    |(a.midpointTicks:ℝ)/(scale:ℝ)-x| ≤ (a.radiusTicks:ℝ)/(scale:ℝ) := by
  apply abs_le.mpr
  have hl : (a.midpointTicks:ℝ)-(a.lo:ℝ) ≤ (a.radiusTicks:ℝ) := by
    exact_mod_cast le_max_left (a.midpointTicks-a.lo) (a.hi-a.midpointTicks)
  have hh : (a.hi:ℝ)-(a.midpointTicks:ℝ) ≤ (a.radiusTicks:ℝ) := by
    exact_mod_cast le_max_right (a.midpointTicks-a.lo) (a.hi-a.midpointTicks)
  constructor
  · calc
      _ = -(a.radiusTicks:ℝ)/(scale:ℝ) := by ring
      _ ≤ ((a.midpointTicks:ℝ)-x*(scale:ℝ))/(scale:ℝ) :=
        (div_le_div_iff_of_pos_right real_scale_pos).2 (by linarith only [hx.2,hh])
      _ = _ := by field_simp [real_scale_pos.ne']
  · apply (le_div_iff₀ real_scale_pos).2
    rw [sub_mul, div_mul_cancel₀ _ real_scale_pos.ne']
    linarith only [hx.1,hl]

def momentWeightRealTicks (n k : ℕ) : ℤ :=
  (normalizedMomentWeightBox n k).re.midpointTicks

def momentWeightImagTicks (n k : ℕ) : ℤ :=
  (normalizedMomentWeightBox n k).im.midpointTicks

def momentWeightRadiusTicks (n k : ℕ) : ℤ :=
  let a := normalizedMomentWeightBox n k
  a.re.radiusTicks+a.im.radiusTicks

/-- A comparison of integer endpoints certifies the needed relative error
in both coordinates together. -/
theorem momentWeight_relative_error_of_ticks {n k : ℕ} (hn : 0 < n)
    (hcap : n ≤ dottiePrefixEnd)
    (h : 10^12 * momentWeightRadiusTicks n k ≤ (inverseSqrtTicks scale.toNat n : ℤ)) :
    ‖momentScorePoint (momentWeightRealTicks n k) (momentWeightImagTicks n k) -
      normalizedMomentWeight n k‖ ≤ (1/10^12)/Real.sqrt n := by
  let a := normalizedMomentWeightBox n k
  have hb := normalizedMomentWeightBox_sound (k := k) hn hcap
  have hr := Interval.midpoint_error hb.1
  have hi := Interval.midpoint_error hb.2
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (momentScorePoint (momentWeightRealTicks n k) (momentWeightImagTicks n k) -
      normalizedMomentWeight n k)
  have hs : (scale.toNat:ℝ) = (scale:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg scale_pos.le
  have hinv := (inverseSqrtTicks_spec scale.toNat n (by decide +kernel) hn).1
  rw [hs] at hinv
  change (10:ℤ)^12*(a.re.radiusTicks+a.im.radiusTicks) ≤ (inverseSqrtTicks scale.toNat n:ℤ) at h
  have hreal : (10:ℝ)^12*((a.re.radiusTicks:ℝ)+(a.im.radiusTicks:ℝ)) ≤
      (inverseSqrtTicks scale.toNat n:ℝ) := by
    exact_mod_cast h
  refine hnorm.trans ?_
  simp only [Complex.sub_re,Complex.sub_im,momentScorePoint,
    momentWeightRealTicks,momentWeightImagTicks]
  refine (add_le_add hr hi).trans ?_
  rw [← add_div]
  have hw := (div_le_div_of_nonneg_right hreal real_scale_pos.le).trans hinv
  rw [mul_div_assoc] at hw
  calc
    _ ≤ (1/Real.sqrt n)/(10:ℝ)^12 := (le_div_iff₀ (by norm_num)).2 (by simpa only [mul_comm] using hw)
    _ = (1/10^12)/Real.sqrt n := by ring

theorem dottie_paired_row_score_eq_archived (N : ℕ) (f : ℕ → ℤ) :
    dottiePairedRowSpan N f 0 N.sqrt =
      ∑ j ∈ range N, archivedLatticeCoeff (j+1) * f (j+1) := by
  rw [← dottieSymmetricScore_eq_row_span, dottieSymmetricScore_eq_dottieTriangleScore,
    dottieTriangleScore_eq_archivedLatticeCoeff]

private theorem normalizedRationalMomentScore_error {N k : ℕ} (hr hi : ℕ → ℤ)
    {e : ℝ} (he : 0 ≤ e)
    (hweights : ∀ n : ℕ, 0 < n → n ≤ N →
      ‖momentScorePoint (hr n) (hi n) - normalizedMomentWeight n k‖ ≤ e/Real.sqrt n) :
    ‖momentScorePoint (dottiePairedRowSpan N hr 0 N.sqrt)
        (dottiePairedRowSpan N hi 0 N.sqrt) -
        signedMoment archivedLatticeCoeff N (1/2+(dottieMomentRationalHeight:ℂ)*I) k/(32:ℂ)^k‖
      ≤ e * (2*(N.sqrt:ℝ)) := by
  rw [dottie_paired_row_score_eq_archived, dottie_paired_row_score_eq_archived,
    momentScorePoint_sum, normalizedMoment_eq_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ e * signedMomentMass archivedLatticeCoeff N := by
      rw [signedMomentMass, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [← momentScorePoint_mul, ← mul_sub, norm_mul, ← Complex.ofReal_intCast,
        Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left
        (hweights (j+1) (Nat.succ_pos j) (Nat.succ_le_of_lt (mem_range.mp hj)))
        (abs_nonneg _)).trans_eq (by push_cast; ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left (archivedMomentMass_le_two_sqrt N) he

private theorem normalizedExactHeight_error {N : ℕ} (hN : N ≤ dottiePrefixEnd) (k : ℕ) :
    ‖signedMoment archivedLatticeCoeff N dottieSharpCenter k/(32:ℂ)^k -
      signedMoment archivedLatticeCoeff N (1/2+(dottieMomentRationalHeight:ℂ)*I) k/(32:ℂ)^k‖
      ≤ 1/(5*10^12) := by
  rw [← sub_div, norm_div, norm_pow, Complex.norm_ofNat]
  apply (div_le_iff₀ (by positivity)).2
  exact (dottie_moment_exact_height_error hN k).trans_eq (by ring)

theorem normalizedExactMomentScore_error {N k : ℕ} (hN : N ≤ dottiePrefixEnd)
    (fr fi : ℕ → ℤ) {e : ℝ} (he : 0 ≤ e)
    (hweights : ∀ n : ℕ, 0 < n → n ≤ N →
      ‖momentScorePoint (fr n) (fi n) - normalizedMomentWeight n k‖ ≤ e/Real.sqrt n) :
    ‖signedMoment archivedLatticeCoeff N dottieSharpCenter k/(32:ℂ)^k -
      momentScorePoint (dottiePairedRowSpan N fr 0 N.sqrt)
        (dottiePairedRowSpan N fi 0 N.sqrt)‖ ≤ e * (2*(N.sqrt:ℝ)) + 1/(5*10^12) := by
  let a := signedMoment archivedLatticeCoeff N dottieSharpCenter k/(32:ℂ)^k
  let b := signedMoment archivedLatticeCoeff N (1/2+(dottieMomentRationalHeight:ℂ)*I) k/(32:ℂ)^k
  let c := momentScorePoint (dottiePairedRowSpan N fr 0 N.sqrt)
    (dottiePairedRowSpan N fi 0 N.sqrt)
  have h := normalizedRationalMomentScore_error fr fi he hweights
  change ‖c-b‖ ≤ _ at h
  change ‖a-c‖ ≤ _
  rw [show a-c = (a-b)-(c-b) by ring, add_comm]
  exact (norm_sub_le _ _).trans (add_le_add (normalizedExactHeight_error hN k) h)

def momentScoreRect (r i : ℤ) (k : ℕ) (e : ℚ) : Rect :=
  (Interval.rational (32^k) (32^k)).scaleBy ((⟨⟨r,r⟩,⟨i,i⟩⟩ : Rect).pad e)

private theorem momentScorePoint_mem (r i : ℤ) :
    (⟨⟨r,r⟩,⟨i,i⟩⟩ : Rect).Contains (momentScorePoint r i) := by
  have hs : (scale:ℝ) ≠ 0 := real_scale_pos.ne'
  simp [Rect.Contains,Interval.Contains,momentScorePoint,div_mul_cancel₀ _ hs]

theorem momentScoreRect_sound {N k : ℕ} {r i : ℤ} {e : ℚ}
    (herr : ‖signedMoment archivedLatticeCoeff N dottieSharpCenter k/(32:ℂ)^k -
      momentScorePoint r i‖ ≤ (e:ℝ)) :
    (momentScoreRect r i k e).Contains (signedMoment archivedLatticeCoeff N dottieSharpCenter k) := by
  have hp := Rect.pad_sound (momentScorePoint_mem r i) herr
  have h : (Interval.rational (32^k) (32^k)).Contains ((32:ℝ)^k) := by
    apply Interval.rational_sound <;> push_cast <;> rfl
  have hx := Rect.scale_sound h hp
  simpa only [momentScoreRect, Complex.ofReal_pow, Complex.ofReal_ofNat,
    mul_div_cancel₀ _ (pow_ne_zero _ (by norm_num : (32:ℂ) ≠ 0))] using hx

def Rect.fits (inner outer : Rect) : Bool :=
  decide (outer.re.lo ≤ inner.re.lo ∧ inner.re.hi ≤ outer.re.hi ∧
    outer.im.lo ≤ inner.im.lo ∧ inner.im.hi ≤ outer.im.hi)

private theorem Rect.fits_sound {inner outer : Rect} {z : ℂ}
    (hfit : inner.fits outer = true) (hz : inner.Contains z) : outer.Contains z := by
  simp only [Rect.fits,decide_eq_true_eq] at hfit
  obtain ⟨hr₀,hr₁,hi₀,hi₁⟩ := hfit
  exact ⟨⟨(by exact_mod_cast hr₀ : (outer.re.lo:ℝ) ≤ inner.re.lo).trans hz.1.1,
      hz.1.2.trans (by exact_mod_cast hr₁)⟩,
    ⟨(by exact_mod_cast hi₀ : (outer.im.lo:ℝ) ≤ inner.im.lo).trans hz.2.1,
      hz.2.2.trans (by exact_mod_cast hi₁)⟩⟩

/-- Two integer sums and the relative-width comparisons suffice to check an
input rectangle of the full circle certificate. The fixed radius here is
in the normalized coordinate, before restoring `32^k`. -/
theorem archivedMomentBox_of_scores {N k : ℕ} {r i : ℤ} {target : Rect}
    (hN : N ≤ dottiePrefixEnd)
    (hwidth : ∀ n : ℕ, 0 < n → n ≤ N →
      10^12*momentWeightRadiusTicks n k ≤ (inverseSqrtTicks scale.toNat n:ℤ))
    (hr : dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) 0 N.sqrt = r)
    (hi : dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) 0 N.sqrt = i)
    (hfit : (momentScoreRect r i k (8/10^8)).fits target = true) :
    target.Contains (signedMoment archivedLatticeCoeff N dottieSharpCenter k) := by
  have hh := normalizedExactMomentScore_error (k := k) hN (fun n => momentWeightRealTicks n k)
    (fun n => momentWeightImagTicks n k) (e := 1/10^12) (by norm_num)
    (fun n hn hnN => momentWeight_relative_error_of_ticks hn (hnN.trans hN) (hwidth n hn hnN))
  rw [hr,hi] at hh
  have hn := (Nat.sqrt_le_sqrt hN).trans_eq (show dottiePrefixEnd.sqrt = 37984 by decide +kernel)
  have hn' : (N.sqrt:ℝ) ≤ 37984 := by exact_mod_cast hn
  have hb : (1/10^12)*(2*(N.sqrt:ℝ)) + 1/(5*10^12) ≤ ((8/10^8:ℚ):ℝ) := by
    push_cast
    linarith only [hn']
  exact Rect.fits_sound hfit (momentScoreRect_sound (hh.trans hb))

#print axioms dottie_paired_row_score_eq_archived
#print axioms momentWeight_relative_error_of_ticks
#print axioms normalizedExactMomentScore_error
#print axioms momentScoreRect_sound
#print axioms archivedMomentBox_of_scores

end QuarticModel.DottieFixedIntervals
