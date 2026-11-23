import DottieFixedCircle
import DottieMomentPhase
import DottieReferenceWeights

/-! Integer interval evaluation of the weights for the 17 retained
moments. The divisor `32^k` keeps the logarithmic powers bounded. -/

namespace QuarticModel.DottieFixedIntervals

open Complex Finset SuperZeta.StirlingCorrection
open private signedTerm from DottieSignedMoments
set_option autoImplicit false

private def inverseSqrtBox (n : ℕ) : Interval :=
  let lo : ℤ := inverseSqrtTicks scale.toNat n
  ⟨lo,lo+1⟩

private theorem inverseSqrtBox_sound {n : ℕ} (hn : 0 < n) :
    (inverseSqrtBox n).Contains (1/Real.sqrt n) := by
  have hs : (scale.toNat : ℝ) = (scale : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg scale_pos.le
  obtain ⟨hl,hh⟩ := inverseSqrtTicks_spec scale.toNat n (by decide +kernel) hn
  rw [hs] at hl hh
  exact ⟨by simpa only [inverseSqrtBox,Int.cast_natCast] using
    (div_le_iff₀ real_scale_pos).mp hl, by
    simpa only [inverseSqrtBox,Int.cast_add,Int.cast_natCast,Int.cast_one] using
      ((lt_div_iff₀ real_scale_pos).mp hh).le⟩

private def normalizedLogBox (n : ℕ) : Interval :=
  let lo : ℚ := dottieQuickLogLowerTicks n
  Interval.rational (-(lo+128)/2^101) (-lo/2^101)

private theorem normalizedLogBox_sound {n : ℕ} (hn : 0 < n) (hcap : n ≤ dottiePrefixEnd) :
    (normalizedLogBox n).Contains (-Real.log n/32) := by
  have h := dottieQuickLogLowerTicks_sharp_spec n hn (by simpa only [dottiePrefixEnd] using hcap)
  unfold normalizedLogBox
  apply Interval.rational_sound <;> push_cast <;> norm_num at h ⊢ <;> linarith only [h.1,h.2]

private def Interval.power (b : Interval) : ℕ → Interval
  | 0 => ⟨scale,scale⟩
  | k+1 => (b.power k).mul b

private theorem Interval.power_sound {b : Interval} {v : ℝ} (h : b.Contains v) (k : ℕ) :
    (b.power k).Contains (v^k) := by
  induction k with
  | zero => simp [Interval.power,Interval.Contains]
  | succ k ih => simpa only [Interval.power,pow_succ] using Interval.mul_sound ih h

private def reducedHalfPhase (n : ℕ) : Rect :=
  let θ := dottieMomentReducedAngle n/2
  imaginaryBox (Interval.rational θ θ)

private theorem reducedHalfPhase_ticks (n : ℕ) : (reducedHalfPhase n).normUpperTicks ≤ 2*scale := by
  let θ := dottieMomentReducedAngle n/2
  obtain ⟨hl,hh⟩ := dottie_moment_reduced_angle_bounds n
  have hπ : dottieMomentPiRat ≤ 4 := by norm_num [dottieMomentPiRat]
  have hls : (-2:ℚ) ≤ θ := by dsimp only [θ]; linarith only [hl,hπ]
  have hhs : θ ≤ (2:ℚ) := by dsimp only [θ]; linarith only [hh,hπ]
  have hscale : 0 ≤ (scale:ℚ) := by exact_mod_cast scale_pos.le
  have h₁ : -2*scale ≤ ⌊θ*(scale:ℚ)⌋ := Int.le_floor.mpr (by
    push_cast
    exact mul_le_mul_of_nonneg_right hls hscale)
  have h₂ : ⌈θ*(scale:ℚ)⌉ ≤ 2*scale := Int.ceil_le.mpr (by
    push_cast
    exact mul_le_mul_of_nonneg_right hhs hscale)
  have h₃ := Int.floor_le_ceil (θ*(scale:ℚ))
  change (0:ℤ) + max |⌊θ*(scale:ℚ)⌋| |⌈θ*(scale:ℚ)⌉| ≤ 2*scale
  rw [zero_add, max_le_iff]
  exact ⟨abs_le.mpr ⟨h₁,h₃.trans h₂⟩,abs_le.mpr ⟨h₁.trans h₃,h₂⟩⟩

private noncomputable def momentPhase (n : ℕ) : ℂ :=
  exp (((-(dottieMomentRationalHeight * Real.log n):ℝ):ℂ)*I)

private def momentPhaseBox (n : ℕ) : Rect :=
  let half := (reducedHalfPhase n).expBox
  (half.mul half).pad (1/10^13)

private theorem momentPhaseBox_sound {n : ℕ} (hn : 0 < n) (hcap : n ≤ dottiePrefixEnd) :
    (momentPhaseBox n).Contains (momentPhase n) := by
  let θ : ℚ := dottieMomentReducedAngle n/2
  have hθ : (reducedHalfPhase n).Contains (((θ:ℝ):ℂ)*I) :=
    imaginaryBox_sound (Interval.rational_sound le_rfl le_rfl)
  have hhalf := Rect.expBox_sound hθ (reducedHalfPhase_ticks n)
  apply Rect.pad_sound (Rect.mul_sound hhalf hhalf)
  rw [← Complex.exp_add, show ((θ:ℝ):ℂ)*I+((θ:ℝ):ℂ)*I =
      ((dottieMomentReducedAngle n:ℝ):ℂ)*I by dsimp only [θ]; push_cast; ring]
  simpa only [momentPhase,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using
    dottie_moment_rational_phase_error n hn hcap

noncomputable def normalizedMomentWeight (n k : ℕ) : ℂ :=
  (((1/Real.sqrt n)*(-Real.log n/32)^k/(k.factorial:ℝ):ℝ):ℂ) * momentPhase n

def normalizedMomentWeightBox (n k : ℕ) : Rect :=
  let factor : ℚ := 1/(k.factorial : ℚ)
  let magnitude := (inverseSqrtBox n).mul ((normalizedLogBox n).power k)
  (magnitude.mul (Interval.rational factor factor)).scaleBy (momentPhaseBox n)

theorem normalizedMomentWeightBox_sound {n k : ℕ} (hn : 0 < n) (hcap : n ≤ dottiePrefixEnd) :
    (normalizedMomentWeightBox n k).Contains (normalizedMomentWeight n k) := by
  have h := Interval.mul_sound (inverseSqrtBox_sound hn)
    (Interval.power_sound (normalizedLogBox_sound hn hcap) k)
  have hf : (Interval.rational (1/(k.factorial:ℚ)) (1/(k.factorial:ℚ))).Contains
      (1/(k.factorial:ℝ)) := by apply Interval.rational_sound <;> push_cast <;> rfl
  simpa only [normalizedMomentWeightBox,normalizedMomentWeight,div_eq_mul_inv,one_mul]
    using Rect.scale_sound (Interval.mul_sound h hf) (momentPhaseBox_sound hn hcap)

private theorem criticalHeightPower (n : ℕ) (hn : 0 < n) :
    (n:ℂ)^(-(1/2+(dottieMomentRationalHeight:ℂ)*I)) =
      (((1/Real.sqrt n : ℝ):ℂ) * momentPhase n) := by
  have hnr : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnc : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold momentPhase
  rw [Complex.cpow_def_of_ne_zero hnc, ← Complex.natCast_log]
  rw [show ((Real.log n:ℝ):ℂ)*(-(1/2+(dottieMomentRationalHeight:ℂ)*I)) =
        ((-Real.log n/2:ℝ):ℂ)+((-(dottieMomentRationalHeight*Real.log n):ℝ):ℂ)*I by
      push_cast
      ring,
    Complex.exp_add, ← Complex.ofReal_exp]
  have h := Real.rpow_def_of_pos hnr (-(1/2):ℝ)
  rw [Real.rpow_neg hnr.le, ← Real.sqrt_eq_rpow, show Real.log n * (-(1/2):ℝ) =
      -Real.log n/2 by ring, ← one_div] at h
  rw [← h]

/-- The exact normalized moment is a signed sum of the enclosed weights. -/
theorem normalizedMoment_eq_sum (a : ℕ → ℤ) (N k : ℕ) :
    signedMoment a N (1/2+(dottieMomentRationalHeight:ℂ)*I) k/(32:ℂ)^k =
      ∑ n ∈ range N, (a (n+1):ℂ)*normalizedMomentWeight (n+1) k := by
  unfold signedMoment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  unfold signedTerm normalizedMomentWeight
  rw [criticalHeightPower (n+1) (Nat.succ_pos n)]
  push_cast
  rw [div_pow]
  have hf : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hc : (32:ℂ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  field_simp [hf,hc]

#print axioms normalizedMomentWeightBox_sound
#print axioms normalizedMoment_eq_sum

end QuarticModel.DottieFixedIntervals
