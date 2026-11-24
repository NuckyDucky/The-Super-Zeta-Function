import DottieFixedIntervals
import DottieHeightPerturbation
import DottieSharpCircleMoments

/-! Enclose the high-degree moments using absolute mass. Only the low
degrees require evaluation of the oscillating signed sums. -/

namespace QuarticModel.DottieFixedIntervals

open Complex Finset SuperZeta.StirlingCorrection
open private signedTerm signedTerm_norm from DottieSignedMoments
open private reference_mass_le from DottieHeightPerturbation
set_option autoImplicit false

def tailMomentBox (mass logCap k : ℕ) : Rect :=
  Rect.zero.pad ((mass:ℚ)*(logCap:ℚ)^k/(k.factorial:ℚ))

private theorem log_le_of_cutoff {N L : ℕ} (hN : (N:ℝ) < (2.7:ℝ)^L)
    {n : ℕ} (hn : n ∈ range N) : Real.log (n+1) ≤ L := by
  have hbase : (2.7:ℝ)^L ≤ Real.exp (L:ℝ) := by
    rw [show (L:ℝ) = (L:ℕ)*(1:ℝ) by simp,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hnR : (n+1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
  exact ((Real.log_lt_iff_lt_exp (by positivity)).2 ((hnR.trans_lt hN).trans_le hbase)).le

private theorem tailMomentBox_sound {N mass logCap : ℕ} (hmass : signedMomentMass archivedLatticeCoeff N ≤ mass)
    (hN : (N:ℝ) < (2.7:ℝ)^logCap) (k : ℕ) :
    (tailMomentBox mass logCap k).Contains (signedMoment archivedLatticeCoeff N dottieSharpCenter k) := by
  apply Rect.pad_sound Rect.zero_sound
  rw [sub_zero]
  push_cast
  have hs : dottieSharpCenter.re = 1/2 := by norm_num [dottieSharpCenter,Complex.mul_re]
  have hcoef : 0 ≤ (logCap:ℝ)^k/(k.factorial:ℝ) := by positivity
  unfold signedMoment
  calc
    _ ≤ ∑ n ∈ range N, ‖signedTerm archivedLatticeCoeff dottieSharpCenter n *
        ((-(Real.log (n+1)):ℝ):ℂ)^k/(k.factorial:ℂ)‖ := norm_sum_le _ _
    _ ≤ signedMomentMass archivedLatticeCoeff N*((logCap:ℝ)^k/(k.factorial:ℝ)) := by
      rw [signedMomentMass,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro n hn
      have hlog : 0 ≤ Real.log (n+1) := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])
      rw [norm_div,norm_mul,signedTerm_norm hs,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_neg,abs_of_nonneg hlog,Complex.norm_natCast,mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hlog (log_le_of_cutoff hN hn) _) (Nat.cast_nonneg _)) (by positivity)
    _ ≤ (mass:ℝ)*((logCap:ℝ)^k/(k.factorial:ℝ)) := mul_le_mul_of_nonneg_right hmass hcoef
    _ = _ := by ring

theorem sharpTailMomentBox_sound (k : ℕ) :
    (tailMomentBox 76000 22 k).Contains (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k) := by
  apply tailMomentBox_sound _ (by norm_num [dottiePrefixEnd])
  have h := archivedMomentMass_le_two_sqrt dottiePrefixEnd
  rw [show dottiePrefixEnd.sqrt = 37984 by decide +kernel] at h
  exact h.trans (by norm_num)

theorem referenceTailMomentBox_sound (k : ℕ) :
    (tailMomentBox 33276 20 k).Contains (signedMoment archivedLatticeCoeff 276824064 dottieSharpCenter k) :=
  tailMomentBox_sound reference_mass_le (by norm_num) k

#print axioms sharpTailMomentBox_sound
#print axioms referenceTailMomentBox_sound

end QuarticModel.DottieFixedIntervals
