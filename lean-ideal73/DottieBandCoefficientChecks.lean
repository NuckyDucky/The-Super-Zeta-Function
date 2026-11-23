import DottieDyadicCoefficient
import DottieSymmetricScore
import DottieWitnessPairBlocks

/-! Exact zero witnesses for the original signed coefficients. The
generator supplies a coprime divisor and optionally a power of two. -/

namespace QuarticModel

open Finset
open private onArchivedShell from ArchivedQuarticLatticeCoefficients
open private axisTerm positiveTerm pairedTerm positiveNorm positiveSign swapCoordinates
  from DottieSymmetricScore
open private witnessedRowSign witnessedRowSign_correct from DottieWitnessPairBlocks
set_option autoImplicit false

private theorem nat_sq_mod_four (n : ℕ) : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases n % 4 <;> decide

theorem archivedLatticeCoeff_eq_zero_of_mod_four {n : ℕ} (hn : n % 4 = 3) :
    archivedLatticeCoeff n = 0 := by
  unfold archivedLatticeCoeff
  apply Finset.sum_eq_zero
  intro j _
  rw [archivedLatticeRow, if_neg]
  intro hs
  unfold onArchivedShell at hs
  rw [← hs, Nat.add_mod] at hn
  rcases nat_sq_mod_four (j+1) with h | h <;>
    rcases nat_sq_mod_four (n-(j+1)^2).sqrt with h' | h' <;>
    simp [h,h'] at hn

theorem archivedLatticeCoeff_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m.Coprime n) :
    archivedLatticeCoeff (m*n) = archivedLatticeCoeff m*archivedLatticeCoeff n := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_mul, archivedLatticeCoeff_eq_signedIdealNormSum _ (Nat.mul_pos hm hn).ne',
    archivedLatticeCoeff_eq_signedIdealNormSum _ hm.ne',
    archivedLatticeCoeff_eq_signedIdealNormSum _ hn.ne', signedIdealNormSum_mul_of_coprime h]

theorem archivedLatticeCoeff_two_pow_mul (k n : ℕ) :
    archivedLatticeCoeff (2^k*n) = archivedLatticeCoeff n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Nat.mul_assoc, archivedLatticeCoeff_two_mul, ih]

theorem dottie_band_coefficient_zero_of_coprime_witness {n m r k : ℕ}
    (he : n = 2^k*(m*r)) (hm : 0 < m) (hr : 0 < r) (hc : m.Coprime r)
    (hz : archivedLatticeCoeff m = 0) : archivedLatticeCoeff n = 0 := by
  rw [he, archivedLatticeCoeff_two_pow_mul, archivedLatticeCoeff_mul_of_coprime hm hr hc, hz, zero_mul]

private theorem dottie_axis_sign_product (a : ℤ) :
    dottieRowSign (a^2) 0 = dottieRowSign a 0*dottieRowSign a 0 := by
  simp only [dottieRowSign_eq_archivedGaussianSign]
  have he : (⟨a^2,0⟩ : GaussianInt) = ⟨a,0⟩*⟨a,0⟩ := by
    apply Zsqrtd.ext <;> simp [pow_two]
  rw [he,archivedGaussianSign_mul]

private theorem dottie_swap_sign_product (a b : ℤ) :
    dottieRowSign a b*dottieRowSign b a = dottieRowSign (a^2+b^2) 0 := by
  have hi : IsUnit (⟨0,1⟩ : GaussianInt) :=
    isUnit_iff_dvd_one.mpr ⟨⟨0,-1⟩,by decide +kernel⟩
  have he : (⟨a,b⟩ : GaussianInt)*⟨b,a⟩ = ⟨a^2+b^2,0⟩*⟨0,1⟩ := by
    apply Zsqrtd.ext <;> simp [pow_two]
    ring
  simp only [dottieRowSign_eq_archivedGaussianSign,← archivedGaussianSign_mul]
  rw [he,archivedGaussianSign_mul,archivedGaussianSign_unit _ hi,mul_one]

/-- If the rational norm has negative sign, each conjugate pair of
Gaussian representations cancels under the archived character. -/
theorem archivedLatticeCoeff_eq_zero_of_rational_sign {n : ℕ}
    (hn : 0 < n) (hneg : dottieRowSign n 0 = -1) : archivedLatticeCoeff n = 0 := by
  let f (m : ℕ) : ℤ := if m = n then 1 else 0
  have he : dottieSymmetricScore n f = archivedLatticeCoeff n := by
    rw [dottieSymmetricScore_eq_dottieTriangleScore,dottieTriangleScore_eq_archivedLatticeCoeff]
    have hs : n-1+1 = n := by omega
    rw [Finset.sum_eq_single (n-1)]
    · simp [f,hs]
    · intro i _ hi
      have hh : i+1 ≠ n := by omega
      simp [f,hh]
    · intro hc
      exact (hc (mem_range.mpr (by omega))).elim
  have haxis (a : ℕ) : axisTerm f a = 0 := by
    by_cases h : (a+1)^2 = n
    · have ha : (((a : ℤ)+1)^2) = (n : ℤ) := by exact_mod_cast h
      have hs := dottie_axis_sign_product ((a : ℤ)+1)
      rw [ha,hneg] at hs
      nlinarith only [hs,sq_nonneg (dottieRowSign ((a : ℤ)+1) 0)]
    · simp [axisTerm,f,h]
  have hdiag (a : ℕ) : positiveTerm f ⟨a,a⟩ = 0 := by
    by_cases h : (a+1)^2+(a+1)^2 = n
    · have ha : (((a : ℤ)+1)^2+((a : ℤ)+1)^2) = (n : ℤ) := by exact_mod_cast h
      have hs := dottie_swap_sign_product ((a : ℤ)+1) ((a : ℤ)+1)
      rw [ha,hneg] at hs
      nlinarith only [hs,sq_nonneg (dottieRowSign ((a : ℤ)+1) ((a : ℤ)+1))]
    · simp [positiveTerm,positiveNorm,f,h]
  have hpair (a b : ℕ) : pairedTerm f ⟨a,b⟩ = 0 := by
    by_cases h : (a+1)^2+(b+1)^2 = n
    · have ha : (((a : ℤ)+1)^2+((b : ℤ)+1)^2) = (n : ℤ) := by exact_mod_cast h
      have hs := dottie_swap_sign_product ((a : ℤ)+1) ((b : ℤ)+1)
      rw [ha,hneg] at hs
      obtain h | h := Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hs
      all_goals simp [pairedTerm,positiveSign,swapCoordinates,h.1,h.2]
    · simp [pairedTerm,positiveNorm,f,h]
  rw [← he]
  simp only [dottieSymmetricScore,haxis,hdiag,hpair,ite_self,sum_const_zero,add_zero]

/-- A checked zero row uses a coprime divisor. A missing sign code selects
the mod-four test, and a supplied code checks the rational character. -/
def dottieBandZeroCheck (n twos m : ℕ) (signCode : Option ℕ) : Bool :=
  let r := n/(2^twos*m)
  decide (n = 2^twos*(m*r) ∧ 0 < m ∧ 0 < r ∧ m.Coprime r) &&
    match signCode with
    | none => decide (m % 4 = 3)
    | some code => decide (witnessedRowSign m 0 code = some (-1))

theorem dottie_band_zero_check_sound {n twos m : ℕ} {signCode : Option ℕ}
    (h : dottieBandZeroCheck n twos m signCode = true) : archivedLatticeCoeff n = 0 := by
  simp only [dottieBandZeroCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨he,hm,hr,hc⟩,hs⟩ := h
  apply dottie_band_coefficient_zero_of_coprime_witness he hm hr hc
  cases signCode with
  | none => exact archivedLatticeCoeff_eq_zero_of_mod_four (of_decide_eq_true hs)
  | some code =>
    exact archivedLatticeCoeff_eq_zero_of_rational_sign hm
      (witnessedRowSign_correct (code := code) (of_decide_eq_true hs))

/-- The first eight coefficients of the original retained band are zero.
These concrete reductions exercise both witness types and dyadic reuse. -/
theorem dottie_retained_band_first_eight_zero (i : ℕ) (hi : i < 8) :
    archivedLatticeCoeff (1854467118035498894+i) = 0 := by
  interval_cases i
  · exact dottie_band_zero_check_sound (twos := 1) (m := 927233559017749447)
      (signCode := none) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498895)
      (signCode := none) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 4) (m := 115904194877218681)
      (signCode := some 886705336) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498897)
      (signCode := some 787918361) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 1) (m := 927233559017749449)
      (signCode := some 721930297) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498899)
      (signCode := none) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 2) (m := 17)
      (signCode := some 522346910) (by decide +kernel)
  · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498901)
      (signCode := some 384917740) (by decide +kernel)

#print axioms archivedLatticeCoeff_eq_zero_of_mod_four
#print axioms archivedLatticeCoeff_mul_of_coprime
#print axioms archivedLatticeCoeff_two_pow_mul
#print axioms dottie_band_coefficient_zero_of_coprime_witness
#print axioms archivedLatticeCoeff_eq_zero_of_rational_sign
#print axioms dottie_band_zero_check_sound
#print axioms dottie_retained_band_first_eight_zero

end QuarticModel
