import DottiePreciseHeight
import DottieHeightPerturbation
import DottieSharpCircleMoments

/-! Move every exact signed moment to one common rational height. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open private signedTerm signedTerm_shift signedTerm_norm from DottieSignedMoments
set_option autoImplicit false

noncomputable def dottieMomentRationalHeight : ℝ := 4526119322477.94539331920732885695

theorem dottieMomentRationalHeight_error : |dottieHeight-dottieMomentRationalHeight| ≤ 1/10^19 := by
  obtain ⟨h₁,h₂⟩ := dottieHeight_precise_enclosure
  unfold dottieMomentRationalHeight
  exact abs_le.mpr ⟨by linarith only [h₁],by linarith only [h₂]⟩

private theorem log_lt_twenty_two {n : ℕ} (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) :
    Real.log (n:ℝ) < 22 := by
  have hp : (2.7 : ℝ)^22 ≤ Real.exp 22 := by
    rw [show (22:ℝ) = (22:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have hq : (n:ℝ) ≤ dottiePrefixEnd := by exact_mod_cast hN
  exact (Real.log_lt_iff_lt_exp (by exact_mod_cast hn)).mpr
    ((hq.trans_lt (by norm_num [dottiePrefixEnd] : (dottiePrefixEnd:ℝ) < (2.7:ℝ)^22)).trans_le hp)

private theorem signedTerm_high_phase_bound (a : ℕ → ℤ) (n : ℕ) (u t : ℝ)
    (hn : n+1 ≤ dottiePrefixEnd) :
    ‖signedTerm a (1/2+(u:ℂ)*I) n-signedTerm a (1/2+(t:ℂ)*I) n‖ ≤
      (|(a (n+1):ℝ)|/Real.sqrt (n+1))*(22*|u-t|) := by
  let l := Real.log ((n:ℝ)+1)
  have hl : 0 ≤ l := Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  have hlog : l ≤ 22 := by
    simpa only [l,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using (log_lt_twenty_two (Nat.succ_pos n) hn).le
  have hphase (v : ℝ) : ((v:ℂ)*I)*((-l:ℝ):ℂ) = ((-(v*l):ℝ):ℂ)*I := by push_cast; ring
  rw [signedTerm_shift a (1/2) ((u:ℂ)*I) n,signedTerm_shift a (1/2) ((t:ℂ)*I) n,
    hphase u,hphase t,← mul_sub,norm_mul,signedTerm_norm (by norm_num : (1/2:ℂ).re = 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (dottie_unit_phase_distance (-(u*l)) (-(t*l))).trans ?_
  rw [show -(u*l)- -(t*l) = -(l*(u-t)) by ring,abs_neg,abs_mul,abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_right hlog (abs_nonneg _)

theorem signed_moment_height_bound (a : ℕ → ℤ) {N : ℕ} (hN : N ≤ dottiePrefixEnd)
    (u t : ℝ) (k : ℕ) :
    ‖signedMoment a N (1/2+(u:ℂ)*I) k-signedMoment a N (1/2+(t:ℂ)*I) k‖ ≤
      signedMomentMass a N*(22*|u-t|)*(32:ℝ)^k := by
  unfold signedMoment
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [signedMomentMass,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  let l := Real.log ((n:ℝ)+1)
  let b := ((-l:ℝ):ℂ)^k/(k.factorial:ℂ)
  have hlog : 0 ≤ l ∧ l ≤ 22 := ⟨Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) n]),by
    simpa only [l,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using
      (log_lt_twenty_two (Nat.succ_pos n) ((mem_range.mp hn).trans_le hN)).le⟩
  have hb : ‖b‖ ≤ (32:ℝ)^k := by
    dsimp only [b]
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg hlog.1,Complex.norm_natCast]
    have hfac : (1:ℝ) ≤ (k.factorial:ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos k))
    calc
      _ ≤ l^k := (div_le_iff₀ (by linarith only [hfac])).2 (by
        simpa using mul_le_mul_of_nonneg_left hfac (pow_nonneg hlog.1 _))
      _ ≤ _ := pow_le_pow_left₀ hlog.1 (hlog.2.trans (by norm_num)) _
  change ‖signedTerm a (1/2+(u:ℂ)*I) n*(((-l:ℝ):ℂ)^k)/(k.factorial:ℂ)-
      signedTerm a (1/2+(t:ℂ)*I) n*(((-l:ℝ):ℂ)^k)/(k.factorial:ℂ)‖ ≤ _
  rw [show signedTerm a (1/2+(u:ℂ)*I) n*(((-l:ℝ):ℂ)^k)/(k.factorial:ℂ)-
      signedTerm a (1/2+(t:ℂ)*I) n*(((-l:ℝ):ℂ)^k)/(k.factorial:ℂ) =
      (signedTerm a (1/2+(u:ℂ)*I) n-signedTerm a (1/2+(t:ℂ)*I) n)*b by dsimp only [b]; ring,
    norm_mul]
  exact mul_le_mul
    (signedTerm_high_phase_bound a n u t ((mem_range.mp hn).trans_le hN)) hb (norm_nonneg _) (by positivity)

theorem dottie_moment_exact_height_error {N : ℕ} (hN : N ≤ dottiePrefixEnd) (k : ℕ) :
    ‖signedMoment archivedLatticeCoeff N dottieSharpCenter k-
      signedMoment archivedLatticeCoeff N (1/2+(dottieMomentRationalHeight:ℂ)*I) k‖ ≤
      (32:ℝ)^k/(5*10^12) := by
  have hmass : signedMomentMass archivedLatticeCoeff N ≤ 76000 := by
    have h := archivedMomentMass_le_two_sqrt N
    have h' := (Nat.sqrt_le_sqrt hN).trans_eq (show dottiePrefixEnd.sqrt = 37984 by decide +kernel)
    have hs : (N.sqrt:ℝ) ≤ 37984 := by exact_mod_cast h'
    linarith only [h,hs]
  have hb := signed_moment_height_bound archivedLatticeCoeff hN dottieHeight dottieMomentRationalHeight k
  refine hb.trans ?_
  calc
    _ ≤ (76000*(22*(1/10^19)))*(32:ℝ)^k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by norm_num) _)
      exact mul_le_mul hmass (mul_le_mul_of_nonneg_left dottieMomentRationalHeight_error (by norm_num))
        (by positivity) (by norm_num)
    _ ≤ (1/(5*10^12):ℝ)*(32:ℝ)^k :=
      mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (by norm_num) _)
    _ = _ := by ring

#print axioms signed_moment_height_bound
#print axioms dottie_moment_exact_height_error

end QuarticModel
