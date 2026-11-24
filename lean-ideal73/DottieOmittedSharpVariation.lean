import ArchivedDottieOmittedBudget
import DottieSharpCircleMoments
import DottieSignedBlockVariation

/-! Transfer the signed block estimates to the exact sharp part of the
archived Gaussian omitted sum. A block contains norms h+1 through h+len. -/

namespace QuarticModel

open Complex Finset
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection
open private signedTerm signedTerm_shift from DottieSignedMoments
open private dottieSharpSide from ArchivedDottieTailPartition

noncomputable def dottieNormBlock (h len : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ range len, signedTerm archivedLatticeCoeff w (h + i)

theorem dottie_norm_block_eq_Ioc (h len : ℕ) (w : ℂ) :
    dottieNormBlock h len w =
      ∑ n ∈ Ioc h (h + len), (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w) := by
  have hset : Ioc h (h + len) = Ico (h + 1) (h + len + 1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range, dottieNormBlock,
    show h + len + 1 - (h + 1) = len by omega]
  apply sum_congr rfl
  intro i _
  unfold signedTerm
  rw [show h + 1 + i = h + i + 1 by omega]

private theorem sharpSide_eq_factor_mul (w : ℂ) {n : ℕ} (hn : 0 < n) :
    dottieSharpSide w n =
      dottieSharpFactor w * ((archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w)) := by
  rw [dottieSharpSide, if_neg hn.ne', dottieSharpFactor, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg (α := ℝ) n),
    Complex.ofReal_natCast, Complex.cpow_neg]
  ring

theorem dottie_omitted_sharp_eq_norm_block (w : ℂ) :
    dottieOmittedSharpBlock w =
      dottieSharpFactor w * dottieNormBlock dottiePrefixEnd (dottieOmittedSharpEnd-dottiePrefixEnd) w +
      conj (dottieSharpFactor (1-conj w) *
        dottieNormBlock dottiePrefixEnd (dottieOmittedSharpEnd-dottiePrefixEnd) (1-conj w)) := by
  have hcut : dottiePrefixEnd ≤ dottieOmittedSharpEnd := by decide +kernel
  have hsum (z : ℂ) : (∑ n ∈ Ioc dottiePrefixEnd dottieOmittedSharpEnd, dottieSharpSide z n) =
      dottieSharpFactor z * dottieNormBlock dottiePrefixEnd (dottieOmittedSharpEnd-dottiePrefixEnd) z := by
    rw [dottie_norm_block_eq_Ioc, Nat.add_sub_of_le hcut, Finset.mul_sum]
    exact sum_congr rfl (fun n hn =>
      sharpSide_eq_factor_mul z ((Nat.zero_le _).trans_lt (mem_Ioc.mp hn).1))
  unfold dottieOmittedSharpBlock
  rw [Finset.sum_add_distrib, ← map_sum, hsum, hsum]

noncomputable def dottieBlockLogWidth (h len : ℕ) : ℝ :=
  Real.log (↑(h + len) : ℝ) - Real.log (h : ℝ)

private theorem dottie_block_log_width_succ_monotone (h : ℕ) :
    Monotone (fun i => dottieBlockLogWidth h (i+1)) := by
  intro i j hij
  apply sub_le_sub_right
  exact Real.log_le_log (by positivity) (by exact_mod_cast (show h+(i+1) ≤ h+(j+1) by omega))

private theorem dottie_block_log_width_one_nonneg {h : ℕ} (hh : 0 < h) :
    0 ≤ dottieBlockLogWidth h 1 := by
  apply sub_nonneg.mpr
  exact Real.log_le_log (by exact_mod_cast hh) (by exact_mod_cast (Nat.le_succ h))

private theorem dottie_signed_term_anchor {h : ℕ} (hh : 0 < h) (s z : ℂ) (i : ℕ) :
    signedTerm archivedLatticeCoeff (s+z) (h+i) =
      (h : ℂ)^(-z) * (Complex.exp ((-z)*(dottieBlockLogWidth h (i+1) : ℂ)) *
        signedTerm archivedLatticeCoeff s (h+i)) := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [signedTerm_shift, Complex.cpow_def_of_ne_zero hh', ← Complex.natCast_log, ← mul_assoc,
    ← Complex.exp_add]
  have hp : (Real.log (h : ℝ) : ℂ) * (-z) + (-z) * (dottieBlockLogWidth h (i+1) : ℂ) =
      z * ((-Real.log (↑(h+i+1) : ℝ) : ℝ) : ℂ) := by
    unfold dottieBlockLogWidth
    rw [show h+(i+1) = h+i+1 by omega]
    push_cast
    ring
  rw [hp]
  simpa only [Nat.cast_add, Nat.cast_one] using
    mul_comm (signedTerm archivedLatticeCoeff s (h+i))
      (Complex.exp (z * ((-Real.log (↑(h+i+1) : ℝ) : ℝ) : ℂ)))

theorem dottie_norm_block_shift_error {h : ℕ} (hh : 0 < h) (last : ℕ) (s z : ℂ) (A : ℝ)
    (hprefix : ∀ k ≤ last+1, ‖dottieNormBlock h k s‖ ≤ A) :
    let L := dottieBlockLogWidth h (last+1)
    ‖dottieNormBlock h (last+1) (s+z) - (h : ℂ)^(-z)*dottieNormBlock h (last+1) s‖ ≤
      ‖(h : ℂ)^(-z)‖ * (2*A*‖z‖*L*Real.exp (‖z‖*L)) := by
  let c := fun i => signedTerm archivedLatticeCoeff s (h+i)
  let u := fun i => dottieBlockLogWidth h (i+1)
  let L := dottieBlockLogWidth h (last+1)
  change ‖_‖ ≤ ‖_‖ * (2*A*‖z‖*L*Real.exp (‖z‖*L))
  have hnest (i : ℕ) :
      signedTerm archivedLatticeCoeff (s+z) (h+i) =
        (h : ℂ)^(-z) * (Complex.exp ((-z)*(u i : ℂ))*c i) :=
    dottie_signed_term_anchor hh s z i
  have heq :
      dottieNormBlock h (last+1) (s+z) - (h : ℂ)^(-z)*dottieNormBlock h (last+1) s =
        (h : ℂ)^(-z) * ∑ i ∈ range (last+1), (Complex.exp ((-z)*(u i : ℂ))-1)*c i := by
    simp only [dottieNormBlock, hnest, ← Finset.mul_sum]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine sum_congr rfl (fun i _ => ?_)
    change _ * c i - c i = _
    ring
  rw [heq, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_neg] using
    dottie_signed_block_exp_displacement c u last A L (-z) (dottie_block_log_width_succ_monotone h)
      (dottie_block_log_width_one_nonneg hh) le_rfl hprefix

/-- The frozen norm polynomial with its exact completion factor and the
coarse phase from the first excluded norm h. -/
noncomputable def dottieAnchoredSharpSide (h len : ℕ) (s w : ℂ) : ℂ :=
  dottieSharpFactor w * ((h : ℂ)^(-(w-s)) * dottieNormBlock h len s)

noncomputable def dottieSharpSideVariation (h : ℕ) (s w : ℂ) : ℝ :=
  ‖dottieSharpFactor w‖ * ‖(h : ℂ)^(-(w-s))‖

theorem dottie_norm_block_completed_shift_error {h : ℕ} (hh : 0 < h)
    (last : ℕ) (s w : ℂ) (A : ℝ)
    (hprefix : ∀ k ≤ last+1, ‖dottieNormBlock h k s‖ ≤ A) :
    let L := dottieBlockLogWidth h (last+1)
    ‖dottieSharpFactor w * dottieNormBlock h (last+1) w -
      dottieAnchoredSharpSide h (last+1) s w‖ ≤
        dottieSharpSideVariation h s w * (2*A*‖w-s‖*L*Real.exp (‖w-s‖*L)) := by
  have hb := dottie_norm_block_shift_error hh last s (w-s) A hprefix
  dsimp only at hb ⊢
  rw [show s+(w-s) = w by ring] at hb
  rw [dottieAnchoredSharpSide, ← mul_sub, norm_mul, dottieSharpSideVariation, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

open private dottie_sharp_reflected_offset from DottieSharpCircleMoments

/-- One measured bound on the signed prefixes of the exact lower omitted
block controls the sharp contribution on the whole circle. The middle
smoothed block has its own signed budget. -/
theorem dottie_omitted_sharp_circle_anchored_error {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (A : ℝ)
    (hprefix : ∀ k ≤ dottieOmittedSharpEnd-dottiePrefixEnd,
      ‖dottieNormBlock dottiePrefixEnd k dottieSharpCenter‖ ≤ A) :
    let h := dottiePrefixEnd
    let len := dottieOmittedSharpEnd-dottiePrefixEnd
    let s := dottieSharpCenter
    let L := dottieBlockLogWidth h len
    let t : ℝ := 67/2048
    let w' := 1-conj w
    ‖dottieOmittedSharpBlock w -
        (dottieAnchoredSharpSide h len s w + conj (dottieAnchoredSharpSide h len s w'))‖ ≤
      (dottieSharpSideVariation h s w + dottieSharpSideVariation h s w') *
        (2*A*t*L*Real.exp (t*L)) := by
  intro h len s L t w'
  have hH : 0 < h := by norm_num [h, dottiePrefixEnd]
  have hlen : len ≠ 0 := by decide +kernel
  have hA : 0 ≤ A := (norm_nonneg _).trans (hprefix 0 (Nat.zero_le _))
  have hL : 0 ≤ L := by
    apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast hH)
      (by exact_mod_cast (Nat.le_add_right h len))
  have hdist : ‖w-s‖ ≤ t := dottie_sharp_circle_offset hw
  have hdist' : ‖w'-s‖ ≤ t := (dottie_sharp_reflected_offset w).le.trans hdist
  have bound (v : ℂ) (hd : ‖v-s‖ ≤ t) :
      ‖dottieSharpFactor v * dottieNormBlock h len v -
        dottieAnchoredSharpSide h len s v‖ ≤
          dottieSharpSideVariation h s v * (2*A*t*L*Real.exp (t*L)) := by
    obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero hlen
    have hlen_eq : len = last+1 := hlast
    have hB := dottie_norm_block_completed_shift_error hH last s v A (by
      intro k hk
      exact hprefix k (hk.trans_eq hlen_eq.symm))
    dsimp only at hB
    rw [← hlen_eq] at hB
    refine hB.trans ?_
    unfold dottieSharpSideVariation
    have hexp : Real.exp (‖v-s‖*L) ≤ Real.exp (t*L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd hL)
    gcongr
  rw [dottie_omitted_sharp_eq_norm_block, add_sub_add_comm, ← map_sub]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, add_mul]
  exact add_le_add (bound w hdist) (bound w' hdist')

#print axioms dottie_norm_block_eq_Ioc
#print axioms dottie_omitted_sharp_eq_norm_block
#print axioms dottie_norm_block_shift_error
#print axioms dottie_norm_block_completed_shift_error
#print axioms dottie_omitted_sharp_circle_anchored_error

end QuarticModel
