import GaussianDirichletVerticalGrowth
import GaussianVaughanHigherContinuation

/-! Uniform growth bounds for the four filtered factors and the actual
completed Gaussian prime continuation. -/

namespace AlpogeSuperZeta

open Complex DirichletCharacter Filter Metric Set
open scoped Classical Topology

noncomputable section

private abbrev dyadicDifference := gaussianScaleDifference (1 / 2)

private theorem norm_dyadicExp_le {z : ℂ} (hz : 3 / 8 ≤ z.re) :
    ‖Complex.exp ((((1 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ))‖ ≤ 2 := by
  simp only [Complex.norm_exp, mul_re, ofReal_im, mul_zero, sub_zero, sub_re, ofReal_re]
  calc
    _ ≤ Real.exp (Real.log 2) := by
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith [mul_nonneg hlog (sub_nonneg.mpr hz)]
    _ = 2 := Real.exp_log (by norm_num)

private theorem norm_dyadicDifference_le {z : ℂ} (hz : 3 / 8 ≤ z.re) :
    ‖dyadicDifference z‖ ≤ 3 := by
  unfold dyadicDifference gaussianScaleDifference
  exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [norm_dyadicExp_le hz])

private theorem dyadicDifference_hasDerivAt (z : ℂ) :
    HasDerivAt dyadicDifference
      ((Real.log 2 : ℂ) * Complex.exp ((((1 / 2 : ℝ) : ℂ) - z) * (Real.log 2 : ℂ))) z := by
  let f : ℂ → ℂ := fun v => (((1 / 2 : ℝ) : ℂ) - v) * (Real.log 2 : ℂ)
  have hlin : HasDerivAt f (-(Real.log 2 : ℂ)) z := by
    simpa only [f, id, neg_one_mul] using
      ((hasDerivAt_id z).const_sub (((1 / 2 : ℝ) : ℂ))).mul_const (Real.log 2 : ℂ)
  have he := ((Complex.hasDerivAt_exp (f z)).comp z hlin).const_sub (1 : ℂ)
  change HasDerivAt (fun v => 1 - Complex.exp (f v)) ((Real.log 2 : ℂ) * Complex.exp (f z)) z
  have hs : -(Complex.exp (f z) * -(Real.log 2 : ℂ)) = (Real.log 2 : ℂ) * Complex.exp (f z) := by ring
  rwa [hs] at he

private theorem norm_dyadicDifference_dslope_le {z : ℂ} (hz : 3 / 8 ≤ z.re) :
    ‖dslope dyadicDifference ((1 / 2 : ℝ) : ℂ) z‖ ≤ 2 * Real.log 2 := by
  let c : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hc : 3 / 8 ≤ c.re := by norm_num [c]
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hderiv (v : ℂ) (hv : 3 / 8 ≤ v.re) : ‖deriv dyadicDifference v‖ ≤ 2 * Real.log 2 := by
    rw [(dyadicDifference_hasDerivAt v).deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, mul_comm 2]
    exact mul_le_mul_of_nonneg_left (norm_dyadicExp_le hv) hlog
  change ‖dslope dyadicDifference c z‖ ≤ _
  by_cases hcz : z = c
  · subst z
    rw [dslope_same]
    exact hderiv c hc
  have hb : ‖dyadicDifference z - dyadicDifference c‖ ≤ (2 * Real.log 2) * ‖z - c‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := dyadicDifference)
      (s := {v : ℂ | 3 / 8 ≤ v.re}) (x := c) (y := z)
      (fun v _ => (dyadicDifference_hasDerivAt v).differentiableAt)
      (fun v hv => hderiv v hv) (convex_halfSpace_re_ge (3 / 8)) hc hz
  rw [dslope_of_ne _ hcz, slope_def_module, norm_smul, norm_inv, mul_comm,
    ← div_eq_mul_inv]
  exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hcz))).mpr hb

private theorem norm_filteredDirichlet_le_logDeriv {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 3 / 8 ≤ z.re) :
    ‖archivedGaussianFilteredDirichletLog χ z‖ ≤
      3 * ‖logDeriv (regularDirichlet χ) (2 * z)‖ + Real.log 2 := by
  have hD := norm_dyadicDifference_le hz
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  by_cases hχ : χ = 1
  · have he : archivedGaussianFilteredDirichletLog χ z =
        dyadicDifference z * (-logDeriv (regularDirichlet χ) (2 * z)) +
          dslope dyadicDifference ((1 / 2 : ℝ) : ℂ) z / 2 := by
      rw [archivedGaussianFilteredDirichletLog_principal χ z hχ, regularDirichlet, if_pos hχ]
    have hs : ‖dslope dyadicDifference ((1 / 2 : ℝ) : ℂ) z / 2‖ ≤ Real.log 2 := by
      rw [norm_div, norm_ofNat]
      linarith [norm_dyadicDifference_dslope_le hz]
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add ?_ hs)
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_right hD (norm_nonneg _)
  · have he : archivedGaussianFilteredDirichletLog χ z =
        dyadicDifference z * (-logDeriv (regularDirichlet χ) (2 * z)) := by
      simp only [archivedGaussianFilteredDirichletLog, regularDirichlet, if_neg hχ]
    rw [he, norm_mul, norm_neg]
    exact (mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_add_of_nonneg_right hlog)

/-- The principal correction does not change the logarithmic height bound
for the doubled, filtered readings on the Mellin contour. -/
theorem filteredDirichletLog_strip (hDir : DirichletLZerosOnLine) (N : ℕ) [NeZero N] :
    ∃ C > 0, ∀ (χ : DirichletCharacter ℂ N) (z : ℂ), 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      ‖archivedGaussianFilteredDirichletLog χ z‖ ≤ C * (1 + Real.log (1 + 2 * |z.im|)) := by
  obtain ⟨C, hC, hbd⟩ := rationalDirichlet_logDeriv_strip hDir N
  have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨3 * C + Real.log 2, by linarith, fun χ z hz₁ hz₂ => ?_⟩
  have hre : (2 * z).re = 2 * z.re := by simp [mul_re]
  have him : |(2 * z).im| = 2 * |z.im| := by simp [mul_im, abs_mul]
  have hL := hbd χ (2 * z) (by linarith) (by linarith)
  rw [him] at hL
  have hlog₀ : 0 ≤ Real.log (1 + 2 * |z.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  refine (norm_filteredDirichlet_le_logDeriv χ hz₁).trans ?_
  nlinarith [mul_nonneg hlog hlog₀]

private theorem norm_four_readings_add_correction_le {a b c d M U R : ℂ} {V D : ℝ}
    (ha : ‖a‖ ≤ V) (hb : ‖b‖ ≤ V) (hc : ‖c‖ ≤ V) (hd : ‖d‖ ≤ V)
    (hU : ‖U‖ ≤ 3) (hR : ‖R‖ ≤ D) :
    ‖M * (a + b + c - d) + (U * M) * R‖ ≤ (4 * V + 3 * D) * ‖M‖ := by
  have h₂ : ‖a + b‖ ≤ V + V := (norm_add_le _ _).trans (add_le_add ha hb)
  have h₃ : ‖a + b + c‖ ≤ V + V + V := (norm_add_le _ _).trans (add_le_add h₂ hc)
  have h₄ : ‖a + b + c - d‖ ≤ 4 * V :=
    (norm_sub_le _ _).trans ((add_le_add h₃ hd).trans (by linarith))
  have hE : ‖U * R‖ ≤ 3 * D := by
    rw [norm_mul]
    exact mul_le_mul hU hR (norm_nonneg _) (by norm_num)
  rw [show M * (a + b + c - d) + (U * M) * R = M * ((a + b + c - d) + U * R) by ring,
    norm_mul, mul_comm (‖M‖)]
  exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add h₄ hE)) (norm_nonneg _)

/-- Bound the archived higher-power continuation by its theta Mellin
factor times a uniform logarithmic height allowance. -/
theorem archivedGaussianVaughanHigherMellin_strip (hDir : DirichletLZerosOnLine) :
    ∃ C > 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      ‖archivedGaussianVaughanHigherMellin z‖ ≤
        C * (1 + Real.log (1 + 2 * |z.im|)) * ‖QuarticModel.archivedMellin (z / 7) / 7‖ := by
  obtain ⟨C, hC, hf⟩ := filteredDirichletLog_strip hDir archivedGaussianRationalLevel
  obtain ⟨D, hD, hg⟩ := archivedGaussianVaughanHigherCorrection_uniform
  refine ⟨4 * C + 3 * D, by linarith, fun z hz₁ hz₂ => ?_⟩
  let A := 1 + Real.log (1 + 2 * |z.im|)
  let M := QuarticModel.archivedMellin (z / 7) / 7
  have hA : 1 ≤ A := by
    dsimp [A]
    have hlog : 0 ≤ Real.log (1 + 2 * |z.im|) :=
      Real.log_nonneg (by linarith [abs_nonneg z.im])
    linarith
  have h := norm_four_readings_add_correction_le
    (hf 1 z hz₁ hz₂) (hf archivedGaussianRationalChi4 z hz₁ hz₂)
    (hf archivedGaussianNormCharacter z hz₁ hz₂)
    (hf (archivedGaussianRationalChi4 * archivedGaussianNormCharacter) z hz₁ hz₂)
    (M := M) (norm_dyadicDifference_le hz₁) (hg z hz₁)
  have hB : (4 * (C * A) + 3 * D) * ‖M‖ ≤ ((4 * C + 3 * D) * A) * ‖M‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hA)]
  change _ ≤ ((4 * C + 3 * D) * A) * ‖M‖
  exact h.trans hB


/-- The contribution to the completed-prime contour has no Gaussian
logarithmic derivative. The remaining Gaussian value and derivative
multiply the decaying theta factor directly. -/
theorem archivedGaussianVaughanCompletedPrime_strip_envelope (hDir : DirichletLZerosOnLine) :
    ∃ C > 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      ‖archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin z‖ ≤
        ‖QuarticModel.archivedMellin (z / 7) / 7‖ *
          (3 * ‖deriv QuarticModel.archivedGaussianFactor z‖ +
            C * (1 + Real.log (1 + 2 * |z.im|)) * ‖QuarticModel.archivedGaussianFactor z‖) := by
  obtain ⟨C, hC, hU⟩ := archivedGaussianVaughanHigherMellin_strip hDir
  refine ⟨C, hC, fun z hz₁ hz₂ => ?_⟩
  unfold archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanMultiplier
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, norm_neg]
  have hD := norm_dyadicDifference_le hz₁
  have hV := hU z hz₁ hz₂
  calc
    _ ≤ (3 * ‖QuarticModel.archivedMellin (z / 7) / 7‖) *
          ‖deriv QuarticModel.archivedGaussianFactor z‖ +
        ‖QuarticModel.archivedGaussianFactor z‖ *
          (C * (1 + Real.log (1 + 2 * |z.im|)) * ‖QuarticModel.archivedMellin (z / 7) / 7‖) :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
        (norm_nonneg _)) (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
    _ = _ := by ring

#check filteredDirichletLog_strip
#print axioms filteredDirichletLog_strip
#check archivedGaussianVaughanHigherMellin_strip
#print axioms archivedGaussianVaughanHigherMellin_strip
#check archivedGaussianVaughanCompletedPrime_strip_envelope
#print axioms archivedGaussianVaughanCompletedPrime_strip_envelope

end
end AlpogeSuperZeta
