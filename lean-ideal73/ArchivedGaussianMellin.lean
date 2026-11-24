import ArchivedGaussianSeries

/-! The archived theta and Mellin normalization on the field toolchain.
The equality with the absolutely convergent series is direct. -/

namespace QuarticModel

open ArithmeticFunction FieldCoefficientTransfer ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable def archivedThetaScale : ℝ := Real.sqrt 26509772707289 / Real.pi

theorem archivedThetaScale_pos : 0 < archivedThetaScale := by
  unfold archivedThetaScale
  positivity

noncomputable def archivedTheta (u : ℝ) : ℝ :=
  ∑' n : ℕ, (archivedLatticeCoeff n : ℝ) * (Real.exp (-u))^n

noncomputable def archivedMellin (w : ℂ) : ℂ :=
  mellin (fun t : ℝ => (archivedTheta (t / archivedThetaScale) : ℂ)) w

noncomputable def archivedGaussianFactor (w : ℂ) : ℂ :=
  archivedMellin w * ((archivedThetaScale : ℂ)^w)⁻¹ * (Complex.Gamma w)⁻¹

private theorem archivedScalePower_ne_zero (w : ℂ) : (archivedThetaScale : ℂ)^w ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'))

private theorem archivedQuarter_exponential_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun p => archivedQuarterWeight p * ((Real.exp (-u) ^ archivedQuarterNorm p : ℝ) : ℂ)) := by
  let f (n : ℕ) := Real.exp (-u)^n
  have hf : Summable f := by
    have hr : ‖Real.exp (-u)‖ < 1 := by
      rw [Real.norm_eq_abs, Real.abs_exp]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
    exact (hasSum_geometric_of_norm_lt_one hr).summable
  have hprod : Summable (fun p : ℕ×ℕ => f p.1 * f p.2) := by
    apply (summable_prod_of_nonneg (fun _ => mul_nonneg (by unfold f; positivity) (by unfold f; positivity))).mpr
    refine ⟨fun n => hf.mul_left (f n), ?_⟩
    simpa only [tsum_mul_left] using hf.mul_right (∑' n : ℕ, f n)
  refine hprod.of_norm_bounded (fun p => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.exp_pos _).le _)]
  calc
    _ ≤ 1 * Real.exp (-u)^archivedQuarterNorm p :=
      mul_le_mul_of_nonneg_right (archivedQuarterWeight_norm_le p) (pow_nonneg (Real.exp_pos _).le _)
    _ ≤ _ := by
      have hnorm : p.1+p.2 ≤ archivedQuarterNorm p := by
        unfold archivedQuarterNorm
        nlinarith [Nat.le_mul_self p.1, Nat.le_mul_self p.2]
      have hpow : Real.exp (-u)^archivedQuarterNorm p ≤ Real.exp (-u)^(p.1+p.2) :=
        pow_le_pow_of_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le)) hnorm
      simpa only [f, one_mul, pow_add] using hpow

theorem archivedTheta_hasSum_quarter {t : ℝ} (ht : 0 < t) :
    HasSum (fun p => archivedQuarterWeight p *
      (Real.exp (-((archivedQuarterNorm p : ℝ) / archivedThetaScale) * t) : ℂ))
      (archivedTheta (t / archivedThetaScale) : ℂ) := by
  let u := t / archivedThetaScale
  have hu : 0 < u := div_pos ht archivedThetaScale_pos
  have h := (archivedQuarter_exponential_summable hu).hasSum
  have hgroup := hasSum_group_by_archivedNorm (F := fun n => (Real.exp (-u)^n : ℝ)) h
  have hvalue : (archivedTheta u : ℂ) =
      ∑' p, archivedQuarterWeight p * ((Real.exp (-u)^archivedQuarterNorm p : ℝ) : ℂ) := by
    rw [← hgroup.tsum_eq, archivedTheta, Complex.ofReal_tsum]
    simp_rw [signedIdealCoefficients_eq_archivedLatticeCoeff, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [hvalue]
  refine h.congr_fun ?_
  intro p
  congr 2
  rw [← Real.exp_nat_mul]
  congr 1
  unfold u
  ring

theorem archivedGaussianFactor_eq_Dirichlet {w : ℂ} (hw : 1 < w.re) :
    archivedGaussianFactor w = archivedGaussianDirichlet w := by
  have hRe : 0 < w.re := zero_lt_one.trans hw
  have hGamma := Complex.Gamma_ne_zero_of_re_pos hRe
  have hscale := archivedScalePower_ne_zero w
  have hN (p : ℕ × ℕ) : 0 < (archivedQuarterNorm p : ℝ) :=
    Nat.cast_pos.mpr (archivedQuarterNorm_pos p)
  have hMellin := hasSum_mellin
    (fun p => Or.inr (div_pos (hN p) archivedThetaScale_pos)) hRe
    (fun t ht => archivedTheta_hasSum_quarter ht) (archivedQuarter_dirichlet_abs_summable hw archivedThetaScale_pos)
  have hm := (hMellin.mul_right (((archivedThetaScale : ℂ)^w)⁻¹)).mul_right (Complex.Gamma w)⁻¹
  have hterms : HasSum (fun p => archivedQuarterWeight p / (archivedQuarterNorm p : ℂ)^w)
      (archivedGaussianFactor w) := by
    refine hm.congr_fun (fun p => ?_)
    have he : ((archivedQuarterNorm p / archivedThetaScale : ℝ) : ℂ)^w *
        (archivedThetaScale : ℂ)^w = (archivedQuarterNorm p : ℂ)^w := by
      rw [← Complex.mul_cpow_ofReal_nonneg (div_pos (hN p) archivedThetaScale_pos).le
        archivedThetaScale_pos.le, ← Complex.ofReal_mul, div_mul_cancel₀ _ archivedThetaScale_pos.ne',
        Complex.ofReal_natCast]
    have hp : (archivedQuarterNorm p : ℂ)^w ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (archivedQuarterNorm_pos p).ne'))
    rw [(eq_div_iff hscale).mpr he]
    field_simp [hGamma, hscale, hp]
  exact hterms.unique (archivedGaussianDirichlet_hasSum_lattice hw)

theorem archivedGaussianFactor_hasSum {w : ℂ} (hw : 1 < w.re) :
    LSeriesHasSum signedIdealCoefficients w (archivedGaussianFactor w) := by
  rw [archivedGaussianFactor_eq_Dirichlet hw]
  exact archivedGaussianDirichlet_hasSum hw

theorem dedekindZeta_eq_archivedGaussianFactor {w : ℂ} (hw : 1 < w.re) :
    NumberField.dedekindZeta K w = riemannZeta w * chi4.LFunction w * archivedGaussianFactor w := by
  rw [archivedGaussianFactor_eq_Dirichlet hw]
  exact dedekindZeta_eq_archivedGaussianDirichlet hw

#print axioms archivedTheta_hasSum_quarter
#print axioms archivedGaussianFactor_hasSum
#print axioms dedekindZeta_eq_archivedGaussianFactor

end QuarticModel
