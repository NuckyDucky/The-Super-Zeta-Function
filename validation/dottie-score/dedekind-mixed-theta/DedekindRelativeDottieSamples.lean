import DedekindRelativeDottie
import DedekindMixedThetaSampleCover
import DedekindSolvableClosure

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set NumberField MeasureTheory SuperZeta.StirlingCorrection
open DedekindZetaZeroFree.AbelianQuotient
open scoped ComplexConjugate
open private dottie_closedBall_avoids_poles from DedekindMixedThetaFiniteSamples
open private commutator_fixedField_isAbelian from DedekindSolvableQuotient

noncomputable section

private theorem norm_le_sample_budget {z sample : ℂ} {error : ℝ}
    (h : ‖z - sample‖ ≤ error) : ‖z‖ ≤ ‖sample‖ + error := by
  calc
    ‖z‖ = ‖sample + (z - sample)‖ := congrArg norm (by ring)
    _ ≤ ‖sample‖ + ‖z - sample‖ := norm_add_le _ _
    _ ≤ ‖sample‖ + error := add_le_add le_rfl h

/-- Two absolute sample errors bound the error in the ordered cross product. -/
theorem norm_cross_product_sub_le {A B A₀ B₀ : ℂ} {eA eB : ℝ}
    (hA : ‖A - A₀‖ ≤ eA) (hB : ‖B - B₀‖ ≤ eB) :
    ‖A * conj B - A₀ * conj B₀‖ ≤ eA * (‖B₀‖ + eB) + ‖A₀‖ * eB := by
  calc
    _ = ‖(A - A₀) * conj B + A₀ * conj (B - B₀)‖ := congrArg norm (by rw [map_sub]; ring)
    _ ≤ ‖(A - A₀) * conj B‖ + ‖A₀ * conj (B - B₀)‖ := norm_add_le _ _
    _ = ‖A - A₀‖ * ‖B‖ + ‖A₀‖ * ‖B - B₀‖ := by rw [norm_mul, norm_mul, norm_conj, norm_conj]
    _ ≤ _ := add_le_add
      (mul_le_mul hA (norm_le_sample_budget hB) (norm_nonneg _) ((norm_nonneg _).trans hA))
      (mul_le_mul_of_nonneg_left hB (norm_nonneg _))

def mixedThetaCompletedSampleError (K : Type) [Field K] [NumberField K]
    (R tail T : ℝ) (n m : ℕ) : ℝ :=
  mixedThetaContourVariation K R (dottieScaledRightCenter T n) (dottieScaledRadius n) *
    (2 * dottieScaledRadius n / (m : ℝ)) + tail

private theorem completed_reading_error_from_sample (K : Type) [Field K] [NumberField K]
    {R tail T : ℝ} {n m : ℕ} {w v : ℂ} (hR : 1 ≤ R)
    (htail : 2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ ≤ tail)
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n))
    (hv : v ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n))
    (hnear : dist w v ≤ 2 * dottieScaledRadius n / (m : ℝ)) :
    ‖mixedThetaCompletedReading K w - mixedThetaCompletedTruncation K R v‖ ≤
      mixedThetaCompletedSampleError K R tail T n m := by
  let V := mixedThetaContourVariation K R (dottieScaledRightCenter T n) (dottieScaledRadius n)
  have hMass : 0 ≤ ∫ t : ℝ in 1..R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ :=
    intervalIntegral.integral_nonneg hR (fun _ _ ↦ norm_nonneg _)
  have hLog := Real.log_nonneg hR
  have hr : 0 < dottieScaledRadius n := by unfold dottieScaledRadius dottieRingScale; positivity
  have hV : 0 ≤ V := by
    change 0 ≤ mixedThetaContourVariation K R (dottieScaledRightCenter T n) (dottieScaledRadius n)
    unfold mixedThetaContourVariation contourPoleVariation
    positivity
  obtain ⟨hc, hc1⟩ := dottie_closedBall_avoids_poles T n
  have hwS := dottieScaledRightDisk_strip hw
  have hvS := dottieScaledRightDisk_strip hv
  have hw0 := (by norm_num : (0 : ℝ) < 1 / 2).trans hwS.1
  have hv0 := (by norm_num : (0 : ℝ) < 1 / 2).trans hvS.1
  have ht := (mixedThetaCompletedTruncation_error_le K R hR w hw0 hwS.2).trans htail
  have ho := mixedThetaCompletedTruncation_difference_le_on_disk K hR hc hc1 hw hv
    hw0.le hwS.2.le hv0.le hvS.2.le
  have hdelta := ho.trans (mul_le_mul_of_nonneg_left ((dist_eq_norm w v) ▸ hnear) hV)
  unfold mixedThetaCompletedSampleError
  rw [← sub_add_sub_cancel (mixedThetaCompletedReading K w) (mixedThetaCompletedTruncation K R w)
    (mixedThetaCompletedTruncation K R v)]
  exact (norm_add_le _ _).trans ((add_le_add ht hdelta).trans_eq (add_comm _ _))

/-- Actual truncated mixed-theta samples and a signed enclosure for their
ordered cross product on one Dottie circle. `K` is the lower field. -/
def HasDottieCompletedCrossProductSamples (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] (T : ℝ) (n : ℕ) : Prop :=
  ∃ RK RL : ℝ, 1 ≤ RK ∧ 1 ≤ RL ∧ ∃ m : ℕ, 0 < m ∧ ∃ axis : ℂ, ‖axis‖ = 1 ∧
    ∃ M margin tailK tailL : ℝ, 0 < M ∧ 0 < margin ∧
      (2 * ∫ t : ℝ in Ioi RK, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖) ≤ tailK ∧
      (2 * ∫ t : ℝ in Ioi RL, ‖(Theta.mixedThetaPair L).f t - (Theta.mixedThetaPair L).f₀‖) ≤ tailL ∧
      ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
        let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j
        let A := mixedThetaCompletedTruncation L RL v
        let B := mixedThetaCompletedTruncation K RK v
        let eA := mixedThetaCompletedSampleError L RL tailL T n m
        let eB := mixedThetaCompletedSampleError K RK tailK T n m
        ‖B‖ + eB ≤ M ∧
          (axis * (A * conj B)).im + eA * (‖B‖ + eB) + ‖A‖ * eB ≤ -margin

theorem completedRelativeReading_boundary_of_samples (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] {g : ℂ → ℂ}
    (hprod : ∀ w : ℂ, w ≠ 1 → mixedThetaContinuation L w = g w * mixedThetaContinuation K w)
    {T : ℝ} {n : ℕ} (hsamples : HasDottieCompletedCrossProductSamples K L T n) :
    HasDottieBoundarySign (completedRelativeReading K L g) T n := by
  obtain ⟨RK, RL, hRK, hRL, m, hm, axis, haxis, M, margin, tailK, tailL, hM, hmargin,
    hKtail, hLtail, hdata⟩ := hsamples
  refine ⟨axis, margin / M ^ 2, div_pos hmargin (pow_pos hM 2), ?_⟩
  simp only [← neg_div]
  apply completedRelativeReading_boundary_of_cross_product K L hprod hM hmargin
  intro w hw
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := by dsimp [r, dottieScaledRadius, dottieRingScale]; positivity
  obtain ⟨a, ha, j, hj, hnear⟩ := exists_near_rationalContourSample hr hw hm
  let v := rationalContourSample c r a m j
  let A := mixedThetaCompletedTruncation L RL v
  let B := mixedThetaCompletedTruncation K RK v
  let eA := mixedThetaCompletedSampleError L RL tailL T n m
  let eB := mixedThetaCompletedSampleError K RK tailK T n m
  have hwD := Metric.sphere_subset_closedBall hw
  have hvD : v ∈ Metric.closedBall c r :=
    Metric.sphere_subset_closedBall (rationalContourSample_mem_sphere hr ha)
  have hA : ‖mixedThetaCompletedReading L w - A‖ ≤ eA :=
    completed_reading_error_from_sample L hRL hLtail hwD hvD hnear
  have hB : ‖mixedThetaCompletedReading K w - B‖ ≤ eB :=
    completed_reading_error_from_sample K hRK hKtail hwD hvD hnear
  obtain ⟨hMass, hSign⟩ := hdata a ha j hj
  change ‖B‖ + eB ≤ M at hMass
  change (axis * (A * conj B)).im + eA * (‖B‖ + eB) + ‖A‖ * eB ≤ -margin at hSign
  refine ⟨(norm_le_sample_budget hB).trans hMass, ?_⟩
  have he := norm_cross_product_sub_le hA hB
  have hi : (axis * (mixedThetaCompletedReading L w * conj (mixedThetaCompletedReading K w) -
      A * conj B)).im ≤ eA * (‖B‖ + eB) + ‖A‖ * eB := by
    refine (le_abs_self _).trans ((abs_im_le_norm _).trans ?_)
    simpa only [norm_mul, haxis, one_mul] using he
  rw [mul_sub, sub_im] at hi
  linarith only [hi, hSign]

/-- A sufficient cofinal condition for the sampled relative-factor route. Analytic
clearance and the finite subcover follow from the existing band proofs. -/
def HasCofinalDottieCrossProductSamples (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∀ ε : ℝ, 0 < ε → ∀ w : ℂ,
    w.im ∈ Icc (0 : ℝ) (M : ℝ) → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
      ∃ a : DottieBandRing 0 (M : ℝ),
        w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieCompletedCrossProductSamples K L a.val.1 a.val.2

theorem dedekindZetaRH_of_solvable_relative_samples (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L] [Group.IsSolvable (L ≃ₐ[K] L)]
    (hK : DedekindZetaRH K) (hs : HasCofinalDottieCrossProductSamples K L) : DedekindZetaRH L := by
  obtain ⟨g, hg, hprod⟩ := dedekind_entire_factor_of_solvable_galois K L
    (mixedThetaContinuation_isDedekind K) (mixedThetaContinuation_isDedekind L)
  apply dedekindZetaRH_of_relative_dottie_bands K L hg hprod hK
  intro N
  obtain ⟨M, hM, hloc⟩ := hs N
  refine ⟨M, hM, ?_⟩
  obtain ⟨ε, hε, hclear⟩ := exists_dedekind_band_clearance (mixedThetaContinuation_isDedekind L) 0 (M : ℝ)
  apply hasFiniteDottieBoundaryCertificate_of_local_signs hε ?_ ?_
  · intro w him hre hhi hclose hz
    have hw : w ≠ 1 := by rintro rfl; norm_num at hhi
    exact hclear w him hre hhi hclose (by rw [hprod w hw, hz, zero_mul])
  · intro w him hre hhi
    obtain ⟨a, ha, hsample⟩ := hloc ε hε w him hre hhi
    exact ⟨a, ha, completedRelativeReading_boundary_of_samples K L hprod hsample⟩

/-- Select the commutator-fixed field and use the rational Dirichlet result
there. The cross-product samples concern that field and the same upper field. -/
theorem dedekindZetaRH_of_solvable_galois_relative_samples (L : Type) [Field L] [NumberField L]
    [IsGalois ℚ L] [Group.IsSolvable (L ≃ₐ[ℚ] L)]
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hs : HasCofinalDottieCrossProductSamples (IntermediateField.fixedField (commutator (L ≃ₐ[ℚ] L))) L) :
    DedekindZetaRH L := by
  let F := IntermediateField.fixedField (commutator (L ≃ₐ[ℚ] L))
  let : IsAbelianGalois ℚ F := commutator_fixedField_isAbelian ℚ L
  let e := IntermediateField.subgroupEquivAlgEquiv (commutator (L ≃ₐ[ℚ] L))
  let : Group.IsSolvable (L ≃ₐ[F] L) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  exact dedekindZetaRH_of_solvable_relative_samples F L (dedekindZetaRH_of_dirichlet_of_abelian hD F) hs

theorem dedekindZetaRH_of_solvable_normalClosure_relative_samples (K : Type) [Field K] [NumberField K]
    [Group.IsSolvable (RationalNormalClosure K ≃ₐ[ℚ] RationalNormalClosure K)]
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hs : let L := RationalNormalClosure K
      HasCofinalDottieCrossProductSamples (IntermediateField.fixedField (commutator (L ≃ₐ[ℚ] L))) L) :
    DedekindZetaRH K :=
  dedekindZetaRH_of_solvable_normalClosure K
    (dedekindZetaRH_of_solvable_galois_relative_samples (RationalNormalClosure K) hD hs)

#print HasDottieCompletedCrossProductSamples
#print HasCofinalDottieCrossProductSamples
#check @dedekindZetaRH_of_solvable_normalClosure_relative_samples
#print axioms norm_cross_product_sub_le
#print axioms completedRelativeReading_boundary_of_samples
#print axioms dedekindZetaRH_of_solvable_relative_samples
#print axioms dedekindZetaRH_of_solvable_galois_relative_samples
#print axioms dedekindZetaRH_of_solvable_normalClosure_relative_samples

end

end FieldTarget
