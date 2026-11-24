import DottieFarNumeric

/-! The absolute bound on finite shifted contour sums scales with the
cutoff. Passing to the absolutely convergent limit gives a bound for the
infinite tail in the original retained sum. -/

namespace QuarticModel

open Complex Finset Filter
open scoped ComplexConjugate Topology
open SuperZeta.StirlingCorrection
open private dottie_far_one_side_numeric from DottieFarNumeric
set_option autoImplicit false

private theorem dottie_far_scalar_le_of_cutoff {X : ℕ}
    (hX : 8*dottieOmittedFarCut ≤ X) {w : ℂ} (hw : 0 ≤ w.re) :
    dottieFarScalar X w ≤ dottieFarScalar dottieOmittedFarCut w * ((8 : ℝ)^6)⁻¹ := by
  let N := dottieOmittedFarCut
  let p := w.re+7
  let A := archivedThetaScale^p
  let D := 14*Real.pi*archivedThetaScale^2
  have hN : 0 < (N : ℝ) := by norm_num [N,dottieOmittedFarCut]
  have hNX : N ≤ X := by dsimp only [N]; omega
  have hXr : 8*(N : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hp : 0 < p := by dsimp [p]; linarith
  have hp' : 0 < p-1 := by dsimp [p]; linarith
  have hp6 : 1-p ≤ -6 := by dsimp [p]; linarith
  have hB := archivedThetaScale_pos
  have hA : 0 ≤ A := Real.rpow_nonneg hB.le _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hS : 0 < (N.sqrt : ℝ) := by
    exact_mod_cast (show 0 < dottieOmittedFarCut.sqrt by decide +kernel)
  have hSr : (N.sqrt : ℝ) ≤ (X.sqrt : ℝ) := by exact_mod_cast Nat.sqrt_le_sqrt hNX
  have hs : 1+(X.sqrt : ℝ)⁻¹ ≤ 1+(N.sqrt : ℝ)⁻¹ := by
    have hi := (inv_le_inv₀ (hS.trans_le hSr) hS).mpr hSr
    linarith
  have hx : (X : ℝ)^(1-p) ≤ ((8 : ℝ)^6)⁻¹*(N : ℝ)^(1-p) := by
    calc
      _ ≤ (8*(N : ℝ))^(1-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hXr (by linarith)
      _ = (8 : ℝ)^(1-p)*(N : ℝ)^(1-p) := Real.mul_rpow (by norm_num) hN.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
        have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 8 by norm_num) hp6
        simpa only [show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_natCast] using h
  change A*((1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-p)*(p/(p-1))))*Real.exp 49/D ≤
    A*((1+(N.sqrt : ℝ)⁻¹)*((N : ℝ)^(1-p)*(p/(p-1))))*Real.exp 49/D*((8 : ℝ)^6)⁻¹
  calc
    _ ≤ A*((1+(N.sqrt : ℝ)⁻¹)*
        ((((8 : ℝ)^6)⁻¹*(N : ℝ)^(1-p))*(p/(p-1))))*Real.exp 49/D := by
      apply div_le_div_of_nonneg_right _ hD
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ hA
      gcongr
    _ = _ := by ring

private theorem dottie_right_after_eight_cutoffs {X : ℕ}
    (hX : 8*dottieOmittedFarCut ≤ X) (S : Finset ℕ) (hS : ∀ n ∈ S, X < n)
    {w : ℂ} (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieRightSide S w 7‖ ≤ 1/10^39 := by
  have hX₀ : 0 < X := by
    have hN : 0 < 8*dottieOmittedFarCut := by decide +kernel
    exact hN.trans_le hX
  have hw : 0 < w.re := by linarith only [hr.1]
  have hT : 0 ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
  have hg₀ : 0 ≤ dottieFarEnvelopeMass w := by
    unfold dottieFarEnvelopeMass dottieFarGammaCore dottieFarGammaOuter
    positivity
  have h := dottie_right_seven_norm_le_of_tilted_gamma S hX₀ hS hw _
    (dottie_far_gamma_envelope_integrable w.re w.im) (dottie_far_gamma_envelope_bound_at hr hi)
  rw [dottie_far_gamma_envelope_integral] at h
  change ‖dottieRightSide S w 7‖ ≤ dottieFarScalar X w*dottieFarEnvelopeMass w at h
  calc
    _ ≤ dottieFarScalar X w*dottieFarEnvelopeMass w := h
    _ ≤ (dottieFarScalar dottieOmittedFarCut w*((8 : ℝ)^6)⁻¹)*dottieFarEnvelopeMass w :=
      mul_le_mul_of_nonneg_right (dottie_far_scalar_le_of_cutoff hX hw.le) hg₀
    _ = (dottieFarScalar dottieOmittedFarCut w*dottieFarEnvelopeMass w)*((8 : ℝ)^6)⁻¹ := by ring
    _ ≤ (1/(5*10^33) : ℝ)*((8 : ℝ)^6)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (dottie_far_one_side_numeric (N := dottieOmittedFarCut)
          (by decide +kernel) hw.le hi) (by positivity)
    _ ≤ _ := by norm_num

theorem dottie_finite_smoothed_late_norm_bound {X : ℕ} (hX : 8*dottieOmittedFarCut ≤ X)
    (S : Finset ℕ) (hS : ∀ n ∈ S, X < n) {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖∑ n ∈ S, dottieSmoothTerm w n‖ ≤ 2/10^39 := by
  have hmr : (1-conj w).re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048) := by
    simp only [sub_re, one_re, conj_re]
    exact ⟨by linarith only [hr.2],by linarith only [hr.1]⟩
  have hmi : |(1-conj w).im-dottieHeight| ≤ 35/2048 := by simpa using hi
  have hn : ∀ n ∈ S, n ≠ 0 := fun n nS => ((Nat.zero_le X).trans_lt (hS n nS)).ne'
  have hw : 0 < w.re+1 := by linarith only [hr.1]
  have hmw : 0 < (1-conj w).re+1 := by linarith only [hmr.1]
  have he : (∑ n ∈ S, dottieSmoothTerm w n) =
      dottieRangeSide S w + conj (dottieRangeSide S (1-conj w)) := by
    rw [dottie_range_side_eq_sum S hw hn, dottie_range_side_eq_sum S hmw hn,
      map_sum, ← Finset.sum_add_distrib]
    rfl
  rw [he, ← dottie_right_side_eq_range_side S w (c := 7) (by norm_num) hw hn,
    ← dottie_right_side_eq_range_side S (1-conj w) (c := 7) (by norm_num) hmw hn]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj]
  exact (add_le_add (dottie_right_after_eight_cutoffs hX S hS hr hi)
    (dottie_right_after_eight_cutoffs hX S hS hmr hmi)).trans (by norm_num)

/-- The infinite retained tail, starting at the original exact cutoff. -/
theorem dottie_retained_far_tail_uniform_absolute {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieFarTail w‖ ≤ 2/10^39 := by
  let a (n : ℕ) := dottieSmoothTerm w (n+dottieTailStart)
  have hw₀ : 0 < w.re := by linarith only [hr.1]
  have hw₁ : w.re < 1 := by linarith only [hr.2]
  have hs₀ : Summable (dottieSmoothTerm w) := (dottieSmoothTerm_norm_summable hw₀ hw₁).of_norm
  have hs : Summable a := (summable_nat_add_iff dottieTailStart).2 hs₀
  have hlim := hs.hasSum.tendsto_sum_nat.norm
  change ‖∑' n : ℕ, a n‖ ≤ _
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  let e (n : ℕ) := n+dottieTailStart
  have hinj : Set.InjOn e ↑(Finset.range k) := by
    intro i _ j _ h
    exact Nat.add_right_cancel h
  change ‖∑ n ∈ Finset.range k, dottieSmoothTerm w (e n)‖ ≤ _
  rw [← Finset.sum_image hinj]
  apply dottie_finite_smoothed_late_norm_bound (X := dottieTailStart-1)
    (by decide +kernel) _ ?_ hr hi
  intro n hn
  obtain ⟨m,_,rfl⟩ := Finset.mem_image.mp hn
  have hstart : 0 < dottieTailStart := by decide +kernel
  dsimp only [e]
  omega

#print axioms dottie_finite_smoothed_late_norm_bound
#print axioms dottie_retained_far_tail_uniform_absolute

end QuarticModel
