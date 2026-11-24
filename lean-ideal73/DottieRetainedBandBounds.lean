import DottieRetainedCore
import DottieRetainedBands
import DottieBandVariation

/-! The exact retained band bound reduces to signed integer sums of the
original quartic coefficients on three contiguous intervals. -/

namespace QuarticModel

open Complex Finset Set SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private dottieContour from ArchivedDottieTailPartition
open private norm_real_add_imag_le from DottieHighGammaTail
set_option autoImplicit false
set_option maxRecDepth 4096

/-- Bounds on the intermediate signed partial sums and the terminal sum,
inclusive of both endpoints of the original band. -/
def DottieBandIntegerSums (a b : ℕ) (A M : ℤ) : Prop :=
  (∀ k ≤ b-a, |∑ i ∈ range k, archivedLatticeCoeff (a+i)| ≤ A) ∧
  |∑ i ∈ range (b-a+1), archivedLatticeCoeff (a+i)| ≤ M

private theorem dottie_conductor_height_product :
    7400000000000000000 ≤ archivedThetaScale*dottieHeight ∧
      archivedThetaScale*dottieHeight ≤ 7420000000000000000 := by
  have hB₀ : (1638000 : ℝ) ≤ archivedThetaScale := by
    unfold archivedThetaScale
    apply (le_div_iff₀ Real.pi_pos).2
    exact (show 1638000*Real.pi ≤ 1638000*3.1416 by linarith only [Real.pi_lt_d4]).trans
      (Real.le_sqrt_of_sq_le (by norm_num))
  have hB₁ : archivedThetaScale ≤ 1639000 := by
    unfold archivedThetaScale
    apply (div_le_iff₀ Real.pi_pos).2
    exact (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩ : √(26509772707289 : ℝ) ≤ 1639000*3.14159).trans
      (by linarith only [Real.pi_gt_d20])
  have hT₀ : (4526119322477 : ℝ) ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
  have hT₁ : dottieHeight ≤ 4526119322478 := by linarith only [dottieHeight_enclosure.2]
  constructor
  · exact (show (7400000000000000000 : ℝ) ≤ 1638000*4526119322477 by norm_num).trans
      (mul_le_mul hB₀ hT₀ (by norm_num) archivedThetaScale_pos.le)
  · exact (mul_le_mul hB₁ hT₁ (by linarith only [hT₀]) (by norm_num)).trans (by norm_num)

private theorem dottie_band_scale_power (B T a σ : ℝ) (hB : 0 < B) (hT : 0 < T) (ha : 0 < a) :
    (B/a)^(σ+1)*(T^(σ-1)/B^2) = ((B*T)/a)^(σ+1)/(B*T)^2 := by
  have ht : T^(σ-1) = T^(σ+1)/(T^2) := by
    rw [show σ-1 = (σ+1)-2 by ring, Real.rpow_sub hT, Real.rpow_two]
  rw [ht, show (B*T)/a = (B/a)*T by ring,
    Real.mul_rpow (div_nonneg hB.le ha.le) hT.le, mul_pow]
  ring

private theorem dottie_core_polynomial_argument {w : ℂ} {u : ℝ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20) :
    let q := w+dottieContour u
    q.re = w.re+1 ∧ 0 ≤ q.re ∧ q.re ≤ 2 ∧ ‖q‖ ≤ 4527000000000 := by
  let q := w+dottieContour u
  have hqr : q.re = w.re+1 := by simp [q,dottieContour]
  have hqi : q.im = w.im+u := by simp [q,dottieContour]
  have hq₀ : 0 ≤ q.re := by rw [hqr]; linarith only [hr.1]
  have hq₁ : q.re ≤ 2 := by rw [hqr]; linarith only [hr.2]
  have he : q = (q.re : ℂ)+(q.im : ℂ)*I := by apply Complex.ext <;> simp
  have hnorm : ‖q‖ ≤ |q.re|+|q.im| :=
    (congrArg norm he).le.trans (norm_real_add_imag_le q.re q.im)
  refine ⟨hqr,hq₀,hq₁,hnorm.trans ?_⟩
  rw [abs_of_nonneg hq₀,hqi]
  rw [abs_le] at hi hu
  have hwim : |w.im| ≤ 4526119322478 := by
    exact abs_le.mpr ⟨by linarith only [hi.1,dottieHeight_enclosure.1],
      by linarith only [hi.2,dottieHeight_enclosure.2]⟩
  linarith only [hq₁, abs_add_le w.im u, hwim, abs_le.mpr hu]

private theorem dottie_one_band_core_of_integer_sums {a b : ℕ} {A M : ℤ} {R : ℝ}
    {w : ℂ} {u : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20)
    (haLo : (4527000000000 : ℝ)/(a : ℝ) ≤ 1/1000)
    (haHi : (a : ℝ) ≤ 7420000000000000000)
    (hR : ((7420000000000000000 : ℝ)/(a : ℝ))^2 ≤ R)
    (hlen : (1001/1000)*4527000000000*((b : ℝ)-a)/(a : ℝ) ≤ 1/3)
    (hs : DottieBandIntegerSums a b A M) :
    ‖dottieRangePolynomial (Finset.Icc a b) (w+dottieContour u)‖ *
      (dottieHeight^(w.re-1)/archivedThetaScale^2) ≤
        R*((M : ℝ)+(A : ℝ)/3)/(7400000000000000000 : ℝ)^2 := by
  let B := archivedThetaScale
  let T := dottieHeight
  let K := B*T
  let q := w+dottieContour u
  obtain ⟨hqr,hq₀,hq₁,hq⟩ := dottie_core_polynomial_argument hr hi hu
  have ha' : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hB : 0 < B := archivedThetaScale_pos
  have hT : 0 < T := by dsimp only [T]; linarith only [dottieHeight_enclosure.1]
  have hK : 0 < K := mul_pos hB hT
  have hA : 0 ≤ A := (abs_nonneg _).trans (hs.1 0 (Nat.zero_le _))
  have hM : 0 ≤ M := (abs_nonneg _).trans hs.2
  have hAr : 0 ≤ (A : ℝ) := by exact_mod_cast hA
  have hMr : 0 ≤ (M : ℝ) := by exact_mod_cast hM
  have hprefix (k : ℕ) (hk : k ≤ b-a) :
      ‖∑ i ∈ range k, (archivedLatticeCoeff (a+i) : ℂ)‖ ≤ (A : ℝ) := by
    rw [← Int.cast_sum, Complex.norm_intCast]
    exact_mod_cast hs.1 k hk
  have hterminal :
      ‖∑ i ∈ range (b-a+1), (archivedLatticeCoeff (a+i) : ℂ)‖ ≤ (M : ℝ) := by
    rw [← Int.cast_sum, Complex.norm_intCast]
    exact_mod_cast hs.2
  have hsmall : ‖q‖/(a : ℝ) ≤ 1/1000 :=
    (div_le_div_of_nonneg_right hq ha'.le).trans haLo
  have hv : (1001/1000)*(‖q‖/(a : ℝ))*((b-a : ℕ) : ℝ) ≤ 1/3 := by
    rw [Nat.cast_sub hab]
    refine le_trans ?_ hlen
    rw [show (1001/1000 : ℝ)*4527000000000*((b : ℝ)-a)/(a : ℝ) =
      (1001/1000)*(4527000000000/(a : ℝ))*((b : ℝ)-a) by ring]
    gcongr
    exact sub_nonneg.mpr (Nat.cast_le.mpr hab)
  have hc : (M : ℝ)+(A : ℝ)*((1001/1000)*(‖q‖/(a : ℝ)))*((b-a : ℕ) : ℝ) ≤
      (M : ℝ)+(A : ℝ)/3 := by
    rw [mul_assoc (A : ℝ)]
    nlinarith only [mul_le_mul_of_nonneg_left hv hAr]
  have hp := dottie_band_polynomial_bound ha hab hq₀ hsmall (A : ℝ) (M : ℝ) hprefix hterminal
  have hpoly : ‖dottieRangePolynomial (Finset.Icc a b) q‖ ≤ (B/(a : ℝ))^q.re*((M : ℝ)+(A : ℝ)/3) :=
    hp.trans (mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by positivity) _))
  have hPower : (K/(a : ℝ))^q.re ≤ R := by
    have hbase : (1 : ℝ) ≤ 7420000000000000000/(a : ℝ) := (one_le_div ha').2 haHi
    refine (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right dottie_conductor_height_product.2 ha'.le) hq₀).trans ?_
    rw [← Real.rpow_two] at hR
    exact (Real.rpow_le_rpow_of_exponent_le hbase hq₁).trans hR
  change ‖dottieRangePolynomial (Finset.Icc a b) q‖ * (T^(w.re-1)/B^2) ≤ _
  calc
    _ ≤ ((B/(a : ℝ))^q.re*((M : ℝ)+(A : ℝ)/3))*(T^(w.re-1)/B^2) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (K/(a : ℝ))^q.re*((M : ℝ)+(A : ℝ)/3)/K^2 := by
      rw [hqr]
      have h := dottie_band_scale_power B T a w.re hB hT ha'
      calc
        _ = ((B/(a : ℝ))^(w.re+1)*(T^(w.re-1)/B^2))*((M : ℝ)+(A : ℝ)/3) := by ring
        _ = _ := by rw [h]; dsimp only [K]; ring
    _ ≤ _ := by
      have hR₀ : 0 ≤ R := (sq_nonneg _).trans hR
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_right hPower (by positivity)) (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) dottie_conductor_height_product.1 2

theorem dottie_retained_band_core_of_integer_sums
    (h₄ : DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12)
    (h₂ : DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482)
    (h₁ : DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338)
    {w : ℂ} {u : ℝ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20) :
    ‖dottieRangePolynomial dottieRetainedBandNorms (w+dottieContour u)‖ *
      (dottieHeight^(w.re-1)/archivedThetaScale^2) ≤
        (31406/3)/(7400000000000000000 : ℝ)^2 := by
  let S₄ := Finset.Icc 1854467118035498894 1854467118035634061
  let S₂ := Finset.Icc 3708934236071001884 3708934236071268123
  let S₁ := Finset.Icc 7417868472142007863 7417868472142536246
  let q := w+dottieContour u
  let C := dottieHeight^(w.re-1)/archivedThetaScale^2
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hT : 0 ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
    exact div_nonneg (Real.rpow_nonneg hT _) (by positivity)
  have hd₂ : Disjoint S₄ S₂ := by
    rw [Finset.disjoint_left]
    simp only [S₄,S₂,Finset.mem_Icc]
    omega
  have hd₁ : Disjoint (S₄ ∪ S₂) S₁ := by
    rw [Finset.disjoint_left]
    simp only [S₄,S₂,S₁,Finset.mem_union,Finset.mem_Icc]
    omega
  have he : dottieRangePolynomial dottieRetainedBandNorms q =
      dottieRangePolynomial S₄ q+dottieRangePolynomial S₂ q+dottieRangePolynomial S₁ q := by
    have h : dottieRetainedBandNorms = (S₄ ∪ S₂) ∪ S₁ := rfl
    rw [h, dottieRangePolynomial, Finset.sum_union hd₁, Finset.sum_union hd₂]
    rfl
  obtain ⟨hl₄,hl₂,hl₁⟩ := dottie_retained_band_phase_lengths
  have e₄ := dottie_one_band_core_of_integer_sums (R := 17) (by decide) (by decide) hr hi hu
    (by norm_num) (by norm_num) (by norm_num) hl₄ h₄
  have e₂ := dottie_one_band_core_of_integer_sums (R := 5) (by decide) (by decide) hr hi hu
    (by norm_num) (by norm_num) (by norm_num) hl₂ h₂
  have e₁ := dottie_one_band_core_of_integer_sums (R := 2) (by decide) (by decide) hr hi hu
    (by norm_num) (by norm_num) (by norm_num) hl₁ h₁
  change ‖dottieRangePolynomial dottieRetainedBandNorms q‖*C ≤ _
  rw [he]
  refine (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) hC).trans ?_
  rw [add_mul,add_mul]
  exact (add_le_add (add_le_add e₄ e₂) e₁).trans (by norm_num)

/-- The three integer sum certificates supply the full retained-band
allowance on the original Dottie circle and its reflection. -/
theorem dottie_retained_bands_bound_of_integer_sums
    (h₄ : DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12)
    (h₂ : DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482)
    (h₁ : DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338)
    {w : ℂ} (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖∑ n ∈ dottieRetainedBandNorms, dottieSmoothTerm w n‖ ≤ 36/10^35 := by
  let S := dottieRetainedBandNorms
  let C : ℝ := (31406/3)/(7400000000000000000 : ℝ)^2
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^19 := by
    intro n hn
    simp only [S,dottieRetainedBandNorms,Finset.mem_union,Finset.mem_Icc] at hn
    omega
  have hside {z : ℂ}
      (hz : z.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
      (hzi : |z.im-dottieHeight| ≤ 35/2048) :
      ‖dottieRangeSide S z‖ ≤ (7/8)*C+1/10^79 := by
    apply dottie_range_side_bound_of_core_mass S hS hz hzi (by norm_num [C])
    intro u hu
    exact dottie_retained_band_core_of_integer_sums h₄ h₂ h₁ hz hzi
      (abs_le.mpr ⟨hu.1.le,hu.2⟩)
  have hmr : (1-conj w).re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048) := by
    simp only [sub_re,one_re,conj_re]
    exact ⟨by linarith only [hr.2],by linarith only [hr.1]⟩
  have hmi : |(1-conj w).im-dottieHeight| ≤ 35/2048 := by simpa using hi
  have hn : ∀ n ∈ S, n ≠ 0 := fun n hn => (hS n hn).1.ne'
  have hw₀ : 0 < w.re+1 := by linarith only [hr.1]
  have hw₁ : 0 < (1-conj w).re+1 := by linarith only [hmr.1]
  have he : (∑ n ∈ S, dottieSmoothTerm w n) =
      dottieRangeSide S w+conj (dottieRangeSide S (1-conj w)) := by
    rw [dottie_range_side_eq_sum S hw₀ hn,dottie_range_side_eq_sum S hw₁ hn,
      map_sum,← Finset.sum_add_distrib]
    rfl
  change ‖∑ n ∈ S, dottieSmoothTerm w n‖ ≤ _
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj]
  exact (add_le_add (hside hr hi) (hside hmr hmi)).trans (by norm_num [C])

#print axioms dottie_retained_band_core_of_integer_sums
#print axioms dottie_retained_bands_bound_of_integer_sums

open SuperZeta.QuarticOrderedTurns in
theorem dottie_ring_painted_orders_of_integer_bands_and_signed_blocks
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks)
    (h₄ : DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12)
    (h₂ : DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482)
    (h₁ : DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338)
    (hsharp : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)))
    (hsigned : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmittedSharpBlock w+dottieOmittedMiddleSmooth w).im ≤
        188*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink inkMirror : ℂ) :
    let q := paintedReading w ink
    let qm := paintedReading (1-conj w) inkMirror
    0 < (J*q).imK ∧ (J*qm).imK < 0 ∧ jk q ≠ kj q ∧ jk qm ≠ kj qm := by
  have hS := dottieCircleReference_lower_of_candidate_equality hscore
  have hS₀ : 0 < dottieCircleReference := lt_of_lt_of_le (by norm_num) hS
  have hm := dottie_retained_margin_of_finite_band_bound hS hsharp (fun _ hz => by
    obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hz
    exact dottie_retained_bands_bound_of_integer_sums h₄ h₂ h₁ hr hi)
  have ht := dottieOmitted_tail_of_split_budget hS₀
    (fun _ hz => dottie_lower_omitted_budget_of_candidate_equality hscore hz) hsigned
    (fun _ hz => dottie_far_budget_of_candidate_equality hscore hz)
  exact dottie_ring_painted_orders_of_signed_bounds hS₀ hm ht hw ink inkMirror

#print axioms dottie_ring_painted_orders_of_integer_bands_and_signed_blocks

end QuarticModel
