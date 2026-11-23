import DottieLowerContourShift
import DottieLeftGammaLocal
import DottieMomentMass

/-! The left segment of the lower smoothing error is small because its
weight contains the sixth power of the norm divided by B T_D. -/

namespace QuarticModel

open Complex Finset MeasureTheory Set
open SuperZeta.StirlingCorrection
open private verticalPoint from ArchivedDottieContourShift
set_option autoImplicit false
set_option maxRecDepth 4096

theorem dottie_theta_scale_gt_three_halves_million : (1500000 : ℝ) < archivedThetaScale := by
  have h : (5000000 : ℝ) < √(26509772707289 : ℝ) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold archivedThetaScale
  exact (lt_div_iff₀ Real.pi_pos).2 (by linarith only [h, Real.pi_lt_d20])

theorem dottie_finite_absolute_mass_le (S : Finset ℕ) {L : ℕ}
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ L) :
    (∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)|) ≤ 2*(L : ℝ) := by
  have hsub : S ⊆ (Finset.range L).image Nat.succ := by
    intro n hn
    have he := hS n hn
    exact Finset.mem_image.mpr ⟨n-1, Finset.mem_range.mpr (by omega), by omega⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)).trans ?_
  rw [Finset.sum_image (fun _ _ _ _ he => Nat.succ.inj he)]
  have h := archived_coeff_prefix_abs_le_linear L
  exact h.trans (by linarith only [show (L.sqrt : ℝ) ≤ L by exact_mod_cast Nat.sqrt_le_self L])

private theorem left_power_identity (B T n σ : ℝ)
    (hB : 0 < B) (hT : 0 < T) (hn : 0 < n) :
    (B/n)^(σ-7)*T^(σ-9)/B^2 = (n/(B*T))^(7-σ)/(B*T)^2 := by
  let p := 7-σ
  have hp : σ-7 = -p := by dsimp [p]; ring
  have hq : σ-9 = -(p+2) := by dsimp [p]; ring
  rw [hp, hq, Real.rpow_neg (div_nonneg hB.le hn.le), Real.rpow_neg hT.le,
    Real.rpow_add hT, Real.rpow_two, Real.div_rpow hB.le hn.le,
    Real.div_rpow hn.le (mul_nonneg hB.le hT.le), Real.mul_rpow hB.le hT.le]
  change ((B^p/n^p)⁻¹)*(T^p*T^2)⁻¹/B^2 = (n^p/(B^p*T^p))/(B*T)^2
  field_simp [(Real.rpow_pos_of_pos hB p).ne', (Real.rpow_pos_of_pos hT p).ne',
    (Real.rpow_pos_of_pos hn p).ne', hB.ne', hT.ne']

private theorem left_polynomial_mass_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {s : ℂ} {σ : ℝ}
    (hs : s.re = σ-7) (hσ : σ ≤ 1) :
    ‖dottieRangePolynomial S s‖ * (dottieHeight^(σ-9)/archivedThetaScale^2) ≤
      (2*10^13 : ℝ)*((10^13/(6*10^18))^6/(6*10^18)^2) := by
  let B := archivedThetaScale
  let T := dottieHeight
  let K := B*T
  let C : ℝ := (10^13/(6*10^18))^6/(6*10^18)^2
  have hB : 0 < B := archivedThetaScale_pos
  have hT' : 4*10^12 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hT : 0 < T := by linarith
  have hK : 0 < K := mul_pos hB hT
  have hK' : 6*10^18 ≤ K := by
    have hb := dottie_theta_scale_gt_three_halves_million
    have hh := mul_le_mul (show (1500000 : ℝ) ≤ B from hb.le) hT'.le
      (by norm_num) hB.le
    dsimp only [K]
    linarith only [hh]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hfactor : 0 ≤ T^(σ-9)/B^2 := div_nonneg (Real.rpow_nonneg hT.le _) (by positivity)
  have hweight (n : ℕ) (hn : n ∈ S) : ((n : ℝ)/K)^(7-σ)/K^2 ≤ C := by
    have hn₀ : 0 ≤ (n : ℝ)/K := by positivity
    have hn₁ : (n : ℝ) ≤ 10^13 := by exact_mod_cast (hS n hn).2
    have hbase : (n : ℝ)/K ≤ 10^13/(6*10^18) :=
      (div_le_div_of_nonneg_right hn₁ hK.le).trans
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hK')
    have hpow : ((n : ℝ)/K)^(7-σ) ≤ (10^13/(6*10^18) : ℝ)^6 := by
      refine (Real.rpow_le_rpow hn₀ hbase (by linarith)).trans ?_
      have he : (10^13/(6*10^18) : ℝ)^(6 : ℝ) = (10^13/(6*10^18) : ℝ)^(6 : ℕ) := by
        simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (10^13/(6*10^18) : ℝ) 6)
      rw [← he]
      exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    exact div_le_div₀ (by positivity) hpow (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hK' 2)
  unfold dottieRangePolynomial
  apply (mul_le_mul_of_nonneg_right (norm_sum_le _ _) hfactor).trans
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)| * C := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (hS n hn).1
      rw [norm_mul, Complex.norm_intCast, norm_cpow_eq_rpow_re_of_pos (div_pos hB hn'), hs]
      have he : (B/(n : ℝ))^(σ-7)*(T^(σ-9)/B^2) = ((n : ℝ)/K)^(7-σ)/K^2 := by
        rw [← mul_div_assoc]
        exact left_power_identity B T n σ hB hT hn'
      rw [mul_assoc, he]
      exact mul_le_mul_of_nonneg_left (hweight n hn) (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      have hm : (∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)|) ≤ (2*10^13 : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using
          dottie_finite_absolute_mass_le S (L := 10^13) hS
      exact mul_le_mul_of_nonneg_right hm hC

/-- Normalized left segment; the same bound works for the lower omitted
range or for the original retained prefix. -/
theorem dottie_normalized_left_segment_bound (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieLeftSegment S w / (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))‖ ≤
      6/10^39 := by
  let T := dottieHeight
  let B := archivedThetaScale
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  let E := 35*Real.pi/4096+2/10^10
  let C : ℝ := (2*10^13)*((10^13/(6*10^18))^6/(6*10^18)^2)
  let M : ℝ := C*(10^22/42)
  let den : ℂ := 2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)
  have hB : 0 < B := archivedThetaScale_pos
  have hT : 0 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hden : ‖den‖ = 2*Real.pi*(B^2*G) := by
    unfold den
    have he : (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)) =
        ((2*Real.pi*(B^2*G) : ℝ) : ℂ) := by
      rw [show archivedDottieCompletionScale = B^2*G from rfl]
      push_cast
      rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hExp : Real.exp (49+E) ≤ 10^22 := by
    have he : 49+E ≤ (50 : ℝ) := by dsimp only [E]; linarith only [Real.pi_lt_four]
    refine (Real.exp_le_exp.mpr he).trans ?_
    rw [show (50 : ℝ) = (50 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le
      (show Real.exp 1 ≤ (11/4 : ℝ) by linarith only [Real.exp_one_lt_d9]) 50).trans (by norm_num)
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioc (-20 : ℝ) 20) :
      ‖dottieRightIntegrand S w (verticalPoint (-7) u)/den‖ ≤ M*Real.exp (-u^2) := by
    let z := verticalPoint (-7) u
    have hz₀ : z.re = -7 := by simp [z, verticalPoint]
    have hz₁ : z.im = u := by simp [z, verticalPoint]
    have hnormz : (7 : ℝ) ≤ ‖z‖ := by
      have h := Complex.abs_re_le_norm z
      rw [hz₀] at h
      simpa using h
    have hprod : (42 : ℝ) ≤ ‖z‖*(2*Real.pi) :=
      (mul_le_mul hnormz (show (6 : ℝ) ≤ 2*Real.pi by linarith only [Real.pi_gt_three])
        (by norm_num) (norm_nonneg _)).trans' (by norm_num)
    have hs : w+z = ⟨w.re-7,w.im+u⟩ := by apply Complex.ext <;> simp [hz₀,hz₁,sub_eq_add_neg]
    have hg : ‖Gamma (w+z)‖/G * Real.exp (Real.pi*u/2) ≤ T^(w.re-9)*Real.exp E := by
      rw [hs]
      exact dottie_gamma_left_tilted_norm_ratio hr hi (abs_le.mpr ⟨hu.1.le,hu.2⟩)
    have hpoly := left_polynomial_mass_le S hS
      (s := w+z) (σ := w.re) (by rw [hs]) (by linarith only [hr.2])
    have hexp :
        ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ =
          (Real.exp 49*Real.exp (-u^2))*Real.exp (Real.pi*u/2) := by
      have he : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
        ring
      rw [Complex.norm_exp, he, hz₀, hz₁, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    change ‖dottieRightIntegrand S w z/den‖ ≤ _
    rw [dottieRightIntegrand, norm_div, norm_div, norm_mul, norm_mul, hexp, hden]
    calc
      _ = (‖dottieRangePolynomial S (w+z)‖/B^2) *
        (‖Gamma (w+z)‖/G * Real.exp (Real.pi*u/2)) *
          (Real.exp 49*Real.exp (-u^2))/(‖z‖*(2*Real.pi)) := by ring
      _ ≤ (‖dottieRangePolynomial S (w+z)‖/B^2) *
        (T^(w.re-9)*Real.exp E) * (Real.exp 49*Real.exp (-u^2))/42 := by
        apply div_le_div₀ (by positivity) ?_ (by norm_num) hprod
        gcongr
      _ = (‖dottieRangePolynomial S (w+z)‖*(T^(w.re-9)/B^2))*
        (Real.exp (49+E)/42)*Real.exp (-u^2) := by rw [Real.exp_add 49 E]; ring
      _ ≤ _ := by
        change _ ≤ C*(10^22/42)*Real.exp (-u^2)
        gcongr
  have hb : Integrable (fun u : ℝ => M*Real.exp (-u^2)) := by
    simpa only [neg_mul, one_mul] using
      (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)).const_mul M
  have hi' := intervalIntegral.norm_integral_le_of_norm_le
    (by norm_num : (-20 : ℝ) ≤ 20) (Filter.Eventually.of_forall hpoint) hb.intervalIntegrable
  change ‖dottieLeftSegment S w / den‖ ≤ _
  rw [dottieLeftSegment, ← intervalIntegral.integral_div]
  refine hi'.trans ?_
  rw [intervalIntegral.integral_of_le (by norm_num : (-20 : ℝ) ≤ 20)]
  refine (setIntegral_le_integral hb (Filter.Eventually.of_forall fun u => ?_)).trans ?_
  · have hM : 0 ≤ M := by dsimp [M,C]; positivity
    exact mul_nonneg hM (Real.exp_pos _).le
  · rw [integral_const_mul]
    have hg : (∫ u : ℝ, Real.exp (-u^2)) = √Real.pi := by
      simpa only [neg_mul, one_mul, div_one] using integral_gaussian (1 : ℝ)
    rw [hg]
    have hπ : √Real.pi ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [Real.pi_lt_four]⟩
    refine (mul_le_mul_of_nonneg_left hπ (by dsimp [M,C]; positivity)).trans ?_
    dsimp [M,C]
    norm_num

#print axioms dottie_theta_scale_gt_three_halves_million
#print axioms dottie_finite_absolute_mass_le
#print axioms dottie_normalized_left_segment_bound

end QuarticModel
