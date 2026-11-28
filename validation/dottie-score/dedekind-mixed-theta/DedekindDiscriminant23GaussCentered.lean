import CenteredExponentialSum
import DedekindDiscriminant23GaussPoint

/-! Center the certified discriminant-23 quadrature at any point of the critical line. -/

namespace FieldTarget

open Finset

noncomputable section

def gauss23CenteredNodes : Finset (ℕ × Fin 24) := Finset.range 16 ×ˢ Finset.univ

def gauss23CenteredNode (p : ℕ × Fin 24) : ℝ :=
  gauss23LogNode (Fin.ofNat 16 p.1) p.2

def gauss23CenteredAmplitude (p : ℕ × Fin 24) : ℝ :=
  gauss23Amplitude (Fin.ofNat 16 p.1) p.2

def gauss23CenteredPlus (slope : Bool) (t : ℝ) (p : ℕ × Fin 24) : ℂ :=
  let u := gauss23CenteredNode p
  ((if slope then u else 1) * gauss23CenteredAmplitude p : ℝ) *
    Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)

def gauss23CenteredMinus (slope : Bool) (t : ℝ) (p : ℕ × Fin 24) : ℂ :=
  let u := gauss23CenteredNode p
  ((if slope then -u else 1) * gauss23CenteredAmplitude p : ℝ) *
    Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))

def gauss23CenteredCoeff (slope : Bool) (t : ℝ) (k : ℕ) : ℂ :=
  centeredExponentialSumCoeff gauss23CenteredNodes gauss23CenteredNode
    (gauss23CenteredPlus slope t) (gauss23CenteredMinus slope t) k

def gauss23CenteredTaylor (slope : Bool) (t : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, gauss23CenteredCoeff slope t k * (w - gauss23CriticalPoint t) ^ k

private theorem gauss23_weighted_sum (f : ℝ → ℂ) :
    rationalCompositeRule gauss24Node gauss24Weight f 0 (1 / 8) 16 =
      ∑ p ∈ gauss23CenteredNodes, (gauss23LogWeight p.2 : ℂ) * f (gauss23CenteredNode p) := by
  rw [gauss23CenteredNodes, Finset.sum_product]
  unfold rationalCompositeRule rationalPanelRule
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hj' : (Fin.ofNat 16 j).val = j := Nat.mod_eq_of_lt (Finset.mem_range.mp hj)
  have hn : (0 : ℝ) + (2 * (j : ℝ) + 1) * (1 / 8) + (1 / 8) * (gauss24Node i : ℝ) =
      gauss23CenteredNode (j, i) := by
    rw [gauss23CenteredNode, gauss23_node_eq, hj']
    ring
  have hw : (((1 / 8 : ℝ) : ℂ)) * (gauss24Weight i : ℂ) = (gauss23LogWeight i : ℂ) := by
    unfold gauss23LogWeight
    push_cast
    ring
  rw [hn, ← mul_assoc, hw]

private theorem gauss23_center_eq (t : ℝ) :
    gauss23CriticalPoint t = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [gauss23CriticalPoint]

private theorem gauss23_centered_sample (slope : Bool) (t : ℝ) (w : ℂ) (p : ℕ × Fin 24) :
    (gauss23LogWeight p.2 : ℂ) * discriminant23GaussIntegrand slope w (gauss23CenteredNode p : ℂ) =
      gauss23CenteredPlus slope t p * Complex.exp ((gauss23CenteredNode p : ℂ) *
        (w - gauss23CriticalPoint t)) +
      gauss23CenteredMinus slope t p * Complex.exp (-((gauss23CenteredNode p : ℂ) *
        (w - gauss23CriticalPoint t))) := by
  let u := gauss23CenteredNode p
  let z := w - gauss23CriticalPoint t
  let v : ℂ := (((t * u : ℝ) : ℂ) * Complex.I)
  have hplus : Complex.exp (w * (u : ℂ)) =
      (Real.exp (u / 2) : ℂ) * Complex.exp v * Complex.exp ((u : ℂ) * z) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp only [v, z]
    rw [gauss23_center_eq]
    push_cast
    ring
  have hminus : Complex.exp ((1 - w) * (u : ℂ)) =
      (Real.exp (u / 2) : ℂ) * Complex.exp (-v) * Complex.exp (-((u : ℂ) * z)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp only [v, z]
    rw [gauss23_center_eq]
    push_cast
    ring
  change (gauss23LogWeight p.2 : ℂ) * discriminant23GaussIntegrand slope w (u : ℂ) =
    gauss23CenteredPlus slope t p * Complex.exp ((u : ℂ) * z) +
    gauss23CenteredMinus slope t p * Complex.exp (-((u : ℂ) * z))
  rw [discriminant23_gaussIntegrand_real_eq, hplus, hminus]
  unfold gauss23CenteredPlus gauss23CenteredMinus gauss23CenteredAmplitude gauss23Amplitude
  cases slope <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    dsimp only [u, v, gauss23CenteredNode] <;> push_cast <;> ring

private theorem gauss23_reading_eq_centered_sum (slope : Bool) (t : ℝ) (w : ℂ) :
    discriminant23GaussReading slope w =
      centeredExponentialSum gauss23CenteredNodes gauss23CenteredNode
        (gauss23CenteredPlus slope t) (gauss23CenteredMinus slope t) (w - gauss23CriticalPoint t) := by
  rw [discriminant23GaussReading, gauss23_weighted_sum, centeredExponentialSum]
  exact Finset.sum_congr rfl (fun p _ ↦ gauss23_centered_sample slope t w p)

private theorem gauss23_amplitude_abs_le_weight (j : Fin 16) (i : Fin 24) :
    |gauss23Amplitude j i| ≤ gauss23LogWeight i * 174 := by
  let u := gauss23LogNode j i
  let θ := discriminant23CharacterPolynomialUpTo 64
    (Real.exp (-discriminant23ThetaScale * Real.exp u))
  have hu : 0 ≤ u := (gauss23_node_limits j i).1
  have hw : 0 ≤ gauss23LogWeight i :=
    div_nonneg (gauss24_weight_nonneg i) (by norm_num)
  have hCount : discriminant23PhaseTermCount 64 = 174 := by decide +kernel
  have hy : |(u : ℂ).im| ≤ 1 / 2 := by norm_num
  have hb : ‖discriminant23PhaseDensityUpTo 64 (u : ℂ)‖ ≤ 174 := by
    calc
      _ ≤ (discriminant23PhaseTermCount 64 : ℝ) := discriminant23_phaseDensity_norm_le _ hy
      _ = _ := by rw [hCount]; norm_num
  have ht : discriminant23PhaseDensityUpTo 64 (u : ℂ) = Complex.exp (u : ℂ) * (θ : ℂ) := by
    simp only [θ, discriminant23PhaseDensityUpTo, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, discriminant23_characterPolynomialUpTo_ofReal]
  rw [ht, norm_mul, ← Complex.ofReal_exp, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u)] at hb
  have hHalf := Real.exp_le_exp.mpr (show u / 2 ≤ u by linarith only [hu])
  have h := (mul_le_mul_of_nonneg_right hHalf (abs_nonneg θ)).trans hb
  change |gauss23LogWeight i * Real.exp (u / 2) * θ| ≤ gauss23LogWeight i * 174
  rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_pos (Real.exp_pos (u / 2)), mul_assoc]
  exact mul_le_mul_of_nonneg_left h hw

private theorem gauss23_amplitude_abs_sum_le :
    (∑ p ∈ gauss23CenteredNodes, |gauss23CenteredAmplitude p|) ≤ 1044 := by
  have hw := gauss24_weight_abs_sum_le
  simp_rw [abs_of_nonneg (gauss24_weight_nonneg _)] at hw
  have hw' : (∑ i : Fin 24, gauss23LogWeight i) ≤ 3 / 8 := by
    unfold gauss23LogWeight
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hw (by norm_num)
  rw [gauss23CenteredNodes, Finset.sum_product]
  calc
    _ ≤ ∑ _ ∈ Finset.range 16, (261 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ i : Fin 24, gauss23LogWeight i * 174 := by
          exact Finset.sum_le_sum (fun i _ ↦ gauss23_amplitude_abs_le_weight (Fin.ofNat 16 j) i)
        _ = (∑ i : Fin 24, gauss23LogWeight i) * 174 := (Finset.sum_mul _ _ _).symm
        _ ≤ 261 / 4 := (mul_le_mul_of_nonneg_right hw' (by norm_num)).trans_eq (by norm_num)
    _ = 1044 := by norm_num

private theorem gauss23_centered_amplitude_bound (slope : Bool) (t : ℝ) (p : ℕ × Fin 24) :
    ‖gauss23CenteredPlus slope t p‖ + ‖gauss23CenteredMinus slope t p‖ ≤
      (if slope then 8 else 2) * |gauss23CenteredAmplitude p| := by
  let u := gauss23CenteredNode p
  let a := gauss23CenteredAmplitude p
  have hU : u ∈ Set.Icc (0 : ℝ) 4 := gauss23_node_limits (Fin.ofNat 16 p.1) p.2
  have hPhase : ‖Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hPhaseNeg : ‖Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  change
    ‖(((if slope then u else 1) * a : ℝ) : ℂ) *
        Complex.exp (((t * u : ℝ) : ℂ) * Complex.I)‖ +
      ‖(((if slope then -u else 1) * a : ℝ) : ℂ) *
        Complex.exp (-(((t * u : ℝ) : ℂ) * Complex.I))‖ ≤
      (if slope then 8 else 2) * |a|
  simp only [norm_mul, hPhase, hPhaseNeg, mul_one, Complex.norm_real, Real.norm_eq_abs]
  cases slope
  · simp only [Bool.false_eq_true, ↓reduceIte, abs_one, one_mul, two_mul, le_refl]
  · simp only [↓reduceIte, abs_neg, abs_of_nonneg hU.1]
    have h := mul_le_mul_of_nonneg_right hU.2 (abs_nonneg a)
    linarith only [h]

private theorem gauss23_centered_mass_le (slope : Bool) (t : ℝ) :
    (∑ p ∈ gauss23CenteredNodes,
      (‖gauss23CenteredPlus slope t p‖ + ‖gauss23CenteredMinus slope t p‖)) ≤
      if slope then 8352 else 2088 := by
  calc
    _ ≤ ∑ p ∈ gauss23CenteredNodes, (if slope then 8 else 2) * |gauss23CenteredAmplitude p| :=
      Finset.sum_le_sum (fun p _ ↦ gauss23_centered_amplitude_bound slope t p)
    _ = (if slope then 8 else 2) * (∑ p ∈ gauss23CenteredNodes, |gauss23CenteredAmplitude p|) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (if slope then 8 else 2) * 1044 :=
      mul_le_mul_of_nonneg_left gauss23_amplitude_abs_sum_le (by cases slope <;> norm_num)
    _ = _ := by cases slope <;> norm_num

theorem discriminant23_gaussCenteredTaylor_error_lt_of_reading (slope : Bool) (t : ℝ) (n : ℕ)
    {w : ℂ} {E r : ℝ} (hReading :
      ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        discriminant23GaussReading slope w‖ < E) (hr : ‖w - gauss23CriticalPoint t‖ ≤ r)
    (hCut : 4 * r / (n + 1 : ℕ) ≤ 1 / 2) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        gauss23CenteredTaylor slope t n w‖ <
      E + (if slope then 8352 else 2088) * (2 * (4 * r) ^ n / (n.factorial : ℝ)) := by
  have hNode : ∀ p ∈ gauss23CenteredNodes, |gauss23CenteredNode p| ≤ 4 := by
    intro p _
    obtain ⟨h₀, h₁⟩ := gauss23_node_limits (Fin.ofNat 16 p.1) p.2
    exact (abs_of_nonneg h₀).trans_le h₁
  have h := centeredExponentialSum_error_le gauss23CenteredNodes gauss23CenteredNode
    (gauss23CenteredPlus slope t) (gauss23CenteredMinus slope t) (by norm_num) hNode
    (gauss23_centered_mass_le slope t) n hCut hr
  rw [← gauss23_reading_eq_centered_sum slope t w] at h
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (add_lt_add_of_lt_of_le hReading h)

theorem discriminant23_gaussCenteredTaylor_error_lt (slope : Bool) (t : ℝ) (n : ℕ)
    {w : ℂ} (hx₀ : 0 ≤ w.re) (hx₁ : w.re ≤ 1) (hy : |w.im| ≤ 20)
    {r : ℝ} (hr : ‖w - gauss23CriticalPoint t‖ ≤ r)
    (hCut : 4 * r / (n + 1 : ℕ) ≤ 1 / 2) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        gauss23CenteredTaylor slope t n w‖ <
      (2 / 10 ^ 19 : ℝ) + (if slope then 8352 else 2088) * (2 * (4 * r) ^ n / (n.factorial : ℝ)) :=
  discriminant23_gaussCenteredTaylor_error_lt_of_reading slope t n
    (discriminant23_gaussReading_error slope hx₀ hx₁ hy) hr hCut

theorem discriminant23_gaussCenteredTaylor_error_lt_of_half_height (slope : Bool) (t : ℝ)
    {w : ℂ} (hx₀ : 0 ≤ w.re) (hx₁ : w.re ≤ 1)
    (hy : |w.im| ≤ 20) (hd : |w.im - t| ≤ 1 / 2) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        gauss23CenteredTaylor slope t 36 w‖ < (3 / 10 ^ 19 : ℝ) := by
  have hx : |w.re - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
  rw [sq_abs] at hx2 hy2
  have hn : ‖w - gauss23CriticalPoint t‖ ≤ (3 / 4 : ℝ) := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, gauss23CriticalPoint]
    norm_num at hx2 hy2
    nlinarith only [hx2, hy2]
  have h := discriminant23_gaussCenteredTaylor_error_lt slope t 36 hx₀ hx₁ hy hn (by norm_num)
  refine h.trans_le ?_
  cases slope <;> norm_num [Nat.factorial]

theorem discriminant23_gaussCenteredTaylor_error_lt_of_right_twentyEight (slope : Bool) (t : ℝ)
    {w : ℂ} (hx₀ : 1 / 2 ≤ w.re) (hx₁ : w.re ≤ 7 / 8)
    (hy : |w.im| ≤ 28) (hd : |w.im - t| ≤ 1 / 2) :
    ‖(if slope then deriv discriminant23CharacterFold w else discriminant23CharacterFold w) -
        gauss23CenteredTaylor slope t 36 w‖ < (1 / 10 ^ 22 : ℝ) := by
  have hx : |w.re - 1 / 2| ≤ (3 / 8 : ℝ) := abs_le.mpr
    ⟨by linarith only [hx₀], by linarith only [hx₁]⟩
  have hx2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg _) hd 2
  rw [sq_abs] at hx2 hy2
  have hn : ‖w - gauss23CriticalPoint t‖ ≤ (5 / 8 : ℝ) := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, gauss23CriticalPoint]
    norm_num at hx2 hy2
    nlinarith only [hx2, hy2]
  have hReading := discriminant23_gaussReading_error_of_twentyEight slope
    (by linarith only [hx₀]) (by linarith only [hx₁]) hy
  have h := discriminant23_gaussCenteredTaylor_error_lt_of_reading slope t 36 hReading hn (by norm_num)
  refine h.trans_le ?_
  cases slope <;> norm_num [Nat.factorial]

#print axioms discriminant23_gaussCenteredTaylor_error_lt_of_reading
#print axioms discriminant23_gaussCenteredTaylor_error_lt
#print axioms discriminant23_gaussCenteredTaylor_error_lt_of_half_height
#print axioms discriminant23_gaussCenteredTaylor_error_lt_of_right_twentyEight

end

end FieldTarget
