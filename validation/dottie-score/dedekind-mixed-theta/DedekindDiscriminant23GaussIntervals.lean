import Gauss24PanelTable
import DedekindDiscriminant23CharacterPolynomial
import MellinFixedElementary
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Shared directed intervals for the 384 rational heat samples. -/

namespace FieldTarget

open Finset DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

def gauss23NodeNumerator (j : Fin 16) (i : Fin 24) : ℤ :=
  (2 * (j.val : ℤ) + 1) * gauss24Denominator + (gauss24Pair i).1

def gauss23NodeDenominator : ℤ := 8 * gauss24Denominator

def gauss23LogNode (j : Fin 16) (i : Fin 24) : ℝ :=
  (gauss23NodeNumerator j i : ℝ) / (gauss23NodeDenominator : ℝ)

def gauss23NodeBox (j : Fin 16) (i : Fin 24) : Box :=
  fromRatio (gauss23NodeNumerator j i) gauss23NodeDenominator

theorem gauss23_node_eq (j : Fin 16) (i : Fin 24) :
    gauss23LogNode j i = (2 * (j.val : ℝ) + 1) / 8 + (gauss24Node i : ℝ) / 8 := by
  unfold gauss23LogNode gauss23NodeNumerator gauss23NodeDenominator gauss24Node
  push_cast
  have hD : (gauss24Denominator : ℝ) ≠ 0 := by norm_num [gauss24Denominator]
  field_simp [hD]

theorem gauss23_node_limits (j : Fin 16) (i : Fin 24) : 0 ≤ gauss23LogNode j i ∧ gauss23LogNode j i ≤ 4 := by
  have hj₀ : (0 : ℝ) ≤ j.val := by positivity
  have hj₁ : (j.val : ℝ) ≤ 15 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  obtain ⟨h₁, h₂⟩ := abs_le.mp (gauss24_node_abs_le i)
  rw [gauss23_node_eq]
  constructor <;> linarith only [hj₀, hj₁, h₁, h₂]

theorem gauss23_nodeBox_contains (j : Fin 16) (i : Fin 24) :
    Contains (gauss23NodeBox j i) (gauss23LogNode j i) :=
  ratio_contains _ (by norm_num [gauss23NodeDenominator, gauss24Denominator])

def discriminant23TightThetaScaleBox : Box := ⟨1310134702738572777267392, 1310134702738572777271590⟩

theorem discriminant23_tightThetaScaleBox_contains :
    Contains discriminant23TightThetaScaleBox discriminant23ThetaScale := by
  have hq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 23)
  have hnon := Real.sqrt_nonneg 23
  have hspos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 23)
  have hsL : (47958315233127195415974 / 10^22 : ℝ) ≤ Real.sqrt 23 := by nlinarith only [hq, hnon]
  have hsU : Real.sqrt 23 ≤ (47958315233127195415975 / 10^22 : ℝ) := by nlinarith only [hq, hnon]
  have hL : (1310134702738572777267392 / 10^24 : ℝ) ≤ discriminant23ThetaScale := by
    unfold discriminant23ThetaScale
    apply (le_div_iff₀ hspos).mpr
    nlinarith only [hsU, Real.pi_gt_d20]
  have hU : discriminant23ThetaScale ≤ (1310134702738572777271590 / 10^24 : ℝ) := by
    unfold discriminant23ThetaScale
    apply (div_le_iff₀ hspos).mpr
    nlinarith only [hsL, Real.pi_lt_d20]
  unfold Contains discriminant23TightThetaScaleBox scale
  constructor <;> norm_num <;> linarith only [hL, hU]

private def gauss23ThetaCoefficient (k : ℕ) : ℤ :=
  [0, 2, -2, -2, 0, 0, 2, 0, 2, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2, -2, 2, 2, 2, 0, -2, 0, -2, 0,
    0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 0, 0, 0, -2, -2, 2, 2, -2, 0, 0, 0, -2, 0, 0, 0, 2, 4, 0, 0, 2, 0, 2].getD k 0

private def countNorm (Q : ℤ → ℤ → ℤ) (k : ℕ) : ℕ :=
  ((characterThetaTermsUpTo Q 64).filter (fun p ↦ (Q p.1 p.2).toNat = k)).card

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private theorem gauss23ThetaCoefficient_correct : ∀ k : Fin 65,
    ((countNorm discriminant23PrincipalForm k.val : ℕ) : ℤ) -
      (countNorm discriminant23OtherForm k.val : ℤ) = gauss23ThetaCoefficient k.val := by
  decide +kernel

private theorem class_sum_by_norm (Q : ℤ → ℤ → ℤ) (q : ℝ) :
    (∑ p ∈ characterThetaTermsUpTo Q 64, q ^ (Q p.1 p.2).toNat) =
      ∑ k ∈ Finset.range 65, (countNorm Q k : ℝ) * q ^ k := by
  have hm (p : ℤ × ℤ) (hp : p ∈ characterThetaTermsUpTo Q 64) :
      (Q p.1 p.2).toNat ∈ Finset.range 65 := by
    have h : (Q p.1 p.2).toNat ≤ 64 := (mem_filter.mp hp).2.2
    exact mem_range.mpr (by omega)
  unfold countNorm
  rw [← sum_fiberwise_of_maps_to' hm (fun k ↦ q ^ k)]
  simp only [sum_const, nsmul_eq_mul]

private theorem gauss23_theta_polynomial (q : ℝ) :
    discriminant23CharacterPolynomialUpTo 64 q =
      ∑ k ∈ Finset.range 65, (gauss23ThetaCoefficient k : ℝ) * q ^ k := by
  unfold discriminant23CharacterPolynomialUpTo
  rw [class_sum_by_norm, class_sum_by_norm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sub_mul]
  congr 1
  exact_mod_cast (gauss23ThetaCoefficient_correct ⟨k, Finset.mem_range.mp hk⟩)

def gauss23ThetaPolynomialBox (q : Box) : Box :=
  horner q (coefficients (fun k ↦ constant (gauss23ThetaCoefficient k)) 0 65)

private theorem gauss23_thetaPolynomialBox_contains {q : Box} {x : ℝ} (h : Contains q x) :
    Contains (gauss23ThetaPolynomialBox q) (discriminant23CharacterPolynomialUpTo 64 x) := by
  rw [gauss23_theta_polynomial]
  simpa only [gauss23ThetaPolynomialBox, Nat.zero_add] using horner_contains h
    (fun k ↦ constant (gauss23ThetaCoefficient k)) (fun k ↦ (gauss23ThetaCoefficient k : ℝ))
    (fun _ ↦ constant_contains _) 0 65

def gauss23LogWeight (i : Fin 24) : ℝ := (gauss24Weight i : ℝ) / 8

def gauss23WeightBox (i : Fin 24) : Box :=
  fromRatio (gauss24Pair i).2 gauss23NodeDenominator

theorem gauss23_weightBox_contains (i : Fin 24) : Contains (gauss23WeightBox i) (gauss23LogWeight i) := by
  have hD : (0 : ℝ) < (gauss24Denominator : ℝ) := by norm_num [gauss24Denominator]
  have hw : gauss23LogWeight i = ((gauss24Pair i).2 : ℝ) / (gauss23NodeDenominator : ℝ) := by
    unfold gauss23LogWeight gauss24Weight gauss23NodeDenominator
    push_cast
    field_simp [hD.ne']
  rw [hw]
  exact ratio_contains (gauss24Pair i).2
    (by norm_num [gauss23NodeDenominator, gauss24Denominator])

def gauss23Amplitude (j : Fin 16) (i : Fin 24) : ℝ :=
  let u := gauss23LogNode j i
  gauss23LogWeight i * Real.exp (u / 2) *
    discriminant23CharacterPolynomialUpTo 64 (Real.exp (-discriminant23ThetaScale * Real.exp u))

def gauss23AmplitudeBox (j : Fin 16) (i : Fin 24) : Box :=
  let half := expFixed (divInt (gauss23NodeBox j i) 2)
  let heat := expFixed (neg (mul discriminant23TightThetaScaleBox (mul half half)))
  mul (mul (gauss23WeightBox i) half) (gauss23ThetaPolynomialBox heat)

theorem gauss23_amplitudeBox_contains (j : Fin 16) (i : Fin 24) :
    Contains (gauss23AmplitudeBox j i) (gauss23Amplitude j i) := by
  let u := gauss23LogNode j i
  obtain ⟨hu₀, hu₁⟩ := gauss23_node_limits j i
  have hhalf : |u / 2| ≤ 128 :=
    abs_le.mpr ⟨by dsimp [u]; linarith only [hu₀], by dsimp [u]; linarith only [hu₁]⟩
  have hH : Contains (divInt (gauss23NodeBox j i) 2) (u / 2) := by
    simpa only [u, Int.cast_ofNat] using
      divInt_contains (gauss23_nodeBox_contains j i) (by norm_num : (0 : ℤ) < 2)
  have hE := expFixed_contains hH hhalf
  have huE : Contains (mul (expFixed (divInt (gauss23NodeBox j i) 2))
        (expFixed (divInt (gauss23NodeBox j i) 2))) (Real.exp u) := by
    have h := mul_contains hE hE
    rwa [← Real.exp_add, show u / 2 + u / 2 = u by ring] at h
  have hp := discriminant23_thetaScale_interval
  have hue : Real.exp u ≤ 81 := by
    refine (Real.exp_le_exp.mpr hu₁).trans ?_
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_nonneg _) Real.exp_one_lt_three.le 4).trans (by norm_num)
  have hHeat : |-(discriminant23ThetaScale * Real.exp u)| ≤ 128 := by
    rw [abs_neg, abs_of_nonneg (mul_nonneg (by linarith only [hp.1]) (Real.exp_nonneg _))]
    exact (mul_le_mul hp.2 hue (Real.exp_nonneg _) (by norm_num)).trans (by norm_num)
  have hh := expFixed_contains (neg_contains (mul_contains discriminant23_tightThetaScaleBox_contains huE)) hHeat
  have h := mul_contains (mul_contains (gauss23_weightBox_contains i) hE) (gauss23_thetaPolynomialBox_contains hh)
  simpa only [gauss23AmplitudeBox, gauss23Amplitude, u, neg_mul] using h

#print axioms discriminant23_tightThetaScaleBox_contains
#print axioms gauss23_amplitudeBox_contains

end

end FieldTarget
