import Discriminant23ClassMellinGauss
import CenteredExponentialSum

namespace FieldTarget

open Finset Complex Set

noncomputable section

private def classGaussNodes : Finset (ℕ × Fin 24) := Finset.range 32 ×ˢ Finset.univ

private def classGaussNode (p : ℕ × Fin 24) : ℝ :=
  ((2 * (p.1 : ℝ) + 1) + (gauss24Node p.2 : ℝ)) / 16

private def classGaussAmplitude (b : ℝ) (p : ℕ × Fin 24) : ℂ :=
  let u := (classGaussNode p : ℂ)
  ((gauss24Weight p.2 : ℝ) / 32 : ℝ) *
    (Complex.exp u * discriminant23ClassCombinationPolynomial b 80
      (Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp u)))

private def classGaussPlus (b : ℝ) (c : ℂ) (p : ℕ × Fin 24) : ℂ :=
  classGaussAmplitude b p * Complex.exp ((c - 1) * (classGaussNode p : ℂ))

private def classGaussMinus (b : ℝ) (c : ℂ) (p : ℕ × Fin 24) : ℂ :=
  classGaussAmplitude b p * Complex.exp (-c * (classGaussNode p : ℂ))

/-- One coefficient of the common expansion of the quadrature about c. -/
def discriminant23ClassCombinationTaylorCoeff (b : ℝ) (c : ℂ) (k : ℕ) : ℂ :=
  centeredExponentialSumCoeff classGaussNodes classGaussNode
    (classGaussPlus b c) (classGaussMinus b c) k

private theorem quadrature_eq_centered (b : ℝ) (c d : ℂ) :
    discriminant23ClassCombinationQuadrature b (c + d) =
      centeredExponentialSum classGaussNodes classGaussNode (classGaussPlus b c)
        (classGaussMinus b c) d := by
  rw [discriminant23ClassCombinationQuadrature, rationalCompositeRule, div_eq_mul_inv,
    Finset.sum_mul, centeredExponentialSum, classGaussNodes, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  rw [rationalPanelRule, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hNode : (0 : ℝ) + (2 * (j : ℝ) + 1) * (1 / 16) + (1 / 16) * (gauss24Node i : ℝ) =
      classGaussNode (j, i) := by
    dsimp only [classGaussNode]
    ring
  rw [hNode]
  let u : ℂ := (classGaussNode (j, i) : ℝ)
  have hPlus : Complex.exp ((c + d - 1) * u) =
      Complex.exp ((c - 1) * u) * Complex.exp (u * d) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hMinus : Complex.exp (-(c + d) * u) =
      Complex.exp (-c * u) * Complex.exp (-(u * d)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold classGaussPlus classGaussMinus classGaussAmplitude discriminant23ClassCombinationIntegrand
  dsimp only [u] at hPlus hMinus
  rw [hPlus, hMinus]
  push_cast
  ring

private theorem classGaussNode_mem (p : ℕ × Fin 24) (hp : p ∈ classGaussNodes) :
    classGaussNode p ∈ Icc (0 : ℝ) 4 := by
  have hj := Finset.mem_range.mp (Finset.mem_product.mp hp).1
  have hPanel : (p.1 : ℝ) ≤ 31 := by exact_mod_cast (show p.1 ≤ 31 by omega)
  have hc := abs_le.mp (gauss24_node_abs_le p.2)
  have h0 : (0 : ℝ) ≤ (p.1 : ℝ) := Nat.cast_nonneg _
  exact ⟨by unfold classGaussNode; linarith only [hc.1, h0],
    by unfold classGaussNode; linarith only [hc.2, hPanel]⟩

private theorem classGauss_amplitude_norm_le {b : ℝ} (hb : |b| ≤ 2)
    (p : ℕ × Fin 24) (hp : p ∈ classGaussNodes) :
    ‖classGaussAmplitude b p‖ ≤ ((gauss24Weight p.2 : ℝ) / 32) * 12 := by
  have hu := (classGaussNode_mem p hp).1
  have hx : -1 / 2 ≤ ((classGaussNode p : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith only [hu]
  have hy : |((classGaussNode p : ℝ) : ℂ).im| ≤ 1 / 2 := by norm_num
  unfold classGaussAmplitude
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hweight := div_nonneg (gauss24_weight_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 32)
  rw [abs_of_nonneg hweight]
  have hDensity := discriminant23_classCombination_density_norm_le hb hx hy
  rw [norm_mul] at hDensity
  exact mul_le_mul_of_nonneg_left hDensity hweight

private theorem classGauss_total_mass_le {b : ℝ} (hb : |b| ≤ 2) {c : ℂ}
    (hlo : 0 ≤ c.re) (hhi : c.re ≤ 1) :
    (∑ p ∈ classGaussNodes, (‖classGaussPlus b c p‖ + ‖classGaussMinus b c p‖)) ≤ 72 := by
  have hPoint (p : ℕ × Fin 24) (hp : p ∈ classGaussNodes) :
      ‖classGaussPlus b c p‖ + ‖classGaussMinus b c p‖ ≤ (gauss24Weight p.2 : ℝ) * (3 / 4) := by
    let u := classGaussNode p
    have hu : 0 ≤ u := (classGaussNode_mem p hp).1
    have hPhase (v : ℂ) (hv : v.re ≤ 0) : ‖Complex.exp (v * (u : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hv hu)
    have hp₁ := hPhase (c - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    have hp₂ := hPhase (-c) (by simp only [Complex.neg_re]; linarith only [hlo])
    unfold classGaussPlus classGaussMinus
    change ‖classGaussAmplitude b p * Complex.exp ((c - 1) * (u : ℂ))‖ +
      ‖classGaussAmplitude b p * Complex.exp (-c * (u : ℂ))‖ ≤ _
    rw [norm_mul, norm_mul]
    have h₁ := mul_le_of_le_one_right (norm_nonneg (classGaussAmplitude b p)) hp₁
    have h₂ := mul_le_of_le_one_right (norm_nonneg (classGaussAmplitude b p)) hp₂
    linarith only [h₁, h₂, classGauss_amplitude_norm_le hb p hp]
  have hWeights := gauss24_weight_abs_sum_le
  simp_rw [abs_of_nonneg (gauss24_weight_nonneg _)] at hWeights
  calc
    _ ≤ ∑ p ∈ classGaussNodes, (gauss24Weight p.2 : ℝ) * (3 / 4) :=
      Finset.sum_le_sum hPoint
    _ = (32 : ℝ) * ((∑ i : Fin 24, (gauss24Weight i : ℝ)) * (3 / 4)) := by
      rw [classGaussNodes, Finset.sum_product, Finset.sum_mul]
      simp
    _ ≤ _ := by linarith only [hWeights]

/-- The same 36 terms approximate every quadrature reading on the half-unit disk.
The center may be anywhere with real part in the closed critical strip. -/
theorem discriminant23_classCombination_taylor_error {b : ℝ} (hb : |b| ≤ 2)
    {c d : ℂ} (hlo : 0 ≤ c.re) (hhi : c.re ≤ 1) (hd : ‖d‖ ≤ 1 / 2) :
    ‖discriminant23ClassCombinationQuadrature b (c + d) -
      ∑ k ∈ Finset.range 36, discriminant23ClassCombinationTaylorCoeff b c k * d ^ k‖ ≤
      1 / 10 ^ 28 := by
  have hNode (p : ℕ × Fin 24) (hp : p ∈ classGaussNodes) : |classGaussNode p| ≤ 4 := by
    obtain ⟨hu, hu'⟩ := classGaussNode_mem p hp
    rwa [abs_of_nonneg hu]
  have h := centeredExponentialSum_error_le classGaussNodes classGaussNode
    (classGaussPlus b c) (classGaussMinus b c) (L := 4) (M := 72) (r := 1 / 2)
    (by norm_num) hNode (classGauss_total_mass_le hb hlo hhi) 36 (by norm_num) hd
  rw [quadrature_eq_centered]
  exact h.trans (by norm_num [Nat.factorial])

#print axioms discriminant23_classCombination_taylor_error

end
end FieldTarget
