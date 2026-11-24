import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-! The divided odd exponential series used by the factored circle replay. -/

namespace QuarticModel

open Complex Finset
set_option autoImplicit false

private theorem neg_even_power (z : ℂ) (j : ℕ) : (-z)^(2*j) = z^(2*j) := by
  simp only [pow_mul,neg_pow_two]

private theorem neg_odd_power (z : ℂ) (j : ℕ) : (-z)^(2*j+1) = -z^(2*j+1) := by
  rw [pow_succ,neg_even_power,pow_succ]
  ring

private theorem exp_poly_odd_sum (z : ℂ) (n : ℕ) :
    (∑ k ∈ range (2*n+1), (z^k/k.factorial-(-z)^k/k.factorial)) =
      2*(∑ k ∈ range n, z^(2*k+1)/(2*k+1).factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+1+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ]
    rw [show 2*n+1+1 = 2*(n+1) by omega,neg_even_power,neg_odd_power]
    ring

private theorem exp_poly_even_sum (z : ℂ) (n : ℕ) :
    (∑ k ∈ range (2*n), (z^k/k.factorial+(-z)^k/k.factorial)) =
      2*(∑ k ∈ range n, z^(2*k)/(2*k).factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n)+1+1 by omega,
      Finset.sum_range_succ,Finset.sum_range_succ,ih,Finset.sum_range_succ,
      neg_odd_power,neg_even_power]
    ring

theorem dottie_cosh_taylor_radius {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖cosh z-∑ k ∈ range 12, z^(2*k)/(2*k).factorial‖ ≤ 2*(2:ℝ)^24/(24 : ℕ).factorial := by
  let P := fun v : ℂ => ∑ k ∈ range 24, v^k/k.factorial
  have hp : P z+P (-z) = 2*(∑ k ∈ range 12, z^(2*k)/(2*k).factorial) := by
    unfold P
    rw [← Finset.sum_add_distrib]
    exact exp_poly_even_sum z 12
  have hPos := Complex.exp_bound' (x := z) (n := 24) (by norm_num; linarith only [hz])
  have hNeg := Complex.exp_bound' (x := -z) (n := 24) (by rw [norm_neg]; norm_num; linarith only [hz])
  change ‖exp z-P z‖ ≤ ‖z‖^24/(24 : ℕ).factorial*2 at hPos
  change ‖exp (-z)-P (-z)‖ ≤ ‖-z‖^24/(24 : ℕ).factorial*2 at hNeg
  rw [norm_neg] at hNeg
  have he : cosh z-(∑ k ∈ range 12, z^(2*k)/(2*k).factorial) =
      ((exp z-P z)+(exp (-z)-P (-z)))/2 := by
    rw [Complex.cosh]
    linear_combination hp / 2
  rw [he,norm_div,Complex.norm_ofNat]
  have h := norm_add_le (exp z-P z) (exp (-z)-P (-z))
  have hpower : ‖z‖^24/(24 : ℕ).factorial*2 ≤ 2*(2:ℝ)^24/(24 : ℕ).factorial := by
    rw [show 2*(2:ℝ)^24/(24 : ℕ).factorial = (2:ℝ)^24/(24 : ℕ).factorial*2 by ring]
    gcongr
  linarith only [h,hPos,hNeg,hpower]

private theorem sinh_poly_tail {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖sinh z-∑ k ∈ range 12, z^(2*k+1)/(2*k+1).factorial‖ ≤
      2*‖z‖^25/(25 : ℕ).factorial := by
  let P := fun v : ℂ => ∑ k ∈ range 25, v^k/k.factorial
  have hp : P z-P (-z) = 2*(∑ k ∈ range 12, z^(2*k+1)/(2*k+1).factorial) := by
    unfold P
    rw [← Finset.sum_sub_distrib]
    exact exp_poly_odd_sum z 12
  have hPos := Complex.exp_bound' (x := z) (n := 25) (by norm_num; linarith only [hz])
  have hNeg := Complex.exp_bound' (x := -z) (n := 25) (by rw [norm_neg]; norm_num; linarith only [hz])
  change ‖exp z-P z‖ ≤ ‖z‖^25/(25 : ℕ).factorial*2 at hPos
  change ‖exp (-z)-P (-z)‖ ≤ ‖-z‖^25/(25 : ℕ).factorial*2 at hNeg
  rw [norm_neg] at hNeg
  have he : sinh z-(∑ k ∈ range 12, z^(2*k+1)/(2*k+1).factorial) =
      ((exp z-P z)-(exp (-z)-P (-z)))/2 := by
    rw [Complex.sinh]
    linear_combination hp / 2
  rw [he,norm_div,Complex.norm_ofNat]
  have h := norm_sub_le (exp z-P z) (exp (-z)-P (-z))
  linarith only [h,hPos,hNeg]

noncomputable def dottieDividedSinhPolynomial (c x : ℂ) : ℂ :=
  c * ∑ k ∈ range 12, (x*c)^(2*k)/(2*k+1).factorial

theorem dottie_divided_sinh_radius {c x : ℂ} (hx : x ≠ 0) (hc : ‖c‖ ≤ 46)
    (hz : ‖x*c‖ ≤ 2) :
    ‖sinh (x*c)/x-dottieDividedSinhPolynomial c x‖ ≤
      92*(2:ℝ)^24/(25 : ℕ).factorial := by
  let z := x*c
  have hsum : (∑ k ∈ range 12, z^(2*k+1)/(2*k+1).factorial) =
      x*dottieDividedSinhPolynomial c x := by
    rw [dottieDividedSinhPolynomial,← mul_assoc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    dsimp [z]
    ring
  have hp : (∑ k ∈ range 12, z^(2*k+1)/(2*k+1).factorial)/x =
      dottieDividedSinhPolynomial c x := by rw [hsum,mul_comm,mul_div_cancel_right₀ _ hx]
  change ‖sinh z/x-dottieDividedSinhPolynomial c x‖ ≤ _
  rw [← hp,← sub_div,norm_div]
  have hx₀ : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnormz : ‖z‖ = ‖x‖*‖c‖ := norm_mul _ _
  calc
    _ ≤ (2*‖z‖^25/(25 : ℕ).factorial)/‖x‖ :=
      div_le_div_of_nonneg_right (sinh_poly_tail hz) hx₀.le
    _ = (2*‖z‖^24*‖c‖)/(25 : ℕ).factorial := by
      rw [show ‖z‖^25 = ‖z‖^24*(‖x‖*‖c‖) by rw [pow_succ,← hnormz]]
      field_simp [hx₀.ne']
    _ ≤ _ := by
      rw [show (92:ℝ)*2^24 = 2*2^24*46 by ring]
      gcongr

#print axioms dottie_divided_sinh_radius
#print axioms dottie_cosh_taylor_radius

end QuarticModel
