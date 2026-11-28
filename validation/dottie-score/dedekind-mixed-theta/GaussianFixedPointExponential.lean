import GaussianRationalPolynomial
import ComplexExponentialDyadic

namespace FieldTarget

open Complex
open scoped BigOperators

noncomputable section

/-- Floor each component on the common Gaussian-integer grid. -/
def gaussianFloorDiv (a : GaussianInt) (d : ℕ) : GaussianInt :=
  ⟨a.re / (d : ℤ), a.im / (d : ℤ)⟩

theorem norm_gaussianFloorDiv_error (a : GaussianInt) {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) :
    ‖gaussianScaled a (s * d) - gaussianScaled (gaussianFloorDiv a d) s‖ ≤ 2 / (s : ℝ) := by
  let R := a - (d : GaussianInt) * gaussianFloorDiv a d
  have hCast : ((d : GaussianInt) : ℂ) = (d : ℂ) := map_natCast GaussianInt.toComplex d
  have hEq : gaussianScaled a (s * d) - gaussianScaled (gaussianFloorDiv a d) s =
      gaussianScaled R (s * d) := by
    simp only [gaussianScaled, R, GaussianInt.toComplex_sub, GaussianInt.toComplex_mul, hCast, Nat.cast_mul]
    have h₀ : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have h₁ : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  have hRe : R.re = a.re % (d : ℤ) := by
    simp only [R, gaussianFloorDiv, Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      mul_zero, zero_mul, add_zero]
    have h := Int.emod_add_ediv_mul a.re (d : ℤ)
    rw [mul_comm (a.re / (d : ℤ)) (d : ℤ)] at h
    omega
  have hIm : R.im = a.im % (d : ℤ) := by
    simp only [R, gaussianFloorDiv, Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
      zero_mul, add_zero]
    have h := Int.emod_add_ediv_mul a.im (d : ℤ)
    rw [mul_comm (a.im / (d : ℤ)) (d : ℤ)] at h
    omega
  have hD : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hNat (n : ℤ) : (n % (d : ℤ)).natAbs ≤ d := by
    have h₀ := Int.emod_nonneg n hD.ne'
    have h₁ := Int.emod_lt_of_pos n hD
    omega
  have hL1 : gaussianL1 R ≤ 2 * d := by
    rw [gaussianL1, hRe, hIm]
    have := add_le_add (hNat a.re) (hNat a.im)
    omega
  have hNatScaled : gaussianL1 R * s ≤ (s * d) * 2 := by
    convert Nat.mul_le_mul_right s hL1 using 1
    ring
  rw [hEq]
  simpa only [Nat.cast_ofNat] using norm_gaussianScaled_le_of_l1 (Nat.mul_pos hs hd) hs hNatScaled

/-- Approximate successive terms z^k/k! without growing the grid denominator. -/
def gaussianTaylorTerm (a : GaussianInt) (d s : ℕ) : ℕ → GaussianInt
  | 0 => (s : GaussianInt)
  | k + 1 => gaussianFloorDiv (a * gaussianTaylorTerm a d s k) (d * (k + 1))

def gaussianTaylorSum (a : GaussianInt) (d s n : ℕ) : GaussianInt :=
  ∑ k ∈ Finset.range n, gaussianTaylorTerm a d s k

theorem norm_gaussianTaylorTerm_error (a : GaussianInt) {d s : ℕ} (hd : 0 < d) (hs : 0 < s)
    (hz : ‖gaussianScaled a d‖ ≤ 1 / 2) (k : ℕ) :
    ‖(gaussianScaled a d) ^ k / (k.factorial : ℂ) - gaussianScaled (gaussianTaylorTerm a d s k) s‖ ≤
      4 / (s : ℝ) := by
  let z := gaussianScaled a d
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  induction k with
  | zero =>
      rw [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, gaussianTaylorTerm, gaussianScaled,
        show ((s : GaussianInt) : ℂ) = (s : ℂ) from map_natCast GaussianInt.toComplex s,
        div_self hs', sub_self, norm_zero]
      positivity
  | succ k ih =>
      let P := z ^ k / (k.factorial : ℂ)
      let T := gaussianScaled (gaussianTaylorTerm a d s k) s
      have hk : (k.succ : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      have h₀ : z ^ k.succ / (k.succ.factorial : ℂ) = z * P / (k.succ : ℂ) := by
        unfold P
        rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
        have hkF : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
        field_simp
      have h₁ : z * T / (k.succ : ℂ) =
          gaussianScaled (a * gaussianTaylorTerm a d s k) (s * (d * k.succ)) := by
        simp only [z, T, gaussianScaled, GaussianInt.toComplex_mul, Nat.cast_mul]
        field_simp
      have hMul : ‖z * P / (k.succ : ℂ) - z * T / (k.succ : ℂ)‖ ≤ 2 / (s : ℝ) := by
        rw [← sub_div, ← mul_sub, norm_div, norm_mul, Complex.norm_natCast]
        have hk1 : (1 : ℝ) ≤ k.succ := by exact_mod_cast (Nat.succ_pos k)
        have hProd := mul_le_mul hz ih (norm_nonneg (P - T)) (by norm_num)
        exact (div_le_self (by positivity) hk1).trans (hProd.trans_eq (by ring))
      have hRound := norm_gaussianFloorDiv_error (a * gaussianTaylorTerm a d s k)
        (Nat.mul_pos hd (Nat.succ_pos k)) hs
      rw [← h₁] at hRound
      change ‖z ^ k.succ / (k.succ.factorial : ℂ) -
        gaussianScaled (gaussianFloorDiv (a * gaussianTaylorTerm a d s k) (d * k.succ)) s‖ ≤ _
      rw [h₀]
      exact ((norm_sub_le_norm_sub_add_norm_sub _ (z * T / (k.succ : ℂ)) _).trans
        (add_le_add hMul hRound)).trans_eq (by ring)

/-- A kernel-checkable evaluation using only integer products, floors and sums. -/
theorem norm_exp_sub_gaussianTaylorSum (a : GaussianInt) {d s : ℕ} (hd : 0 < d) (hs : 0 < s)
    (hz : ‖gaussianScaled a d‖ ≤ 1 / 2) (n : ℕ) :
    ‖Complex.exp (gaussianScaled a d) - gaussianScaled (gaussianTaylorSum a d s n) s‖ ≤
      (1 / 2 : ℝ) ^ n / n.factorial * 2 + (n : ℝ) * (4 / (s : ℝ)) := by
  let z := gaussianScaled a d
  let P := ∑ k ∈ Finset.range n, z ^ k / (k.factorial : ℂ)
  have hSum : gaussianScaled (gaussianTaylorSum a d s n) s =
      ∑ k ∈ Finset.range n, gaussianScaled (gaussianTaylorTerm a d s k) s := by
    unfold gaussianScaled gaussianTaylorSum
    rw [map_sum, Finset.sum_div]
  have hCut : ‖z‖ / (n.succ : ℝ) ≤ 1 / 2 :=
    (div_le_self (norm_nonneg z) (by exact_mod_cast (Nat.succ_pos n))).trans hz
  have hTail : ‖Complex.exp z - P‖ ≤ (1 / 2 : ℝ) ^ n / n.factorial * 2 := by
    refine (Complex.exp_bound' hCut).trans ?_
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz n) (by positivity)) (by norm_num)
  have hRound : ‖P - gaussianScaled (gaussianTaylorSum a d s n) s‖ ≤ (n : ℝ) * (4 / (s : ℝ)) := by
    rw [hSum]
    dsimp only [P]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖z ^ k / (k.factorial : ℂ) -
          gaussianScaled (gaussianTaylorTerm a d s k) s‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range n, (4 / (s : ℝ)) :=
        Finset.sum_le_sum (fun k _ ↦ norm_gaussianTaylorTerm_error a hd hs hz k)
      _ = _ := by simp
  exact (norm_sub_le_norm_sub_add_norm_sub _ P _).trans (add_le_add hTail hRound)

#print axioms norm_gaussianFloorDiv_error
#print axioms norm_gaussianTaylorTerm_error
#print axioms norm_exp_sub_gaussianTaylorSum

end
end FieldTarget
