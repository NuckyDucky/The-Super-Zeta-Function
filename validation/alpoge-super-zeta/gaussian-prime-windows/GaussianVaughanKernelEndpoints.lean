import GaussianVaughanConvolvedKernel

/-! The two-scale theta kernel is exponentially small at the low cutoff.
Its Gaussian convolution has an exponential envelope at the large cutoff. -/

namespace AlpogeSuperZeta

open Complex QuarticModel

noncomputable section

private theorem seventhKernel_small_exp {v : ℝ} (hv : 0 < v)
    (h : 2 ≤ (v ^ 7)⁻¹ / archivedThetaScale) :
    |archivedGaussianSeventhFreeKernel v| ≤
      (4 * archivedThetaScale) * Real.exp (-((v ^ 7)⁻¹ / archivedThetaScale / 2)) := by
  let a := archivedThetaScale
  have ha : 0 < a := archivedThetaScale_pos
  let u := (v ^ 7)⁻¹ / a
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hInv : (v ^ 7)⁻¹ = a * u := by dsimp [u]; field_simp
  have hExp : u ≤ 2 * Real.exp (u / 2) := by linarith [Real.add_one_le_exp (u / 2)]
  refine (archivedGaussianSeventhFreeKernel_lowerTail hv h).trans ?_
  change (v ^ 7)⁻¹ * (2 * Real.exp (-u)) ≤ (4 * a) * Real.exp (-(u / 2))
  rw [hInv]
  calc
    _ = (2 * a) * u * Real.exp (-u) := by ring
    _ ≤ (2 * a) * (2 * Real.exp (u / 2)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hExp (by positivity))
        (Real.exp_pos _).le
    _ = (4 * a) * (Real.exp (u / 2) * Real.exp (-u)) := by ring
    _ = _ := by rw [← Real.exp_add, show u / 2 + -u = -(u / 2) by ring]

theorem archivedGaussianVaughanKernel_small_exp :
    ∃ C > 0, ∃ c > 0, ∀ v > (0 : ℝ), v ^ (7 : ℕ) ≤ c →
      |archivedGaussianVaughanKernel v| ≤ C * Real.exp (-(c / v ^ (7 : ℕ))) := by
  let a := archivedThetaScale
  have ha : 0 < a := archivedThetaScale_pos
  let b := Real.exp (1 / 2 * Real.log 2)
  let c := (256 * a)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨4 * a + b * (4 * a), by dsimp [b]; positivity, c, hc, fun v hv hvCut => ?_⟩
  have hInv : 256 * a ≤ (v ^ (7 : ℕ))⁻¹ := by
    have h := inv_anti₀ (pow_pos hv 7) hvCut
    dsimp only [c] at h
    rw [inv_inv] at h
    exact h
  have hv₂ : 0 < 2 * v := by positivity
  have hTwo : ((2 * v) ^ (7 : ℕ))⁻¹ = (1 / 128 : ℝ) * (v ^ (7 : ℕ))⁻¹ := by
    rw [mul_pow, mul_inv]
    norm_num
  have h₁ : 2 ≤ (v ^ (7 : ℕ))⁻¹ / a := (le_div_iff₀ ha).mpr (by linarith)
  have h₂ : 2 ≤ ((2 * v) ^ (7 : ℕ))⁻¹ / a := by
    rw [hTwo, le_div_iff₀ ha]
    linarith
  have hSame : ((2 * v) ^ (7 : ℕ))⁻¹ / a / 2 = c / v ^ (7 : ℕ) := by
    rw [hTwo]
    dsimp only [c]
    field_simp [ha.ne', hv.ne']
    ring
  have hLe : ((2 * v) ^ (7 : ℕ))⁻¹ / a / 2 ≤ (v ^ (7 : ℕ))⁻¹ / a / 2 := by
    rw [hTwo]
    gcongr
    exact mul_le_of_le_one_left (by positivity) (by norm_num)
  change |archivedGaussianSeventhFreeKernel v - b * archivedGaussianSeventhFreeKernel (2 * v)| ≤ _
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hV := seventhKernel_small_exp hv h₁
  have hU := seventhKernel_small_exp hv₂ h₂
  change _ ≤ (4 * a) * Real.exp (-((v ^ 7)⁻¹ / a / 2)) at hV
  change _ ≤ (4 * a) * Real.exp (-(((2 * v) ^ 7)⁻¹ / a / 2)) at hU
  rw [hSame] at hU hLe
  calc
    _ ≤ (4 * a) * Real.exp (-(c / v ^ 7)) + b * ((4 * a) * Real.exp (-(c / v ^ 7))) := by
      exact add_le_add
        (hV.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hLe)) (by positivity)))
        (mul_le_mul_of_nonneg_left hU (by positivity))
    _ = _ := by ring

theorem archivedGaussianVaughanKernel_large_exp :
    ∃ C > 0, ∃ c > 0, ∃ T ≥ (1 : ℝ), ∀ v ≥ T,
      |archivedGaussianVaughanKernel v| ≤ C * Real.exp (-(c * v ^ (7 : ℕ))) := by
  let a := archivedThetaScale
  have ha : 0 < a := archivedThetaScale_pos
  let b := Real.exp (1 / 2 * Real.log 2)
  let T := max 1 (2 * a)
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨2 + 2 * b, by dsimp [b]; positivity, a⁻¹, inv_pos.mpr ha, T, hT, fun v hv => ?_⟩
  have hv₁ := hT.trans hv
  have hv₀ := zero_lt_one.trans_le hv₁
  have h₀ : 2 * a ≤ v ^ (7 : ℕ) :=
    ((le_max_right _ _).trans hv).trans (le_self_pow₀ hv₁ (by decide))
  have h₂ : v ^ (7 : ℕ) ≤ (2 * v) ^ (7 : ℕ) :=
    pow_le_pow_left₀ hv₀.le (by linarith) _
  have hV := archivedGaussianSeventhFreeKernel_upperTail ((le_div_iff₀ ha).mpr h₀)
  have hU := archivedGaussianSeventhFreeKernel_upperTail ((le_div_iff₀ ha).mpr (h₀.trans h₂))
  have hE : Real.exp (-((2 * v) ^ (7 : ℕ) / a)) ≤ Real.exp (-(a⁻¹ * v ^ (7 : ℕ))) := by
    rw [div_eq_mul_inv, mul_comm a⁻¹]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right h₂ (inv_nonneg.mpr ha.le)))
  change |archivedGaussianSeventhFreeKernel v - b * archivedGaussianSeventhFreeKernel (2 * v)| ≤ _
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h₁ : |archivedGaussianSeventhFreeKernel v| ≤ 2 * Real.exp (-(a⁻¹ * v ^ (7 : ℕ))) := by
    simpa only [div_eq_mul_inv, mul_comm a⁻¹] using hV
  calc
    _ ≤ 2 * Real.exp (-(a⁻¹ * v ^ (7 : ℕ))) + b * (2 * Real.exp (-(a⁻¹ * v ^ (7 : ℕ)))) :=
      add_le_add h₁ (mul_le_mul_of_nonneg_left
        (hU.trans (mul_le_mul_of_nonneg_left hE (by norm_num))) (by dsimp [b]; positivity))
    _ = _ := by ring

private theorem exp_neg_linear_inv_sq {c v : ℝ} (hc : 0 < c) (hv : 0 < v) :
    Real.exp (-(c * v)) ≤ (2 / c ^ (2 : ℕ)) / v ^ (2 : ℕ) := by
  have h := Real.pow_div_factorial_le_exp (x := c * v) (by positivity) 2
  norm_num at h
  rw [Real.exp_neg]
  calc
    _ ≤ (((c * v) ^ (2 : ℕ)) / 2)⁻¹ := inv_anti₀ (by positivity) h
    _ = _ := by field_simp [hc.ne', hv.ne']

theorem archivedGaussianVaughanConvolvedKernel_large_exp :
    ∃ C ≥ 0, ∃ c > 0, ∃ T ≥ (1 : ℝ), ∀ v ≥ T,
      |archivedGaussianVaughanConvolvedKernel v| ≤
        C * Real.exp (-(c * v ^ (7 : ℕ))) / v ^ (2 : ℕ) := by
  obtain ⟨D, hD, c, hc, T, hT, hH⟩ := archivedGaussianVaughanKernel_large_exp
  let e := c / 2
  have he : 0 < e := by dsimp [e]; positivity
  let b (n : ℕ) := ‖LSeries.term signedIdealCoefficients (2 : ℂ) n‖
  have hsum : Summable b := (archivedGaussianFactor_hasSum (w := (2 : ℂ))
    (by norm_num)).LSeriesSummable.norm
  refine ⟨D * (2 / e ^ (2 : ℕ)) * ∑' n, b n,
    by positivity [show 0 ≤ ∑' n, b n from tsum_nonneg fun _ => norm_nonneg _],
    e, he, T, hT, fun v hv => ?_⟩
  have hv₁ := hT.trans hv
  have hv₀ := zero_lt_one.trans_le hv₁
  let f (n : ℕ) := (signedIdealCoefficients n).re * archivedGaussianVaughanKernel (n * v)
  let M := (D * (2 / e ^ (2 : ℕ))) * Real.exp (-(e * v ^ (7 : ℕ))) / v ^ (2 : ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hNorm (n : ℕ) : ‖f n‖ ≤ M * b n := by
    by_cases hn : n = 0
    · subst n
      simp [f, b]
    let u : ℝ := n * v
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn₀ := zero_lt_one.trans_le hn₁
    have hvu : v ≤ u := le_mul_of_one_le_left hv₀.le hn₁
    have hu₁ := hv₁.trans hvu
    have hu₀ := zero_lt_one.trans_le hu₁
    have hSep : Real.exp (-(c * u ^ (7 : ℕ))) ≤
        Real.exp (-(e * v ^ (7 : ℕ))) * Real.exp (-(e * u)) := by
      have h₁ := pow_le_pow_left₀ hv₀.le hvu (7 : ℕ)
      have h₂ := le_self_pow₀ hu₁ (by decide : (7 : ℕ) ≠ 0)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp only [e]
      linarith [mul_le_mul_of_nonneg_left h₁ hc.le, mul_le_mul_of_nonneg_left h₂ hc.le]
    have hb : b n = ‖signedIdealCoefficients n‖ / (n : ℝ) ^ (2 : ℕ) := by
      change ‖LSeries.term signedIdealCoefficients (2 : ℂ) n‖ = _
      rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hn₀]
      norm_num [Real.rpow_two]
    change ‖(signedIdealCoefficients n).re * archivedGaussianVaughanKernel u‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ ‖signedIdealCoefficients n‖ * (D * Real.exp (-(c * u ^ (7 : ℕ)))) :=
        mul_le_mul (Complex.abs_re_le_norm _) (hH u (hv.trans hvu)) (abs_nonneg _) (norm_nonneg _)
      _ ≤ ‖signedIdealCoefficients n‖ *
          (D * (Real.exp (-(e * v ^ (7 : ℕ))) * ((2 / e ^ (2 : ℕ)) / u ^ (2 : ℕ)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hSep.trans (mul_le_mul_of_nonneg_left (exp_neg_linear_inv_sq he hu₀)
            (Real.exp_pos _).le)) hD.le) (norm_nonneg _)
      _ = _ := by rw [hb]; dsimp [M, u]; field_simp [hn₀.ne', hv₀.ne']
  rw [archivedGaussianVaughanConvolvedKernel, ← Real.norm_eq_abs]
  have hf := (hsum.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hNorm
  refine (norm_tsum_le_tsum_norm hf).trans ((hf.tsum_le_tsum hNorm (hsum.mul_left M)).trans_eq ?_)
  rw [tsum_mul_left]
  dsimp [M]
  ring

#print axioms archivedGaussianVaughanKernel_small_exp
#print axioms archivedGaussianVaughanKernel_large_exp
#print axioms archivedGaussianVaughanConvolvedKernel_large_exp

end
end AlpogeSuperZeta
