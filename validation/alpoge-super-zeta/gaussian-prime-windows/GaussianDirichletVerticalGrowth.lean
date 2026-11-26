import GaussianLogDerivativeDisk
import GaussianVaughanFilteredDirichlet
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

/-! Control the four filtered rational Dirichlet factors on the contour
used by the archived Gaussian higher-power Mellin transform. -/

namespace AlpogeSuperZeta

open Complex DirichletCharacter Filter Metric Set
open scoped Classical Topology

noncomputable section

/-- The Dirichlet L-function with its pole removed for the principal character. -/
def regularDirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

private theorem regularDirichlet_differentiable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Differentiable ℂ (regularDirichlet χ) := by
  by_cases hχ : χ = 1
  · simpa only [regularDirichlet, if_pos hχ] using differentiable_LFunctionTrivChar₁ N
  · simpa only [regularDirichlet, if_neg hχ] using differentiable_LFunction hχ

private theorem regularDirichlet_ne_zero (hDir : DirichletLZerosOnLine) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {w : ℂ} (hw : 1 / 2 < w.re) :
    regularDirichlet χ w ≠ 0 := by
  by_cases h₁ : w = 1
  · subst w
    by_cases hχ : χ = 1
    · simpa only [regularDirichlet, if_pos hχ] using LFunctionTrivChar₁_apply_one_ne_zero N
    · change (if χ = 1 then LFunctionTrivChar₁ N else LFunction χ) 1 ≠ 0
      rw [if_neg hχ]
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  have hL : LFunction χ w ≠ 0 := by
    by_cases hσ : w.re < 1
    · intro hzero
      have he := hDir N χ w (by linarith) hσ hzero
      linarith
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inr h₁) (le_of_not_gt hσ)
  by_cases hχ : χ = 1
  · rw [regularDirichlet, if_pos hχ, LFunctionTrivChar₁, Function.update_of_ne h₁]
    rw [hχ] at hL
    exact mul_ne_zero (sub_ne_zero.mpr h₁) hL
  · simpa only [regularDirichlet, if_neg hχ] using hL

private theorem eulerFactors_norm_le (N : ℕ) [NeZero N] {w : ℂ} (hw : 0 ≤ w.re) :
    ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-w))‖ ≤ (N : ℝ) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ N.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hp₂ : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
      have hpow : ‖(p : ℂ) ^ (-w)‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hprime.pos, neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    _ = ((∏ p ∈ N.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (N : ℝ) := by exact_mod_cast Nat.le_of_dvd (NeZero.pos N) (Nat.prod_primeFactors_dvd N)

private theorem principal_growth (N : ℕ) [NeZero N] {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    ‖LFunctionTrivChar₁ N w‖ ≤ 4 * N * (1 + ‖w‖) ^ 2 := by
  by_cases h₁ : w = 1
  · subst w
    simp only [LFunctionTrivChar₁, Function.update_self, norm_one]
    have he := eulerFactors_norm_le N (w := 1) (by simp)
    simpa only [cpow_neg_one] using he.trans (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith)
  rw [LFunctionTrivChar₁, Function.update_of_ne h₁, LFunctionTrivChar_eq_mul_riemannZeta h₁,
    norm_mul, norm_mul, mul_left_comm]
  have hzeta := Formalism.ZF.growthBound w (by linarith) h₁
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h₁)
  have hd₁ := norm_sub_le w (1 : ℂ)
  rw [norm_one] at hd₁
  have hd₂ : ‖w - 1‖ ≤ 1 + ‖w‖ := by linarith
  have hre : 1 / w.re ≤ 2 := (div_le_iff₀ (by linarith : 0 < w.re)).2 (by linarith)
  have hnorm : ‖w - 1‖ * ‖riemannZeta w‖ ≤ 4 * (1 + ‖w‖) ^ 2 := by
    calc
      _ ≤ ‖w - 1‖ * (1 + 1 / ‖w - 1‖ + ‖w‖ * (1 + 1 / w.re)) :=
        mul_le_mul_of_nonneg_left hzeta hd.le
      _ = ‖w - 1‖ + 1 + ‖w - 1‖ * (‖w‖ * (1 + 1 / w.re)) := by
        rw [mul_add, mul_add, mul_one, mul_one_div_cancel hd.ne']
      _ ≤ (1 + ‖w‖) + 1 + (1 + ‖w‖) * (‖w‖ * (1 + 2)) := by gcongr
      _ ≤ _ := by nlinarith [norm_nonneg w]
  calc
    _ ≤ (N : ℝ) * (4 * (1 + ‖w‖) ^ 2) :=
      mul_le_mul (eulerFactors_norm_le N (by linarith)) hnorm (by positivity) (Nat.cast_nonneg _)
    _ = _ := by ring

private theorem regularDirichlet_growth (N : ℕ) [NeZero N] :
    ∃ A ≥ 4, ∀ (χ : DirichletCharacter ℂ N) (w : ℂ), 1 / 2 ≤ w.re →
      ‖regularDirichlet χ w‖ ≤ A * (1 + ‖w‖) ^ 2 := by
  obtain ⟨C, hC⟩ := Formalism.ZeroFreeDirichlet.lfunction_polynomial_growth
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hm : (4 : ℝ) ≤ max 4 C := le_max_left _ _
  refine ⟨max 4 C * N, ?_, fun χ w hw => ?_⟩
  · exact (mul_one (4 : ℝ)).symm.trans_le (mul_le_mul hm hN zero_le_one (by linarith))
  by_cases hχ : χ = 1
  · rw [regularDirichlet, if_pos hχ]
    exact (principal_growth N hw).trans (by gcongr)
  rw [regularDirichlet, if_neg hχ]
  have hb : 1 ≤ 1 + ‖w‖ := by linarith [norm_nonneg w]
  calc
    _ ≤ C * N * (1 + ‖w‖) := hC N χ hχ w hw
    _ ≤ max 4 C * N * (1 + ‖w‖) := by gcongr; exact le_max_right _ _
    _ ≤ _ := by gcongr; nlinarith

private theorem regularDirichlet_center {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {c : ℂ} (hc : c.re = 2) : 1 / 2 ≤ ‖regularDirichlet χ c‖ := by
  have hσ : 1 < c.re := by rw [hc]; norm_num
  have hL₀ := LFunction_ne_zero_of_one_le_re χ
    (Or.inr (show c ≠ 1 from fun h => by rw [h, one_re] at hc; norm_num at hc)) hσ.le
  have hLpos := norm_pos_iff.mpr hL₀
  have hinv := Formalism.ZeroFreeDirichlet.inverseBound N χ c hσ
  rw [hc] at hinv
  have hL : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have hb : ‖LFunction χ c‖⁻¹ ≤ 2 := by norm_num at hinv ⊢; exact hinv
    have ht := (div_le_iff₀ hLpos).mp (by simpa only [one_div] using hb :
      1 / ‖LFunction χ c‖ ≤ 2)
    linarith
  by_cases hχ : χ = 1
  · subst χ
    have hc₁ : c ≠ 1 := by intro h; rw [h, one_re] at hc; norm_num at hc
    rw [regularDirichlet, if_pos rfl, LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul]
    have hone : 1 ≤ ‖c - 1‖ := by
      have h := Complex.re_le_norm (c - 1)
      rw [sub_re, one_re, hc] at h
      linarith
    exact hL.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hone (norm_nonneg (LFunctionTrivChar N c)))
  · simpa only [regularDirichlet, if_neg hχ] using hL

/-- For a fixed modulus, the zero-free input bounds the logarithmic
derivatives uniformly in the character and in the height. The principal
function is regularized at one before taking its logarithmic derivative. -/
theorem rationalDirichlet_logDeriv_strip (hDir : DirichletLZerosOnLine) (N : ℕ) [NeZero N] :
    ∃ C > 0, ∀ (χ : DirichletCharacter ℂ N) (w : ℂ), 3 / 4 ≤ w.re → w.re ≤ 13 / 4 →
      ‖logDeriv (regularDirichlet χ) w‖ ≤ C * (1 + Real.log (1 + |w.im|)) := by
  obtain ⟨A, hA, hgrowth⟩ := regularDirichlet_growth N
  let a := Real.log (25 * A) - Real.log (1 / 2) + 1
  have ha : 0 ≤ a := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2)
      (show (1 / 2 : ℝ) ≤ 25 * A by linarith)
    dsimp [a]
    linarith
  refine ⟨520 * (a + 2), by positivity, fun χ w hw₁ hw₂ => ?_⟩
  let c : ℂ := 2 + (w.im : ℂ) * I
  let f : ℂ → ℂ := fun u => regularDirichlet χ (c + u)
  let u := w - c
  let B := 25 * A * (1 + |w.im|) ^ 2
  have hc : c.re = 2 := by simp [c, mul_re]
  have hci : c.im = w.im := by simp [c, mul_im]
  have hcu : c + u = w := by dsimp [u]; ring
  have hu : ‖u‖ ≤ 5 / 4 := by
    have hue : u = ((w.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [u, hc]
      · simp [u, hci]
    rw [hue, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hfd : Differentiable ℂ f :=
    (regularDirichlet_differentiable χ).comp (differentiable_id.const_add c)
  have hhalf (v : ℂ) (hv : v ∈ ball (0 : ℂ) (7 / 5)) : 1 / 2 < (c + v).re := by
    have hvn := mem_ball_zero_iff.mp hv
    have hvr := (abs_le.mp (Complex.abs_re_le_norm v)).1
    rw [add_re, hc]
    linarith
  have hupper (v : ℂ) (hv : v ∈ ball (0 : ℂ) (7 / 5)) : ‖f v‖ ≤ B := by
    have hvn := mem_ball_zero_iff.mp hv
    have hcn : ‖c‖ ≤ 2 + |w.im| := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real, Real.norm_eq_abs]
    have hn := norm_add_le c v
    have hcomp : 1 + ‖c + v‖ ≤ 5 * (1 + |w.im|) := by
      linarith [abs_nonneg w.im]
    have hsq : (1 + ‖c + v‖) ^ 2 ≤ (5 * (1 + |w.im|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcomp _
    calc
      _ ≤ A * (1 + ‖c + v‖) ^ 2 := hgrowth χ _ (hhalf v hv).le
      _ ≤ A * (5 * (1 + |w.im|)) ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = B := by dsimp [B]; ring
  have hcenter : (1 / 2 : ℝ) ≤ ‖f 0‖ := by
    simpa only [f, add_zero] using regularDirichlet_center χ hc
  have hbound := logDeriv_le_disk (b := 1 / 2) (by norm_num) hcenter
    hfd.differentiableOn (fun v hv => regularDirichlet_ne_zero hDir χ (hhalf v hv)) hupper hu
  have hshift : logDeriv f u = logDeriv (regularDirichlet χ) w := by
    have hd := (regularDirichlet_differentiable χ (c + u)).hasDerivAt
    have hcomp := hd.comp u ((hasDerivAt_id u).const_add c)
    rw [logDeriv_apply, logDeriv_apply]
    change deriv f u / regularDirichlet χ (c + u) = _
    rw [hcu, show deriv f u = deriv (regularDirichlet χ) (c + u) * 1 from hcomp.deriv, hcu, mul_one]
  rw [hshift] at hbound
  have hlog : Real.log B = Real.log (25 * A) + 2 * Real.log (1 + |w.im|) := by
    dsimp [B]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hlog₀ := Real.log_nonneg (show 1 ≤ 1 + |w.im| by linarith [abs_nonneg w.im])
  refine hbound.trans ?_
  rw [hlog]
  dsimp [a] at ha ⊢
  nlinarith [mul_nonneg ha hlog₀]

#check rationalDirichlet_logDeriv_strip
#print axioms rationalDirichlet_logDeriv_strip

end
end AlpogeSuperZeta
