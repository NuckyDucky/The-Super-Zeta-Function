import DottieNormPhase
import DottieCosRescale

/-! Integer evaluations and their error bounds for the weights of the
archived Dottie reference sum. -/

namespace QuarticModel

open private periodCount from DottieNormPhase

/-- Lower ticks for the reciprocal square root. -/
def inverseSqrtTicks (scale n : ℕ) : ℕ := (scale^2/n).sqrt

theorem inverseSqrtTicks_spec (scale n : ℕ) (hs : 0 < scale) (hn : 0 < n) :
    (inverseSqrtTicks scale n : ℝ)/scale ≤ 1/Real.sqrt n ∧
      1/Real.sqrt n < ((inverseSqrtTicks scale n : ℝ)+1)/scale := by
  let j := inverseSqrtTicks scale n
  have h₀ : j^2*n ≤ scale^2 := (Nat.le_div_iff_mul_le hn).mp (Nat.sqrt_le' _)
  have h₁ : scale^2 < (j+1)^2*n := by
    have h := Nat.sqrt_lt'.mp (Nat.lt_succ_self j)
    rwa [Nat.div_lt_iff_lt_mul hn] at h
  have h₀' : (j:ℝ)^2*(n:ℝ) ≤ (scale:ℝ)^2 := by exact_mod_cast h₀
  have h₁' : (scale:ℝ)^2 < ((j:ℝ)+1)^2*(n:ℝ) := by exact_mod_cast h₁
  have hn' : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hs' : 0 < (scale:ℝ) := by exact_mod_cast hs
  have e₀ : ((j:ℝ)*Real.sqrt n)^2 ≤ (scale:ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact h₀'
  have e₁ : (scale:ℝ)^2 < (((j:ℝ)+1)*Real.sqrt n)^2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    exact h₁'
  constructor
  · apply (div_le_div_iff₀ hs' hn').2
    simpa only [one_mul] using
      (pow_le_pow_iff_left₀ (by positivity : 0 ≤ (j:ℝ)*Real.sqrt n) hs'.le (by decide : (2:ℕ) ≠ 0)).1 e₀
  · apply (div_lt_div_iff₀ hn' hs').2
    simpa only [one_mul] using
      (pow_lt_pow_iff_left₀ hs'.le (by positivity : 0 ≤ ((j:ℝ)+1)*Real.sqrt n) (by decide : (2:ℕ) ≠ 0)).1 e₁

private def quarticCosine (x : ℝ) := 8*x^4-8*x^2+1

private theorem cos_four (x : ℝ) : Real.cos (4*x) = quarticCosine (Real.cos x) := by
  rw [show 4*x = 2*(2*x) by ring, Real.cos_two_mul, Real.cos_two_mul]
  unfold quarticCosine
  ring

private theorem quarticCosine_distance (x y : ℝ) (hx : |x| ≤ 2) (hy : |y| ≤ 2) :
    |quarticCosine x-quarticCosine y| ≤ 288*|x-y| := by
  have hxy : |x+y| ≤ 4 := (abs_add_le _ _).trans (by linarith only [hx,hy])
  have hx₂ := pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hy₂ := pow_le_pow_left₀ (abs_nonneg y) hy 2
  rw [sq_abs] at hx₂ hy₂
  have hquad : |x^2+y^2-1| ≤ 9 := by
    apply abs_le.mpr
    constructor
    · nlinarith only [sq_nonneg x, sq_nonneg y]
    · linarith only [hx₂, hy₂]
  rw [show quarticCosine x-quarticCosine y = 8*(x-y)*((x+y)*(x^2+y^2-1)) by unfold quarticCosine; ring]
  simp only [abs_mul, show |(8:ℝ)| = 8 by norm_num]
  have h := mul_le_mul hxy hquad (abs_nonneg _) (by norm_num)
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 8*|x-y| by positivity)
  linarith only [h']

private def dottieCosineQuarterTicks (n : ℕ) : ℤ :=
  (fixedCosBounds (dottieAngleNumerator n) dottieAngleDenominator).1

/-- Approximate phase cosine in ticks of `scale^4`. -/
def dottieCosineTicks (n : ℕ) : ℤ :=
  let c := dottieCosineQuarterTicks n
  let b := (fixedCosScale : ℤ)
  8*c^4-8*b^2*c^2+b^4

theorem dottieCosineTicks_spec (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    |(dottieCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 -
      Real.cos (3.9229252-4526119322477.943440197603*Real.log n)| ≤ 1/1000000 := by
  let q := dottieNormAngleQuarter n
  have hcast : (q : ℝ) = (q.num : ℝ)/q.den := Rat.cast_def q
  have hq := dottieNormAngleQuarter_abs_le n
  change |(q : ℝ)| ≤ 1 at hq
  have hab : q.num.natAbs ≤ q.den := by
    rw [hcast, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) q.den)] at hq
    have h := (div_le_one (by exact_mod_cast q.den_pos : (0:ℝ)<q.den)).mp hq
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] at h
    exact_mod_cast h
  have enclosure := fixedCosBounds_spec q.num q.den q.den_pos hab
  rw [← hcast] at enclosure
  let c : ℝ := (dottieCosineQuarterTicks n : ℝ)/fixedCosScale
  have hcEq : c = ((fixedCosBounds q.num q.den).1 : ℝ)/fixedCosScale := by
    unfold c dottieCosineQuarterTicks q
    rw [dottieAngleTicks_fixedCosBounds]
  have hlo : c ≤ Real.cos q := hcEq ▸ enclosure.1
  have hwidth := fixedCosBounds_width q.num q.den
  rw [← hcEq] at hwidth
  have hd : |c-Real.cos q| ≤ 6/2^48 := by
    apply abs_le.mpr
    constructor <;> linarith only [hlo, enclosure.2, hwidth]
  have hc : |c| ≤ 2 := by
    calc
      |c| = |c-Real.cos q+Real.cos q| := by rw [sub_add_cancel]
      _ ≤ |c-Real.cos q|+|Real.cos q| := abs_add_le ..
      _ ≤ 2 := by linarith only [hd, Real.abs_cos_le_one (q:ℝ)]
  have hT := quarticCosine_distance c (Real.cos q) hc ((Real.abs_cos_le_one _).trans (by norm_num))
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 288))
  rw [← cos_four] at hT'
  let θ : ℝ := 3.9229252-4526119322477.943440197603*Real.log n
  let p : ℝ := (periodCount n : ℝ)*(2*Real.pi)
  have hcos : Real.cos (θ-p) = Real.cos θ := by
    have h := Real.cos_add_int_mul_two_pi (θ-p) (periodCount n)
    change Real.cos (θ-p+p) = Real.cos (θ-p) at h
    rwa [sub_add_cancel, eq_comm] at h
  have hr := dottie_norm_angle_reduction n hn hcap
  change |θ-p-4*(q:ℝ)| ≤ _ at hr
  have he : |Real.cos (4*(q:ℝ))-Real.cos θ| ≤ 1/2000000 := by
    rw [← hcos, abs_sub_comm]
    exact (Real.abs_cos_sub_cos_le _ _).trans hr
  have hrepr : (dottieCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 = quarticCosine c := by
    simp only [dottieCosineTicks, c, quarticCosine, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    field [show (fixedCosScale:ℝ) ≠ 0 by norm_num [fixedCosScale]]
  rw [hrepr]
  change |quarticCosine c-Real.cos θ| ≤ _
  rw [show quarticCosine c-Real.cos θ =
    (quarticCosine c-Real.cos (4*(q:ℝ)))+(Real.cos (4*(q:ℝ))-Real.cos θ) by ring]
  exact (abs_add_le _ _).trans ((add_le_add hT' he).trans (by norm_num))

#print axioms inverseSqrtTicks_spec
#print axioms dottieCosineTicks_spec

end QuarticModel
