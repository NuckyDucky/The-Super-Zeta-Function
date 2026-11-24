import DottieNormLog
import DottieRationalProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Rat.Floor

/-! Compute a small rational angle for each norm in the signed reference
sum. The enclosure accounts for multiplying the logarithm by the full
Dottie height and for the large integer number of discarded periods. -/

namespace QuarticModel

private def piLower : ℚ := 3.14159265358979323846

private def referenceHeightRat : ℚ := 4526119322477.943440197603

private def referenceAngleRat : ℚ := 3.9229252

private def normAngleOf (ticks : ℕ) : ℚ :=
  referenceAngleRat - referenceHeightRat * (ticks : ℚ) / 2^96

/-- The integer period subtracted to center the phase formed from log ticks at scale `2^96`. -/
def dottieNormPeriodCountOf (ticks : ℕ) : ℤ := ⌊(normAngleOf ticks + piLower) / (2 * piLower)⌋

private def periodCount (n : ℕ) : ℤ := dottieNormPeriodCountOf (normLogBounds (2^96) 31 n).1

/-- The centered quarter angle for log ticks at scale `2^96`. -/
def dottieNormAngleQuarterOf (ticks : ℕ) : ℚ :=
  (normAngleOf ticks - dottieNormPeriodCountOf ticks * (2 * piLower)) / 4

/-- Bounded argument at which to evaluate a cosine and then use the
quadruple-angle formula. Norms run through the exact reference cutoff. -/
def dottieNormAngleQuarter (n : ℕ) : ℚ := dottieNormAngleQuarterOf (normLogBounds (2^96) 31 n).1

private theorem lower_log_accurate (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    0 ≤ Real.log n - ((normLogBounds (2^96) 31 n).1 : ℝ)/2^96 ∧
      Real.log n - ((normLogBounds (2^96) 31 n).1 : ℝ)/2^96 ≤ (120:ℝ)/2^96 := by
  have hvalid := normLogBounds_spec (2^96) 31 n (by decide +kernel) hn
  have hw := normLogBounds_width (2^96) 31 n hn (by omega : n ≤ 2^29)
  rw [show 30 * logAtanhErrorTicks (2^96) 31 = 120 by decide +kernel] at hw
  have hw' : (normLogBounds (2^96) 31 n).2 ≤ (normLogBounds (2^96) 31 n).1 + 120 := by
    omega
  have hw'' : ((normLogBounds (2^96) 31 n).2 : ℝ) ≤ (normLogBounds (2^96) 31 n).1 + 120 := by
    exact_mod_cast hw'
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hvalid
  constructor
  · linarith only [hvalid.1]
  · linarith only [hvalid.2, div_le_div_of_nonneg_right hw'' (by positivity : (0:ℝ) ≤ 2^96)]

private theorem log_lt_twenty (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    Real.log n < 20 := by
  have hp : (2.7 : ℝ)^20 ≤ Real.exp 20 := by
    rw [show (20:ℝ) = (20:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
  have h : (n : ℝ) ≤ 276824064 := by exact_mod_cast hcap
  exact (Real.log_lt_iff_lt_exp (by exact_mod_cast hn)).mpr
    (h.trans_lt ((by norm_num : (276824064:ℝ) < 2.7^20).trans_le hp))

private theorem periodCountOf_bounds (ticks : ℕ) :
    (dottieNormPeriodCountOf ticks : ℝ) ≤ ((normAngleOf ticks : ℝ)+piLower)/(2*(piLower : ℝ)) ∧
    ((normAngleOf ticks : ℝ)+piLower)/(2*(piLower : ℝ)) < (dottieNormPeriodCountOf ticks : ℝ)+1 := by
  have h := Int.floor_le ((normAngleOf ticks+piLower)/(2*piLower))
  have h' := Int.lt_floor_add_one ((normAngleOf ticks+piLower)/(2*piLower))
  constructor
  · exact_mod_cast h
  · exact_mod_cast h'

theorem dottieNormAngleQuarterOf_abs_le (ticks : ℕ) :
    |(dottieNormAngleQuarterOf ticks : ℝ)| ≤ 1 := by
  obtain ⟨hl,hu⟩ := periodCountOf_bounds ticks
  have hp : (0:ℝ) < 2*(piLower : ℝ) := by norm_num [piLower]
  have hl' := (le_div_iff₀ hp).mp hl
  have hu' := (div_lt_iff₀ hp).mp hu
  have hpi : (piLower : ℝ) < 4 := by norm_num [piLower]
  push_cast [dottieNormAngleQuarterOf]
  apply abs_le.mpr
  constructor <;> nlinarith only [hl',hu',hpi]

theorem dottieNormAngleQuarter_abs_le (n : ℕ) : |(dottieNormAngleQuarter n : ℝ)| ≤ 1 :=
  dottieNormAngleQuarterOf_abs_le (normLogBounds (2^96) 31 n).1

/-- Absolute error from using the rational angle and reducing by approximate
periods. The angle is subtracted from the exact phase after matching its
integer number of true periods. -/
theorem dottie_norm_angle_reduction_of (n ticks : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064)
    (hlog₀ : 0 ≤ Real.log n - (ticks : ℝ)/2^96)
    (hlog₁ : Real.log n - (ticks : ℝ)/2^96 ≤ (120:ℝ)/2^96) :
    |3.9229252 - 4526119322477.943440197603 * Real.log n -
      (dottieNormPeriodCountOf ticks : ℝ)*(2*Real.pi) -
        4*(dottieNormAngleQuarterOf ticks : ℝ)| ≤ 1/2000000 := by
  let l : ℝ := (ticks : ℝ)/2^96
  let u : ℝ := (normAngleOf ticks : ℝ)
  let k : ℝ := (dottieNormPeriodCountOf ticks : ℝ)
  change 0 ≤ Real.log n-l at hlog₀
  change Real.log n-l ≤ (120:ℝ)/2^96 at hlog₁
  have hu : u = 3.9229252 - 4526119322477.943440197603 * l := by
    dsimp only [u, normAngleOf, l, referenceHeightRat, referenceAngleRat]
    push_cast
    norm_num1
    ring
  have hl₀ : 0 ≤ l := by positivity
  have hl₁ : l ≤ 20 := by linarith only [hlog₀, log_lt_twenty n hn hcap]
  obtain ⟨hk₀,hk₁⟩ := periodCountOf_bounds ticks
  have hp₀ : (0:ℝ) < 2*(piLower : ℝ) := by norm_num [piLower]
  have hk₀' := (le_div_iff₀ hp₀).mp hk₀
  have hk₁' := (div_lt_iff₀ hp₀).mp hk₁
  norm_num [piLower] at hk₀' hk₁'
  have hk : |k| ≤ 2*10^13 := by
    apply abs_le.mpr
    constructor <;> linarith only [hu, hk₀', hk₁', hl₀,hl₁]
  have hperiod : |(piLower : ℝ)-Real.pi| ≤ 1/10^20 := by
    apply abs_le.mpr
    norm_num [piLower]
    constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
  have hx : |l-Real.log n| ≤ (120:ℝ)/2^96 := by
    apply abs_le.mpr
    constructor <;> linarith only [hlog₀,hlog₁]
  have ht : |4526119322477.943440197603*(l-Real.log n)| ≤ (1:ℝ)/10^13 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4526119322477.943440197603)]
    exact (mul_le_mul_of_nonneg_left hx (by norm_num)).trans (by norm_num)
  have hperiod' : |2*k*((piLower : ℝ)-Real.pi)| ≤ (4:ℝ)/10^7 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hperiod
      (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have e : (4:ℝ)*(dottieNormAngleQuarterOf ticks : ℝ) = u-k*(2*(piLower : ℝ)) := by
    push_cast [dottieNormAngleQuarterOf]
    dsimp only [u,k]
    ring
  rw [e, hu]
  change |3.9229252 - 4526119322477.943440197603 * Real.log n - k*(2*Real.pi) -
    (3.9229252 - 4526119322477.943440197603*l-k*(2*(piLower : ℝ)))| ≤ _
  rw [show 3.9229252 - 4526119322477.943440197603 * Real.log n - k*(2*Real.pi) -
    (3.9229252 - 4526119322477.943440197603*l-k*(2*(piLower : ℝ))) =
    4526119322477.943440197603*(l-Real.log n)+2*k*((piLower : ℝ)-Real.pi) by ring]
  exact (abs_add_le _ _).trans ((add_le_add ht hperiod').trans (by norm_num))

/-- The same bound after applying cosine, which removes the integer period. -/
theorem dottie_norm_angle_cosine_error_of (n ticks : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064)
    (hlog₀ : 0 ≤ Real.log n - (ticks : ℝ)/2^96)
    (hlog₁ : Real.log n - (ticks : ℝ)/2^96 ≤ (120:ℝ)/2^96) :
    |Real.cos (4*(dottieNormAngleQuarterOf ticks : ℝ)) -
      Real.cos (3.9229252 - 4526119322477.943440197603 * Real.log n)| ≤ 1/2000000 := by
  let θ : ℝ := 3.9229252 - 4526119322477.943440197603 * Real.log n
  let p : ℝ := (dottieNormPeriodCountOf ticks : ℝ)*(2*Real.pi)
  change |Real.cos (4*(dottieNormAngleQuarterOf ticks : ℝ)) - Real.cos θ| ≤ _
  have hcos : Real.cos (θ-p) = Real.cos θ := by
    have h := Real.cos_add_int_mul_two_pi (θ-p) (dottieNormPeriodCountOf ticks)
    change Real.cos (θ-p+p) = Real.cos (θ-p) at h
    rwa [sub_add_cancel, eq_comm] at h
  rw [← hcos, abs_sub_comm]
  exact (Real.abs_cos_sub_cos_le _ _).trans (dottie_norm_angle_reduction_of n ticks hn hcap hlog₀ hlog₁)

/-- The reduction bound for the original log evaluation. -/
theorem dottie_norm_angle_reduction (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    |3.9229252 - 4526119322477.943440197603 * Real.log n -
      (periodCount n : ℝ)*(2*Real.pi) - 4*(dottieNormAngleQuarter n : ℝ)| ≤ 1/2000000 :=
  let hlog := lower_log_accurate n hn hcap
  dottie_norm_angle_reduction_of n (normLogBounds (2^96) 31 n).1 hn hcap hlog.1 hlog.2

#print axioms dottieNormAngleQuarterOf_abs_le
#print axioms dottieNormAngleQuarter_abs_le
#print axioms dottie_norm_angle_reduction_of
#print axioms dottie_norm_angle_cosine_error_of
#print axioms dottie_norm_angle_reduction

end QuarticModel
