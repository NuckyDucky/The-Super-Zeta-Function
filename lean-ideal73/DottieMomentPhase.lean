import DottieQuickLog
import DottiePreciseMomentHeight

/-! Rational phase reduction for the sharp signed moments. The 96-bit
logarithm and the 32-decimal pi bracket are used at the original height. -/

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open private dottie_pi_lower dottie_pi_upper from DottiePreciseHeight
open private log_lt_twenty_two from DottiePreciseMomentHeight
set_option autoImplicit false

def dottieMomentHeightRat : ℚ := 4526119322477.94539331920732885695
def dottieMomentPiRat : ℚ := 3.14159265358979323846264338327950

def dottieMomentAngle (n : ℕ) : ℚ :=
  -dottieMomentHeightRat*((dottieQuickLogLowerTicks n:ℚ)/2^96)

def dottieMomentAngleTurn (n : ℕ) : ℤ :=
  ⌊(dottieMomentAngle n+dottieMomentPiRat)/(2*dottieMomentPiRat)⌋

def dottieMomentReducedAngle (n : ℕ) : ℚ :=
  dottieMomentAngle n-2*dottieMomentPiRat*(dottieMomentAngleTurn n:ℚ)

theorem dottie_moment_reduced_angle_bounds (n : ℕ) :
    -dottieMomentPiRat ≤ dottieMomentReducedAngle n ∧ dottieMomentReducedAngle n < dottieMomentPiRat := by
  let θ := dottieMomentAngle n
  let π₀ := dottieMomentPiRat
  let q := dottieMomentAngleTurn n
  have hq₀ : (q:ℚ) ≤ (θ+π₀)/(2*π₀) := Int.floor_le _
  have hq₁ : (θ+π₀)/(2*π₀) < (q:ℚ)+1 := Int.lt_floor_add_one _
  have hp : 0 < 2*π₀ := by norm_num [π₀,dottieMomentPiRat]
  have hl := (le_div_iff₀ hp).1 hq₀
  have hu := (div_lt_iff₀ hp).1 hq₁
  change -π₀ ≤ θ-2*π₀*(q:ℚ) ∧ θ-2*π₀*(q:ℚ) < π₀
  constructor <;> nlinarith only [hl,hu]

theorem dottie_moment_rational_phase_error (n : ℕ) (hn : 0 < n) (hN : n ≤ dottiePrefixEnd) :
    ‖exp (((-(dottieMomentRationalHeight*Real.log n):ℝ):ℂ)*I)-
      exp (((dottieMomentReducedAngle n:ℝ):ℂ)*I)‖ ≤ 1/10^13 := by
  let T := dottieMomentRationalHeight
  let L := (dottieQuickLogLowerTicks n:ℝ)/2^96
  let q := dottieMomentAngleTurn n
  let θ : ℝ := dottieMomentReducedAngle n
  let π₀ : ℝ := dottieMomentPiRat
  have hT : 0 ≤ T ∧ T ≤ 5*10^12 := by norm_num [T,dottieMomentRationalHeight]
  have eAngle : (dottieMomentAngle n:ℝ) = -T*L := by
    unfold dottieMomentAngle dottieMomentHeightRat T L dottieMomentRationalHeight
    push_cast
    norm_num
  have eθ : θ = -T*L-2*π₀*(q:ℝ) := by
    unfold θ dottieMomentReducedAngle
    push_cast
    rw [eAngle]
  have hlog := dottieQuickLogLowerTicks_sharp_spec n hn (by simpa only [dottiePrefixEnd] using hN)
  have hS : (0:ℝ) < 2^96 := by positivity
  have hL : 0 ≤ L ∧ L ≤ Real.log n := ⟨by positivity,(div_le_iff₀ hS).2 (by linarith only [hlog.1])⟩
  have hlogErr : 0 ≤ Real.log n-L ∧ Real.log n-L ≤ 128/(2:ℝ)^96 := by
    constructor
    · linarith only [hL.2]
    · dsimp only [L]
      rw [sub_le_iff_le_add,← add_div]
      exact (le_div_iff₀ hS).2 (by linarith only [hlog.2])
  have hπ : 3 ≤ π₀ ∧ π₀ ≤ 4 := by norm_num [π₀,dottieMomentPiRat]
  have hπerr : |π₀-Real.pi| ≤ 1/10^32 := by
    have hp₁ := dottie_pi_lower
    have hp₂ := dottie_pi_upper
    dsimp [π₀,dottieMomentPiRat]
    push_cast
    exact abs_le.mpr ⟨by linarith only [hp₂],by linarith only [hp₁]⟩
  have hθ : |θ| ≤ 4 := by
    obtain ⟨hlo,hhi⟩ := dottie_moment_reduced_angle_bounds n
    have hl : -π₀ ≤ θ := by
      change -(dottieMomentPiRat:ℝ) ≤ (dottieMomentReducedAngle n:ℝ)
      exact_mod_cast hlo
    have hu : θ ≤ π₀ := by
      change (dottieMomentReducedAngle n:ℝ) ≤ (dottieMomentPiRat:ℝ)
      exact_mod_cast hhi.le
    exact abs_le.mpr ⟨by linarith only [hl,hπ.2],hu.trans hπ.2⟩
  have hTL : |-T*L| ≤ 11*10^13 := by
    rw [abs_mul,abs_neg,abs_of_nonneg hT.1,abs_of_nonneg hL.1]
    exact (mul_le_mul hT.2 (hL.2.trans (log_lt_twenty_two hn hN).le) hL.1 (by norm_num)).trans (by norm_num)
  have hq : |(q:ℝ)| ≤ 2*10^13 := by
    have hp : |2*π₀*(q:ℝ)| ≤ 11*10^13+4 := by
      rw [show 2*π₀*(q:ℝ) = -T*L-θ by rw [eθ]; ring]
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (add_le_add hTL (by simpa only [abs_neg] using hθ))
    rw [abs_mul,abs_of_nonneg (by linarith only [hπ.1] : 0 ≤ 2*π₀)] at hp
    nlinarith only [hp,mul_le_mul_of_nonneg_right hπ.1 (abs_nonneg (q:ℝ))]
  have hperiod : exp ((((θ+2*Real.pi*(q:ℝ)):ℝ):ℂ)*I) = exp ((θ:ℂ)*I) := by
    rw [show (((θ+2*Real.pi*(q:ℝ):ℝ):ℂ)*I) = (θ:ℂ)*I+(q:ℂ)*(2*(Real.pi:ℂ)*I) by push_cast; ring,
      Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
  change ‖exp (((-(T*Real.log n):ℝ):ℂ)*I)-exp ((θ:ℂ)*I)‖ ≤ _
  rw [← hperiod]
  refine (dottie_unit_phase_distance _ _).trans ?_
  rw [show -(T*Real.log n)-(θ+2*Real.pi*(q:ℝ)) =
      -(T*(Real.log n-L))+2*(q:ℝ)*(π₀-Real.pi) by rw [eθ]; ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg,abs_mul,abs_of_nonneg hT.1,abs_of_nonneg hlogErr.1,
    abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h₁ := mul_le_mul hT.2 hlogErr.2 hlogErr.1 (by norm_num)
  have h₂ := mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 2))
    hπerr (abs_nonneg _) (by norm_num)
  norm_num at h₁ h₂ ⊢
  linarith only [h₁,h₂]

#print axioms dottie_moment_reduced_angle_bounds
#print axioms dottie_moment_rational_phase_error

end QuarticModel
