import SuperZeta.CoupledDeterminant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.LinearCombination

/-!
# First trace of the signed determinant and two oriented probes

The scalar characteristic is `z − σ cos(z − φ)` for `σ = ±1`. Its symmetric
product at `z` and `−z` gives an entire determinant in `v = z²`. For a native
angle `θ` the positive stage uses `φ = −θ`.
-/

namespace DottieOriented.TraceRecovery

noncomputable section

def signedCharacteristic (σ φ : ℝ) (z : ℂ) : ℂ :=
  z - (σ : ℂ) * Complex.cos (z - (φ : ℂ))

/-- Coefficients of `z sin z` in `v = z²`. -/
private def sineCoeff : ℕ → ℂ
  | 0 => 0
  | n + 1 => (-1) ^ n / (Nat.factorial (2 * n + 1) : ℂ)

private theorem sineCoeff_hasSum (z : ℂ) :
    HasSum (fun n => sineCoeff n * (z ^ 2) ^ n) (z * Complex.sin z) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [Finset.sum_range_one, sineCoeff, pow_zero, zero_mul, sub_zero]
  convert (Complex.hasSum_sin z).mul_left z using 1
  funext n
  rw [← pow_mul, show 2 * (n + 1) = 2 * n + 1 + 1 by omega, pow_succ]
  ring

private def signedCoeff (σ φ : ℝ) (n : ℕ) : ℂ :=
  ((SuperZeta.Spectrum.determinantCoeff 1 n : ℂ) -
    (if n = 0 then (Real.sin φ : ℂ) ^ 2 else 0) +
    2 * (σ : ℂ) * (Real.sin φ : ℂ) * sineCoeff n) / (Real.cos φ : ℂ) ^ 2

private def signedSeries (σ φ : ℝ) :=
  FormalMultilinearSeries.ofScalars ℂ (signedCoeff σ φ)

/-- The determinant in the squared spectral variable. Its normalization is valid
when `cos φ ≠ 0`. -/
def signedDet (σ φ : ℝ) : ℂ → ℂ :=
  (signedSeries σ φ).sum

private theorem signedCoeff_hasSum (σ φ : ℝ) (z : ℂ) :
    HasSum (fun n => signedCoeff σ φ n * (z ^ 2) ^ n)
      ((Complex.cos z ^ 2 - z ^ 2 - (Real.sin φ : ℂ) ^ 2 +
        2 * (σ : ℂ) * (Real.sin φ : ℂ) * (z * Complex.sin z)) /
        (Real.cos φ : ℂ) ^ 2) := by
  convert (((SuperZeta.Spectrum.determinant_hasSum 1 z).sub
    (hasSum_ite_eq (0 : ℕ) ((Real.sin φ : ℂ) ^ 2))).add
    ((sineCoeff_hasSum z).mul_left (2 * (σ : ℂ) * (Real.sin φ : ℂ)))).div_const
    ((Real.cos φ : ℂ) ^ 2) using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [signedCoeff, sineCoeff]
    · simp [signedCoeff, hn, div_mul_eq_mul_div, add_mul, sub_mul, mul_assoc]
  · norm_num

/-- The expanded determinant at the square of a characteristic parameter. -/
theorem signedDet_sq_expanded (σ φ : ℝ) (z : ℂ) :
    signedDet σ φ (z ^ 2) =
      (Complex.cos z ^ 2 - z ^ 2 - (Real.sin φ : ℂ) ^ 2 +
        2 * (σ : ℂ) * (Real.sin φ : ℂ) * (z * Complex.sin z)) /
        (Real.cos φ : ℂ) ^ 2 := by
  change FormalMultilinearSeries.ofScalarsSum (signedCoeff σ φ) (z ^ 2) = _
  simpa only [FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul] using
    (signedCoeff_hasSum σ φ z).tsum_eq

/-- For each oriented stage the two antipodes give the squared determinant. -/
theorem signedDet_sq {σ : ℝ} (hσ : σ ^ 2 = 1) (φ : ℝ) (z : ℂ) :
    signedDet σ φ (z ^ 2) =
      signedCharacteristic σ φ z * signedCharacteristic σ φ (-z) /
        (Real.cos φ : ℂ) ^ 2 := by
  rw [signedDet_sq_expanded]
  congr 1
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have hz := Complex.cos_sq_add_sin_sq z
  have hφ : (Real.cos φ : ℂ) ^ 2 + (Real.sin φ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq φ
  simp only [signedCharacteristic, Complex.cos_sub, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  symm
  calc
    _ = (σ : ℂ) ^ 2 * (Complex.cos z ^ 2 * (Real.cos φ : ℂ) ^ 2 -
        Complex.sin z ^ 2 * (Real.sin φ : ℂ) ^ 2) - z ^ 2 +
        2 * (σ : ℂ) * (Real.sin φ : ℂ) * (z * Complex.sin z) := by ring
    _ = _ := by
      rw [hσC, one_mul]
      linear_combination Complex.cos z ^ 2 * hφ - (Real.sin φ : ℂ) ^ 2 * hz

theorem signedDet_zero_iff {σ φ : ℝ} (hσ : σ ^ 2 = 1) (hφ : Real.cos φ ≠ 0)
    (z : ℂ) : signedDet σ φ (z ^ 2) = 0 ↔
      signedCharacteristic σ φ z = 0 ∨ signedCharacteristic σ φ (-z) = 0 := by
  rw [signedDet_sq hσ]
  have hc : Complex.cos (φ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]
    exact_mod_cast hφ
  simp [hc, mul_eq_zero]

private theorem signedSeries_radius (σ φ : ℝ) : (signedSeries σ φ).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  let z : ℂ := (Real.sqrt r : ℝ)
  have hz : z ^ 2 = ((r : ℝ) : ℂ) := by
    change (↑(Real.sqrt r) : ℂ) ^ 2 = _
    rw [← Complex.ofReal_pow, Real.sq_sqrt r.coe_nonneg]
  have hs := (signedCoeff_hasSum σ φ z).summable.norm
  simp only [hz, norm_mul, norm_pow, Complex.norm_of_nonneg r.coe_nonneg] at hs
  simpa only [signedSeries, FormalMultilinearSeries.ofScalars_norm] using hs

theorem signedDet_analytic (σ φ : ℝ) (v : ℂ) : AnalyticAt ℂ (signedDet σ φ) v := by
  have hr := signedSeries_radius σ φ
  exact ((signedSeries σ φ).hasFPowerSeriesOnBall (by simp [hr])).analyticAt_of_mem
    (by simp [hr])

theorem signedDet_at_zero {σ φ : ℝ} (hφ : Real.cos φ ≠ 0) : signedDet σ φ 0 = 1 := by
  have h := signedDet_sq_expanded σ φ 0
  have hc : Complex.cos (φ : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]
    exact_mod_cast hφ
  have htrig := Complex.cos_sq_add_sin_sq (φ : ℂ)
  simp at h
  rw [h, ← eq_sub_iff_add_eq.mpr htrig, div_self (pow_ne_zero _ hc)]

theorem signedDet_hasDerivAt_zero (σ φ : ℝ) :
    HasDerivAt (signedDet σ φ)
      (((-2 + 2 * σ * Real.sin φ) / Real.cos φ ^ 2 : ℝ) : ℂ) 0 := by
  have hr := signedSeries_radius σ φ
  have h := ((signedSeries σ φ).hasFPowerSeriesOnBall (by simp [hr])).hasFPowerSeriesAt
  have hderiv := h.hasDerivAt
  change HasDerivAt (signedDet σ φ) ((signedSeries σ φ) 1 (fun _ => 1)) 0 at hderiv
  convert hderiv using 1
  rw [signedSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  norm_num [signedCoeff, sineCoeff, SuperZeta.Spectrum.determinantCoeff, Nat.factorial]

/-- The first trace coefficient of `−E'/E` at `E(0) = 1`. -/
def firstTrace (σ φ : ℝ) : ℝ := -(deriv (signedDet σ φ) 0).re

private theorem traceDenominators {σ φ : ℝ} (hσ : σ ^ 2 = 1) (hφ : Real.cos φ ≠ 0) :
    (1 + σ * Real.sin φ) * (1 - σ * Real.sin φ) = Real.cos φ ^ 2 ∧
    1 + σ * Real.sin φ ≠ 0 ∧ 1 - σ * Real.sin φ ≠ 0 := by
  have hmul : (1 + σ * Real.sin φ) * (1 - σ * Real.sin φ) = Real.cos φ ^ 2 := by
    calc
      _ = 1 - σ ^ 2 * Real.sin φ ^ 2 := by ring
      _ = _ := by rw [hσ, one_mul, ← Real.cos_sq_add_sin_sq φ]; ring
  exact ⟨hmul, left_ne_zero_of_mul (hmul.trans_ne (pow_ne_zero _ hφ)),
    right_ne_zero_of_mul (hmul.trans_ne (pow_ne_zero _ hφ))⟩

theorem firstTrace_eq {σ φ : ℝ} (hσ : σ ^ 2 = 1) (hφ : Real.cos φ ≠ 0) :
    firstTrace σ φ = 2 / (1 + σ * Real.sin φ) := by
  obtain ⟨hmul, hp, hm⟩ := traceDenominators hσ hφ
  rw [firstTrace, (signedDet_hasDerivAt_zero σ φ).deriv, Complex.ofReal_re, ← hmul]
  field_simp [hp, hm]
  ring

/-- Move from the native angle to the spectral phase for the positive stage. -/
def nativeTrace (θ : ℝ) : ℝ := firstTrace 1 (-θ)

theorem nativeTrace_eq {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    nativeTrace θ = 2 / (1 - Real.sin θ) := by
  have hc : Real.cos (-θ) ≠ 0 := by simpa using hθ
  simpa [nativeTrace, sub_eq_add_neg] using
    (firstTrace_eq (σ := 1) (by norm_num) hc)

/-- Probe order is the positive turn followed by the negative turn. -/
def traceProbes (δ θ : ℝ) : ℝ × ℝ :=
  (nativeTrace (θ + δ), nativeTrace (θ - δ))

/-- Convert a single trace coefficient to the sine of its probe angle. -/
def sineReading (m : ℝ) : ℝ := 1 - 2 / m

theorem sineReading_native {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    sineReading (nativeTrace θ) = Real.sin θ := by
  have hd : 1 - Real.sin θ ≠ 0 := by
    intro hs
    have hsin : Real.sin θ = 1 := by linarith
    have hsq := Real.sin_sq_add_cos_sq θ
    rw [hsin, one_pow] at hsq
    have hz : Real.cos θ ^ 2 = 0 := by linarith
    exact pow_ne_zero 2 hθ hz
  rw [sineReading, nativeTrace_eq hθ]
  field_simp [hd]

/-- The decoder returns `cos θ` and `sin θ` in that order. -/
def recover (δ : ℝ) (m : ℝ × ℝ) : ℝ × ℝ :=
  ((sineReading m.1 - sineReading m.2) / (2 * Real.sin δ),
    (sineReading m.1 + sineReading m.2) / (2 * Real.cos δ))

theorem recover_probes {δ θ : ℝ} (hs : Real.sin δ ≠ 0) (hc : Real.cos δ ≠ 0)
    (hp : Real.cos (θ + δ) ≠ 0) (hm : Real.cos (θ - δ) ≠ 0) :
    recover δ (traceProbes δ θ) = (Real.cos θ, Real.sin θ) := by
  dsimp [recover, traceProbes]
  rw [sineReading_native hp, sineReading_native hm, Real.sin_add, Real.sin_sub]
  congr 1 <;> field_simp [hs, hc] <;> ring

private theorem sin_reflect (θ : ℝ) : Real.sin (-Real.pi - θ) = Real.sin θ := by
  rw [show -Real.pi - θ = -(θ + Real.pi) by ring, Real.sin_neg, Real.sin_add_pi, neg_neg]

private theorem cos_reflect (θ : ℝ) : Real.cos (-Real.pi - θ) = -Real.cos θ := by
  rw [show -Real.pi - θ = -(θ + Real.pi) by ring, Real.cos_neg, Real.cos_add_pi]

theorem nativeTrace_reflect {θ : ℝ} (hθ : Real.cos θ ≠ 0) :
    nativeTrace (-Real.pi - θ) = nativeTrace θ := by
  have hc : Real.cos (-Real.pi - θ) ≠ 0 := by simpa [cos_reflect] using hθ
  rw [nativeTrace_eq hc, nativeTrace_eq hθ, sin_reflect]

/-- Reflection about `−π/2` exchanges the two labeled readings. -/
theorem traceProbes_reflect {δ θ : ℝ} (hp : Real.cos (θ + δ) ≠ 0)
    (hm : Real.cos (θ - δ) ≠ 0) :
    traceProbes δ (-Real.pi - θ) = (traceProbes δ θ).swap := by
  change (nativeTrace ((-Real.pi - θ) + δ), nativeTrace ((-Real.pi - θ) - δ)) =
    (nativeTrace (θ - δ), nativeTrace (θ + δ))
  rw [show (-Real.pi - θ) + δ = -Real.pi - (θ - δ) by ring,
    show (-Real.pi - θ) - δ = -Real.pi - (θ + δ) by ring,
    nativeTrace_reflect hm, nativeTrace_reflect hp]

theorem traceProbes_tie_iff {δ θ : ℝ} (hs : Real.sin δ ≠ 0)
    (hp : Real.cos (θ + δ) ≠ 0) (hm : Real.cos (θ - δ) ≠ 0) :
    (traceProbes δ θ).1 = (traceProbes δ θ).2 ↔ Real.cos θ = 0 := by
  change nativeTrace (θ + δ) = nativeTrace (θ - δ) ↔ Real.cos θ = 0
  constructor
  · intro h
    have hsin := congrArg sineReading h
    rw [sineReading_native hp, sineReading_native hm, Real.sin_add, Real.sin_sub] at hsin
    exact (mul_eq_zero.mp (show Real.cos θ * Real.sin δ = 0 by linarith)).resolve_right hs
  · intro h
    rw [nativeTrace_eq hp, nativeTrace_eq hm, Real.sin_add, Real.sin_sub, h, zero_mul,
      add_zero, sub_zero]

/-- The full central interval between the two singular probe angles. -/
theorem probeGuards_pi_div_six {θ : ℝ} (hlo : -2 * Real.pi / 3 < θ)
    (hhi : θ < -Real.pi / 3) :
    Real.cos (θ + Real.pi / 6) ≠ 0 ∧ Real.cos (θ - Real.pi / 6) ≠ 0 := by
  have hπ := Real.pi_pos
  constructor
  · exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).ne'
  · rw [← Real.cos_neg]
    exact (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)).ne

private theorem sin_pi_div_six_ne : Real.sin (Real.pi / 6) ≠ 0 := by
  norm_num [Real.sin_pi_div_six]

private theorem cos_pi_div_six_ne : Real.cos (Real.pi / 6) ≠ 0 := by
  rw [Real.cos_pi_div_six]
  positivity

/-- The `±30°` decoder only needs the two first trace coefficients. -/
theorem recover_pi_div_six {θ : ℝ} (hp : Real.cos (θ + Real.pi / 6) ≠ 0)
    (hm : Real.cos (θ - Real.pi / 6) ≠ 0) :
    let m := traceProbes (Real.pi / 6) θ
    (sineReading m.1 - sineReading m.2, (sineReading m.1 + sineReading m.2) / Real.sqrt 3) =
      (Real.cos θ, Real.sin θ) := by
  have h := recover_probes sin_pi_div_six_ne cos_pi_div_six_ne hp hm
  have hs : 2 * Real.sin (Real.pi / 6) = 1 := by norm_num [Real.sin_pi_div_six]
  have hc : 2 * Real.cos (Real.pi / 6) = Real.sqrt 3 := by rw [Real.cos_pi_div_six]; ring
  simpa only [recover, hs, hc, div_one] using h

theorem traceProbes_pi_div_six_tie_iff {θ : ℝ} (hlo : -2 * Real.pi / 3 < θ)
    (hhi : θ < -Real.pi / 3) :
    (traceProbes (Real.pi / 6) θ).1 = (traceProbes (Real.pi / 6) θ).2 ↔
      θ = -(Real.pi / 2) := by
  obtain ⟨hp, hm⟩ := probeGuards_pi_div_six hlo hhi
  rw [traceProbes_tie_iff sin_pi_div_six_ne hp hm, ← Real.sin_add_pi_div_two,
    Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  constructor <;> intro h <;> linarith

theorem traceProbes_pi_div_six_at_pivot :
    traceProbes (Real.pi / 6) (-(Real.pi / 2)) =
      (8 - 4 * Real.sqrt 3, 8 - 4 * Real.sqrt 3) := by
  have hπ := Real.pi_pos
  obtain ⟨hp, hm⟩ := probeGuards_pi_div_six (θ := -(Real.pi / 2)) (by linarith) (by linarith)
  change (nativeTrace (-(Real.pi / 2) + Real.pi / 6),
    nativeTrace (-(Real.pi / 2) - Real.pi / 6)) = _
  rw [nativeTrace_eq hp, nativeTrace_eq hm,
    show -(Real.pi / 2) + Real.pi / 6 = Real.pi / 6 - Real.pi / 2 by ring,
    show -(Real.pi / 2) - Real.pi / 6 = -(Real.pi / 6) - Real.pi / 2 by ring,
    Real.sin_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.cos_neg, Real.cos_pi_div_six]
  have hroot : 2 / (1 - -(Real.sqrt 3 / 2)) = 8 - 4 * Real.sqrt 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hd : (1 - -(Real.sqrt 3 / 2)) ≠ 0 :=
      (show (0 : ℝ) < 1 - -(Real.sqrt 3 / 2) by linarith [Real.sqrt_nonneg 3]).ne'
    apply (div_eq_iff hd).mpr
    linear_combination 2 * hs
  rw [hroot]

end

end DottieOriented.TraceRecovery
