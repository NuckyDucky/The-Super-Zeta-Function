import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The cosine determinant and its integer traces

This module proves the cosine determinant expansion in §4 of the cosine-spectrum
manuscript at every squared complex argument. It then constructs the
formal logarithmic derivative over the rationals, proves its
Newton convolution in every degree, and evaluates the first four traces.
The analytic identification with the spectral sum is equation (16) of the
manuscript. The zero-transport theorem below takes equation (21) as an
explicit hypothesis.
-/

namespace SuperZeta.Spectrum

noncomputable section

/-- Coefficients of the determinant, with `q = ε⁻²`. -/
def determinantCoeff (q : ℚ) (n : ℕ) : ℚ :=
  (if n = 0 then 1 / 2 else 0) +
    (-1) ^ n * 2 ^ (2 * n) / (Nat.factorial (2 * n) : ℚ) / 2 -
    (if n = 1 then q else 0)

/-- The coefficient series equals the actual complex cosine determinant at `λ = u²`. -/
theorem determinant_hasSum (q : ℚ) (u : ℂ) :
    HasSum (fun n => (determinantCoeff q n : ℂ) * (u ^ 2) ^ n)
      (Complex.cos u ^ 2 - (q : ℂ) * u ^ 2) := by
  have hs := ((hasSum_ite_eq (0 : ℕ) (1/2 : ℂ)).add
    ((Complex.hasSum_cos (2 * u)).div_const 2)).sub
      (hasSum_ite_eq (1 : ℕ) ((q : ℂ) * u ^ 2))
  have hv : 1/2 + Complex.cos (2*u)/2 - (q : ℂ)*u^2 =
      Complex.cos u^2 - (q : ℂ)*u^2 := by rw [Complex.cos_two_mul]; ring
  rw [hv] at hs
  apply hs.congr_fun
  intro n
  by_cases h₀ : n = 0
  · subst n
    norm_num [determinantCoeff, Nat.factorial]
  by_cases h₁ : n = 1
  · subst n
    norm_num [determinantCoeff, Nat.factorial]
    ring
  simp [determinantCoeff, h₀, h₁, mul_pow, pow_mul]
  ring

def determinant (q : ℚ) : PowerSeries ℚ := PowerSeries.mk (determinantCoeff q)

/-- The coefficient of degree `n` in `−E'/E` gives the trace of index `n+1`. -/
def traceSeries (q : ℚ) : PowerSeries ℚ :=
  (determinant q)⁻¹ * (-PowerSeries.derivative ℚ (determinant q))

def traceCoeff (q : ℚ) (n : ℕ) : ℚ := PowerSeries.coeff n (traceSeries q)

theorem determinant_mul_traceSeries (q : ℚ) :
    determinant q * traceSeries q = -PowerSeries.derivative ℚ (determinant q) := by
  have h : PowerSeries.constantCoeff (determinant q) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, determinant, PowerSeries.coeff_mk]
    norm_num [determinantCoeff, Nat.factorial]
  rw [traceSeries, ← mul_assoc, PowerSeries.mul_inv_cancel _ h, one_mul]

/-- The convolution from `E · (−E'/E) = −E'`, at every coefficient. -/
theorem newton_convolution (q : ℚ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), determinantCoeff q k * traceCoeff q (n - k)) =
      -(determinantCoeff q (n + 1) * ((n : ℚ) + 1)) := by
  have h := congrArg (PowerSeries.coeff n) (determinant_mul_traceSeries q)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    map_neg, PowerSeries.coeff_derivative] at h
  simpa only [determinant, PowerSeries.coeff_mk, traceCoeff] using h

/-- Equation (17), computed from the formal determinant. -/
theorem first_four_unit_coupling_traces :
    traceCoeff 1 0 = 2 ∧ traceCoeff 1 1 = 10/3 ∧
    traceCoeff 1 2 = 92/15 ∧ traceCoeff 1 3 = 3538/315 := by
  have h₀ := newton_convolution 1 0
  have h₁ := newton_convolution 1 1
  have h₂ := newton_convolution 1 2
  have h₃ := newton_convolution 1 3
  norm_num [Finset.sum_range_succ, determinantCoeff, Nat.factorial] at h₀ h₁ h₂ h₃
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A single quartet root's modulus contribution at positive or negative height,
with the principal argument and complex power. -/
theorem quartet_mode_norm {u : ℂ} (hu : u ≠ 0) (s : ℂ) :
    ‖u ^ (-(2 * s))‖ = ‖u‖ ^ (-(2 * s.re)) * Real.exp (2 * s.im * u.arg) := by
  rw [Complex.norm_cpow_of_ne_zero hu]
  have hre : (-(2 * s)).re = -(2 * s.re) := by simp [two_mul]
  have him : u.arg * (-(2 * s)).im = -(2 * s.im * u.arg) := by
    simp [two_mul]
    ring
  rw [hre, him, Real.exp_neg, div_inv_eq_mul]

/-- The factor in the reconstruction formula, with complex powers on the principal branch. -/
def riemannFactor (s : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) ^ (-(2 * s)) * ((2 : ℂ) ^ (2 * s) - 1)

/-- It cannot introduce an additional zero to the right of the imaginary axis. -/
theorem riemannFactor_ne_zero {s : ℂ} (hs : 0 < s.re) : riemannFactor s ≠ 0 := by
  have hre : 0 < (2 * s).re := by
    simpa [two_mul] using (add_pos hs hs)
  have hnorm : 1 < ‖(2 : ℂ) ^ (2 * s)‖ := by
    calc
      1 < (2 : ℝ) ^ (2 * s).re := Real.one_lt_rpow (by norm_num) hre
      _ = ‖(2 : ℂ) ^ (2 * s)‖ := by
        simpa using (Complex.norm_cpow_eq_rpow_re_of_pos
          (by norm_num : 0 < (2 : ℝ)) (2 * s)).symm
  have htwo : (2 : ℂ) ^ (2 * s) ≠ 1 := by
    intro h
    rw [h, norm_one] at hnorm
    exact (lt_irrefl _ hnorm)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))) (sub_ne_zero.mpr htwo)

/-- Under the manuscript's analytic identity at `s`, the two complex values
agree exactly when the doubled input is a zero of mathlib's Riemann zeta. -/
theorem equality_iff_riemann_zero
    {s full correction : ℂ} (hs : 0 < s.re)
    (reconstruction : full - correction = riemannFactor s * riemannZeta (2 * s)) :
    full = correction ↔ riemannZeta (2 * s) = 0 := by
  rw [← sub_eq_zero, reconstruction, mul_eq_zero]
  simp [riemannFactor_ne_zero hs]

end

end SuperZeta.Spectrum
