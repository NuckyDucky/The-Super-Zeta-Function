import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The positive lower integrand used to bound each zero in the Dottie height band. -/

namespace SuperZeta.GaussianDiskKernel

open Real Set MeasureTheory

noncomputable def taper (y : ℝ) : ℝ :=
  (1 - y) * cos (π * y) + sin (π * y) / π

theorem taper_derivative (y : ℝ) :
    HasDerivAt taper (-π * (1-y) * sin (π*y)) y := by
  have h := (hasDerivAt_id y).const_mul π
  change HasDerivAt (fun x : ℝ => π * x) (π * 1) y at h
  have h' := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).mul h.cos).add
    (h.sin.div_const π)
  convert h' using 1
  dsimp
  field_simp [Real.pi_ne_zero]
  ring

theorem taper_antitone : AntitoneOn taper (Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact (fun x _ => (taper_derivative x).continuousAt.continuousWithinAt)
  · exact fun x _ => (taper_derivative x).differentiableAt.differentiableWithinAt
  · intro x hx
    obtain ⟨hx₀, hx₁⟩ := interior_subset hx
    rw [(taper_derivative x).deriv]
    have hs := sin_nonneg_of_nonneg_of_le_pi (mul_nonneg pi_pos.le hx₀)
      (show π * x ≤ π by simpa using mul_le_mul_of_nonneg_left hx₁ pi_pos.le)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [pi_pos]) (sub_nonneg.mpr hx₁)) hs

theorem taper_nonneg {y : ℝ} (hy : y ∈ Icc 0 1) : 0 ≤ taper y := by
  simpa [taper] using taper_antitone hy (right_mem_Icc.mpr zero_le_one) hy.2

noncomputable def weight (A u : ℝ) : ℝ := taper (u / A) / cosh (u / 2)

noncomputable def lowerIntegrand (A r u : ℝ) : ℝ := weight A u * cos (r*u)

private theorem weight_nonneg {A u : ℝ} (hA : 0 < A) (hu : u ∈ Icc 0 A) :
    0 ≤ weight A u := by
  apply div_nonneg _ (cosh_pos _).le
  exact taper_nonneg ⟨div_nonneg hu.1 hA.le, (div_le_one hA).mpr hu.2⟩

private theorem cos_nonneg_on_support {A r u : ℝ} (hr : 0 ≤ r)
    (hcut : r*A ≤ π/2) (hu : u ∈ Icc 0 A) : 0 ≤ cos (r*u) :=
  cos_nonneg_of_mem_Icc ⟨by linarith [mul_nonneg hr hu.1, pi_pos],
    (mul_le_mul_of_nonneg_left hu.2 hr).trans hcut⟩

/-- Moving a zero sideways cannot reduce its contribution below the uniform band bound. -/
theorem band_integrand_lower {A r u d : ℝ} (x : ℝ) (hA : 0 < A) (hr : 0 ≤ r)
    (hcut : r*A ≤ π/2) (hu : u ∈ Icc 0 A) (hd : |d| ≤ r) :
    lowerIntegrand A r u ≤ weight A u * cos (d*u) * cosh (x*u) := by
  have hru := (mul_le_mul_of_nonneg_left hu.2 hr).trans hcut
  have hcos : cos (r*u) ≤ cos (d*u) := by
    rw [← cos_abs (d*u)]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
    simpa [abs_mul, abs_of_nonneg hu.1] using mul_le_mul_of_nonneg_right hd hu.1
  have hw := weight_nonneg hA hu
  have hnn := (cos_nonneg_on_support hr hcut hu).trans hcos
  exact (mul_le_mul_of_nonneg_left hcos hw).trans
    (le_mul_of_one_le_right (mul_nonneg hw hnn) (one_le_cosh _))

/-- Decreasing factors on the positive half of the Fourier support give a lower Riemann sum. -/
theorem lower_antitone {A r : ℝ} (hA : 0 < A) (hr : 0 ≤ r) (hcut : r*A ≤ π/2) :
    AntitoneOn (lowerIntegrand A r) (Icc 0 A) := by
  intro a ha b hb hab
  have hw : weight A b ≤ weight A a := by
    apply div_le_div₀ _ _ (cosh_pos _) _
    · exact taper_nonneg ⟨div_nonneg ha.1 hA.le, (div_le_one hA).mpr ha.2⟩
    · apply taper_antitone _ _ (div_le_div_of_nonneg_right hab hA.le)
      · exact ⟨div_nonneg ha.1 hA.le, (div_le_one hA).mpr ha.2⟩
      · exact ⟨div_nonneg hb.1 hA.le, (div_le_one hA).mpr hb.2⟩
    · apply cosh_strictMonoOn.monotoneOn _ _ (by linarith)
      · exact div_nonneg ha.1 (by norm_num)
      · exact div_nonneg hb.1 (by norm_num)
  have hc := cos_le_cos_of_nonneg_of_le_pi (mul_nonneg hr ha.1)
    (show r*b ≤ π by linarith [mul_le_mul_of_nonneg_left hb.2 hr, pi_pos])
    (mul_le_mul_of_nonneg_left hab hr)
  exact mul_le_mul hw hc (cos_nonneg_on_support hr hcut hb) (weight_nonneg hA ha)

/-- Each rectangle evaluated at its right endpoint lies below the actual integral. -/
theorem right_rectangle_lower {A r a b : ℝ} (hA : 0 < A) (hr : 0 ≤ r)
    (hcut : r*A ≤ π/2) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A) :
    (b-a) * lowerIntegrand A r b ≤ ∫ u in a..b, lowerIntegrand A r u := by
  have hc : Continuous (lowerIntegrand A r) := by
    unfold lowerIntegrand weight taper
    fun_prop (disch := exact fun x => (cosh_pos _).ne')
  have h := intervalIntegral.integral_mono_on (μ := volume) hab
    (f := fun _ : ℝ => lowerIntegrand A r b) intervalIntegrable_const
    (hc.intervalIntegrable a b) (fun x hx =>
      lower_antitone hA hr hcut ⟨ha.trans hx.1, hx.2.trans hb⟩
        ⟨ha.trans hab, hb⟩ hx.2)
  simpa [smul_eq_mul] using h

/-- Any increasing partition of the Fourier support gives a rigorous lower sum.
The numerical replay takes 4,096 equal subintervals. -/
theorem partition_lower {A r : ℝ} (hA : 0 < A) (hr : 0 ≤ r) (hcut : r*A ≤ π/2)
    (p : ℕ → ℝ) (n : ℕ) (hp : Monotone p) (h₀ : p 0 = 0) (hₙ : p n = A) :
    ∑ k ∈ Finset.range n, (p (k+1) - p k) * lowerIntegrand A r (p (k+1))
      ≤ ∫ u in (0 : ℝ)..A, lowerIntegrand A r u := by
  have hc : Continuous (lowerIntegrand A r) := by
    unfold lowerIntegrand weight taper
    fun_prop (disch := exact fun x => (cosh_pos _).ne')
  calc
    _ ≤ ∑ k ∈ Finset.range n, ∫ u in p k..p (k+1), lowerIntegrand A r u := by
      apply Finset.sum_le_sum
      intro k hk
      apply right_rectangle_lower hA hr hcut
      · simpa only [h₀] using hp (Nat.zero_le k)
      · exact hp (Nat.le_succ k)
      · simpa only [hₙ] using hp (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
    _ = _ := by
      simpa only [h₀, hₙ] using
        (intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := n)
          (fun k _ => hc.intervalIntegrable (p k) (p (k+1))))

/-- The lower sum applies directly to the real Fourier integral at every zero
whose height differs from the test height by at most r, for any real displacement x. -/
theorem partition_le_band_weight {A r d : ℝ} (x : ℝ) (hA : 0 < A) (hr : 0 ≤ r)
    (hcut : r*A ≤ π/2) (hd : |d| ≤ r) (p : ℕ → ℝ) (n : ℕ)
    (hp : Monotone p) (h₀ : p 0 = 0) (hₙ : p n = A) :
    2 * (∑ k ∈ Finset.range n, (p (k+1) - p k) * lowerIntegrand A r (p (k+1)))
      ≤ 2 * ∫ u in (0 : ℝ)..A, weight A u * cos (d*u) * cosh (x*u) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (partition_lower hA hr hcut p n hp h₀ hₙ).trans
  apply intervalIntegral.integral_mono_on hA.le
  · apply Continuous.intervalIntegrable
    unfold lowerIntegrand weight taper
    fun_prop (disch := exact fun u => (cosh_pos _).ne')
  · apply Continuous.intervalIntegrable
    unfold weight taper
    fun_prop (disch := exact fun u => (cosh_pos _).ne')
  · exact fun u hu => band_integrand_lower x hA hr hcut hu hd

end SuperZeta.GaussianDiskKernel
