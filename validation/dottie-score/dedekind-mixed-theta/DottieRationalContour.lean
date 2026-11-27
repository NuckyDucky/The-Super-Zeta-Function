import DottieDyadicGeometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Floor.Semiring

/-! Rational samples on the measuring circumference, with a distance bound
to every point of the circle. -/

namespace SuperZeta.StirlingCorrection

open Complex Set
open scoped ComplexConjugate

noncomputable section

/-- The circle point with half-angle parameter `t`, using rational operations. -/
def rationalUnitArc (t : ℝ) : ℂ := (1 + I * (t : ℂ)) / (1 - I * (t : ℂ))

private theorem denominator_norm_ge_one (t : ℝ) : 1 ≤ ‖1 - I * (t : ℂ)‖ := by
  simpa [Complex.mul_re] using Complex.abs_re_le_norm (1 - I * (t : ℂ))

private theorem denominator_ne_zero (t : ℝ) : 1 - I * (t : ℂ) ≠ 0 :=
  norm_ne_zero_iff.mp (zero_lt_one.trans_le (denominator_norm_ge_one t)).ne'

theorem rationalUnitArc_norm (t : ℝ) : ‖rationalUnitArc t‖ = 1 := by
  have hc : conj (1 + I * (t : ℂ)) = 1 - I * (t : ℂ) := by simp [sub_eq_add_neg]
  rw [rationalUnitArc, norm_div, ← hc, Complex.norm_conj]
  have h : ‖1 + I * (t : ℂ)‖ ≠ 0 := by
    rw [← Complex.norm_conj (1 + I * (t : ℂ)), hc]
    exact norm_ne_zero_iff.mpr (denominator_ne_zero t)
  exact div_self h

theorem rationalUnitArc_difference_le (t u : ℝ) :
    ‖rationalUnitArc t - rationalUnitArc u‖ ≤ 2 * |t - u| := by
  have hEq : rationalUnitArc t - rationalUnitArc u =
      (2 * I * ((t - u : ℝ) : ℂ)) / ((1 - I * (t : ℂ)) * (1 - I * (u : ℂ))) := by
    unfold rationalUnitArc
    push_cast
    field_simp [denominator_ne_zero t, denominator_ne_zero u]
    ring
  have hden : 1 ≤ ‖(1 - I * (t : ℂ)) * (1 - I * (u : ℂ))‖ := by
    rw [norm_mul]
    exact one_le_mul_of_one_le_of_one_le (denominator_norm_ge_one t) (denominator_norm_ge_one u)
  rw [hEq, norm_div]
  apply (div_le_iff₀ (zero_lt_one.trans_le hden)).mpr
  simp only [norm_mul, norm_ofNat, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact le_mul_of_one_le_right (by positivity) (by simpa only [norm_mul] using hden)

private theorem exists_rationalUnitArc_of_first_quadrant {z : ℂ}
    (hn : ‖z‖ = 1) (hx : 0 ≤ z.re) (hy : 0 ≤ z.im) :
    ∃ t ∈ Icc (0 : ℝ) 1, rationalUnitArc t = z := by
  let t := z.im / (1 + z.re)
  have hd : 0 < 1 + z.re := by linarith
  have hn' := Complex.sq_norm z
  rw [hn, one_pow, normSq_apply] at hn'
  have hym : z.im ≤ 1 := (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans_eq hn)
  refine ⟨t, ⟨div_nonneg hy hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
  apply (div_eq_iff (denominator_ne_zero t)).mpr
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    dsimp [t]
    field_simp
    linarith only [hn']
  · simp [Complex.mul_re, Complex.mul_im]
    dsimp [t]
    field_simp
    ring

open Classical in
/-- The four exact rotations used to cover the unit circle. -/
def contourQuarterTurns : Finset ℂ := {1, I, -1, -I}

private theorem norm_of_mem_contourQuarterTurns {a : ℂ} (ha : a ∈ contourQuarterTurns) :
    ‖a‖ = 1 := by
  classical
  simp only [contourQuarterTurns, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp

private theorem exists_quarter_first_quadrant {z : ℂ} (hn : ‖z‖ = 1) :
    ∃ a ∈ contourQuarterTurns, ∃ u : ℂ,
      ‖u‖ = 1 ∧ 0 ≤ u.re ∧ 0 ≤ u.im ∧ z = a * u := by
  classical
  by_cases hx : 0 ≤ z.re <;> by_cases hy : 0 ≤ z.im
  · exact ⟨1, by simp [contourQuarterTurns], z, hn, hx, hy, (one_mul z).symm⟩
  · refine ⟨-I, by simp [contourQuarterTurns], I * z, by simp [hn], ?_, ?_, ?_⟩
    · simpa [Complex.mul_re] using neg_nonneg.mpr (le_of_not_ge hy)
    · simpa [Complex.mul_im] using hx
    · rw [← mul_assoc]
      simp
  · refine ⟨I, by simp [contourQuarterTurns], -I * z, by simp [hn], ?_, ?_, ?_⟩
    · simpa [Complex.mul_re] using hy
    · simpa [Complex.mul_im] using neg_nonneg.mpr (le_of_not_ge hx)
    · rw [← mul_assoc]
      simp
  · exact ⟨-1, by simp [contourQuarterTurns], -z, by simp [hn],
      by simpa using neg_nonneg.mpr (le_of_not_ge hx),
      by simpa using neg_nonneg.mpr (le_of_not_ge hy), by simp⟩

/-- For a rational center and radius these samples are rational complex points. -/
def rationalContourSample (c : ℂ) (r : ℝ) (a : ℂ) (m j : ℕ) : ℂ :=
  c + (r : ℂ) * (a * rationalUnitArc ((j : ℝ) / m))

theorem rationalContourSample_mem_sphere {c a : ℂ} {r : ℝ} (hr : 0 < r)
    {m j : ℕ} (ha : a ∈ contourQuarterTurns) :
    rationalContourSample c r a m j ∈ Metric.sphere c r := by
  rw [Metric.mem_sphere, dist_eq_norm]
  simp [rationalContourSample, norm_of_mem_contourQuarterTurns ha,
    rationalUnitArc_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- At (m+1) samples per quadrant the distance allowance is `2*r/m`. -/
theorem exists_near_rationalContourSample {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ Metric.sphere c r) {m : ℕ} (hm : 0 < m) :
    ∃ a ∈ contourQuarterTurns, ∃ j ≤ m,
      dist z (rationalContourSample c r a m j) ≤ 2 * r / (m : ℝ) := by
  let v := (z - c) / (r : ℂ)
  have hv : ‖v‖ = 1 := by
    rw [show v = (z-c)/(r:ℂ) from rfl, norm_div, ← dist_eq_norm, Metric.mem_sphere.mp hz,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  obtain ⟨a, ha, u, hu, hx, hy, hvu⟩ := exists_quarter_first_quadrant hv
  obtain ⟨t, ht, htu⟩ := exists_rationalUnitArc_of_first_quadrant hu hx hy
  have hvt : v = a * rationalUnitArc t := by rw [htu, hvu]
  have hzEq : z = c + (r : ℂ) * (a * rationalUnitArc t) := by
    rw [← hvt, show v = (z-c)/(r:ℂ) from rfl, ← mul_div_assoc,
      mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
    ring
  let j := ⌊t * (m : ℝ)⌋₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hjlow : (j : ℝ) ≤ t * m := Nat.floor_le (mul_nonneg ht.1 hmR.le)
  have hjhigh : t * m < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj : j ≤ m := by
    exact_mod_cast hjlow.trans (mul_le_of_le_one_left hmR.le ht.2)
  have hdivlow : (j : ℝ) / m ≤ t := (div_le_iff₀ hmR).mpr hjlow
  have hdivhigh : t ≤ ((j : ℝ) + 1) / m := (le_div_iff₀ hmR).mpr hjhigh.le
  have hmesh : |t - (j : ℝ) / m| ≤ 1 / m := by
    rw [add_div] at hdivhigh
    rw [abs_of_nonneg (sub_nonneg.mpr hdivlow)]
    linarith
  refine ⟨a, ha, j, hj, ?_⟩
  rw [dist_eq_norm, hzEq, rationalContourSample]
  rw [show c + (r : ℂ) * (a * rationalUnitArc t) -
      (c + (r : ℂ) * (a * rationalUnitArc ((j : ℝ) / m))) =
        (r : ℂ) * a * (rationalUnitArc t - rationalUnitArc ((j : ℝ) / m)) by ring,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
    norm_of_mem_contourQuarterTurns ha, mul_one]
  calc
    _ ≤ r * (2 * |t - (j : ℝ) / m|) :=
      mul_le_mul_of_nonneg_left (rationalUnitArc_difference_le _ _) hr.le
    _ ≤ r * (2 * (1 / m)) := by gcongr
    _ = _ := by ring

/-- A derivative allowance and finitely many sample bounds give the signed
inequality everywhere on the original circumference. -/
theorem dottie_signed_boundary_of_rational_samples {F : ℂ → ℂ} {axis : ℂ}
    {T M margin : ℝ} {n m : ℕ} (hm : 0 < m) (hM : 0 ≤ M)
    (hF : ∀ z ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      DifferentiableAt ℂ F z)
    (hderiv : ∀ z ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      ‖deriv F z‖ ≤ M)
    (hsamples : ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      (axis * F (rationalContourSample (dottieScaledRightCenter T n)
        (dottieScaledRadius n) a m j)).im +
        ‖axis‖ * (M * (2 * dottieScaledRadius n / (m : ℝ))) ≤ -margin) :
    ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (axis * F z).im ≤ -margin := by
  intro z hz
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := by dsimp [r, dottieScaledRadius, dottieRingScale]; positivity
  obtain ⟨a, ha, j, hj, hzdist⟩ := exists_near_rationalContourSample hr hz hm
  let p := rationalContourSample c r a m j
  have hp : p ∈ Metric.closedBall c r :=
    Metric.sphere_subset_closedBall (rationalContourSample_mem_sphere hr ha)
  have hvar : ‖F z - F p‖ ≤ M * (2 * r / (m : ℝ)) := by
    refine (Convex.norm_image_sub_le_of_norm_deriv_le hF hderiv (convex_closedBall c r)
      hp (Metric.sphere_subset_closedBall hz)).trans ?_
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left hzdist hM
  have hdiff : (axis * (F z - F p)).im ≤ ‖axis‖ * (M * (2 * r / (m : ℝ))) := by
    refine (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
  rw [mul_sub, sub_im] at hdiff
  have hs : (axis * F p).im + ‖axis‖ * (M * (2 * r / (m : ℝ))) ≤ -margin :=
    hsamples a ha j hj
  linarith

#print axioms rationalContourSample_mem_sphere
#print axioms exists_near_rationalContourSample
#print axioms dottie_signed_boundary_of_rational_samples

end

end SuperZeta.StirlingCorrection
