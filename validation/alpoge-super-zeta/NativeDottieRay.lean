import SuperZeta.Oriented.FirstCorrection
import SuperZeta.Oriented.LiuConnection
import SuperZeta.MellinContinuation
import SuperZeta.Multiplicity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The negative ray of the two archived native Dottie determinants. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex TraceRecovery

/-- The determinant's phase is the negative of the native angle. -/
def phase (positiveAngle : Bool) : ℝ :=
  if positiveAngle then -(Real.pi / 6) else Real.pi / 6

def sineSign (positiveAngle : Bool) : ℝ :=
  if positiveAngle then -1 else 1

theorem sineSign_sq (positiveAngle : Bool) : sineSign positiveAngle ^ 2 = 1 := by
  cases positiveAngle <;> norm_num [sineSign]

theorem sin_phase (positiveAngle : Bool) :
    Real.sin (phase positiveAngle) = sineSign positiveAngle / 2 := by
  cases positiveAngle <;> norm_num [phase, sineSign, Real.sin_pi_div_six, Real.sin_neg]

theorem cos_phase_sq (positiveAngle : Bool) : Real.cos (phase positiveAngle) ^ 2 = 3/4 := by
  cases positiveAngle <;> simp only [phase, Bool.false_eq_true, if_false, if_true,
    Real.cos_neg, Real.sq_cos_pi_div_six]

theorem cos_phase_ne (positiveAngle : Bool) : Real.cos (phase positiveAngle) ≠ 0 := by
  intro h
  have hs := cos_phase_sq positiveAngle
  norm_num [h] at hs

def determinant (positiveAngle : Bool) : ℂ → ℂ :=
  signedDet 1 (phase positiveAngle)

theorem determinant_sq (positiveAngle : Bool) (z : ℂ) :
    determinant positiveAngle (z^2) =
      (4/3 : ℂ) * (cos z ^ 2 - 1/4 - z^2 + (sineSign positiveAngle : ℂ)*(z*sin z)) := by
  have hcos : (Real.cos (phase positiveAngle) : ℂ)^2 = 3/4 := by
    rw [← Complex.ofReal_pow, cos_phase_sq, Complex.ofReal_div]
    norm_num
  rw [determinant, signedDet_sq_expanded, sin_phase, hcos]
  have hsq : (sineSign positiveAngle : ℂ)^2 = 1 := by
    exact_mod_cast sineSign_sq positiveAngle
  push_cast
  linear_combination (-(1/3 : ℂ))*hsq

theorem reference_sq (positiveAngle : Bool) (z : ℂ) :
    referenceDet (phase positiveAngle) (z^2) = (4/3 : ℂ) * (cos z ^ 2 - 1/4) := by
  have hcos : (Real.cos (phase positiveAngle) : ℂ)^2 = 3/4 := by
    rw [← Complex.ofReal_pow, cos_phase_sq, Complex.ofReal_div]
    norm_num
  rw [referenceDet, signedDet_sq_expanded, sin_phase, hcos]
  have hsq : (sineSign positiveAngle : ℂ)^2 = 1 := by
    exact_mod_cast sineSign_sq positiveAngle
  push_cast
  linear_combination (-(1/3 : ℂ))*hsq

/-- Exact determinant contrast for the two native angles. -/
theorem determinant_contrast_sq (z : ℂ) :
    determinant false (z^2) - determinant true (z^2) = (8/3 : ℂ) * z * sin z := by
  rw [determinant_sq, determinant_sq]
  norm_num [sineSign]
  ring

theorem determinant_zeros_disjoint_sq (z : ℂ) (h₀ : determinant false (z^2) = 0)
    (h₁ : determinant true (z^2) = 0) : False := by
  have hprod := determinant_contrast_sq z
  rw [h₀, h₁, sub_zero] at hprod
  have hz : z ≠ 0 := by
    intro h
    rw [h, determinant_sq, sineSign] at h₀
    norm_num at h₀
  have hsin : sin z = 0 :=
    (mul_eq_zero.mp hprod.symm).resolve_left (mul_ne_zero (by norm_num) hz)
  have hcos : cos z ^ 2 = 1 := by simpa [hsin] using cos_sq_add_sin_sq z
  rw [determinant_sq, hcos, hsin, mul_zero, mul_zero, add_zero] at h₀
  have hv : z^2 = (3/4 : ℂ) := by linear_combination -(3/4 : ℂ) * h₀
  obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp hsin
  have hk₀ : k ≠ 0 := by intro h; apply hz; simp [hk, h]
  have hka : 1 ≤ |(k : ℝ)| := by
    rcases lt_or_gt_of_ne hk₀ with hneg | hpos
    · rw [abs_of_nonpos (by exact_mod_cast hneg.le)]
      exact_mod_cast (show 1 ≤ -k by omega)
    · rw [abs_of_nonneg (by exact_mod_cast hpos.le)]
      exact_mod_cast (show 1 ≤ k by omega)
  have hk₂ : (1 : ℝ) ≤ (k : ℝ)^2 := by
    simpa only [one_pow, sq_abs] using pow_le_pow_left₀ zero_le_one hka 2
  have hπ₂ : (1 : ℝ) ≤ Real.pi^2 := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one (by linarith [Real.pi_gt_three] :
      (1 : ℝ) ≤ Real.pi) 2
  have hge : (1 : ℝ) ≤ (k : ℝ)^2 * Real.pi^2 := by
    simpa using mul_le_mul hk₂ hπ₂ (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  rw [hk, mul_pow] at hv
  have hreal := congrArg Complex.re hv
  have hc : (3/4 : ℂ).re = (3/4 : ℝ) := by norm_num [Complex.div_re, Complex.normSq_apply]
  rw [hc] at hreal
  have he : ((k : ℝ)^2 * Real.pi^2 : ℝ) = 3/4 := by
    simpa only [← Complex.ofReal_intCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re] using hreal
  linarith

def referenceRay (x : ℝ) : ℝ := 1 + (4/3)*Real.sinh x ^ 2

def rayOffset (positiveAngle : Bool) (x : ℝ) : ℝ :=
  (4/3)*(x^2-sineSign positiveAngle*(x*Real.sinh x))

def determinantRay (positiveAngle : Bool) (x : ℝ) : ℝ :=
  referenceRay x + rayOffset positiveAngle x

theorem reference_ray_eq (positiveAngle : Bool) (x : ℝ) :
    referenceDet (phase positiveAngle) (-((x : ℂ)^2)) = referenceRay x := by
  rw [← show ((x : ℂ)*I)^2 = -((x : ℂ)^2) by rw [mul_pow, I_sq]; ring,
    reference_sq, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have hs : (Real.cosh x : ℂ)^2 - (Real.sinh x : ℂ)^2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq x
  unfold referenceRay
  push_cast at hs ⊢
  linear_combination (4/3 : ℂ)*hs

theorem determinant_ray_eq (positiveAngle : Bool) (x : ℝ) :
    determinant positiveAngle (-((x : ℂ)^2)) = determinantRay positiveAngle x := by
  rw [← show ((x : ℂ)*I)^2 = -((x : ℂ)^2) by rw [mul_pow, I_sq]; ring,
    determinant_sq, Complex.cos_mul_I, Complex.sin_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, mul_pow, I_sq]
  have hterm : ((x : ℂ)*I)*((Real.sinh x : ℂ)*I) = -((x*Real.sinh x : ℝ) : ℂ) := by
    rw [show ((x : ℂ)*I)*((Real.sinh x : ℂ)*I) =
      ((x : ℂ)*(Real.sinh x : ℂ))*I^2 by ring, I_sq, Complex.ofReal_mul]
    ring
  rw [hterm]
  have hs : (Real.cosh x : ℂ)^2 - (Real.sinh x : ℂ)^2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq x
  unfold determinantRay referenceRay rayOffset
  push_cast at hs ⊢
  linear_combination (4/3 : ℂ)*hs

theorem reference_ray_pos (x : ℝ) : 0 < referenceRay x := by
  unfold referenceRay
  positivity

theorem determinant_ray_pos (positiveAngle : Bool) (x : ℝ) :
    0 < determinantRay positiveAngle x := by
  have hs := sineSign_sq positiveAngle
  have he : determinantRay positiveAngle x =
      1 + (4/3)*((Real.sinh x - sineSign positiveAngle*x/2)^2 + 3*x^2/4) := by
    unfold determinantRay referenceRay rayOffset
    linear_combination -(x^2/3)*hs
  rw [he]
  positivity

theorem ray_order {x : ℝ} (hx : 0 < x) :
    determinantRay false x < referenceRay x ∧ referenceRay x < determinantRay true x := by
  have hs := Real.self_lt_sinh_iff.mpr hx
  have hh := mul_lt_mul_of_pos_left hs hx
  constructor <;> dsimp [determinantRay, rayOffset, sineSign] <;>
    nlinarith [mul_pos hx (hx.trans hs)]

def realKernel (positiveAngle : Bool) (x : ℝ) : ℝ :=
  Real.log (determinantRay positiveAngle x / referenceRay x)

def kernel (positiveAngle : Bool) (x : ℝ) : ℂ := (realKernel positiveAngle x : ℂ)

theorem kernel_signs {x : ℝ} (hx : 0 < x) :
    realKernel false x < 0 ∧ 0 < realKernel true x := by
  obtain ⟨h₀, h₁⟩ := ray_order hx
  have h := reference_ray_pos x
  exact ⟨Real.log_neg (div_pos (determinant_ray_pos false x) h)
      ((div_lt_one h).mpr h₀),
    Real.log_pos ((one_lt_div h).mpr h₁)⟩

#print axioms firstCorrection_pi_div_six
#print axioms firstCorrection_neg_pi_div_six
#print axioms determinant_contrast_sq
#print axioms determinant_zeros_disjoint_sq
#print axioms reference_ray_eq
#print axioms determinant_ray_eq
#print axioms kernel_signs

end DottieOriented.NativeSpectrum
end
