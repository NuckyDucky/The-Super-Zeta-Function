import SuperZeta.Reciprocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The Dottie spire manuscript, section "The exact fixed curve and Dottie fold".
The phase parameter and its two logarithms are retained explicitly. -/

noncomputable section

namespace SuperZeta.Dottie

open SuperZeta.Reciprocal
open scoped Topology

/-- Existence and uniqueness on the manuscript's centerline parameter interval. -/
theorem existsUnique_dottie :
    ∃! d : ℝ, d ∈ Set.Ioo 0 (Real.pi/2) ∧ d = Real.cos d := by
  have hp := Real.pi_div_two_pos
  have hcont : Continuous (fun u : ℝ => u - Real.cos u) :=
    continuous_id.sub Real.continuous_cos
  have hz : (0 : ℝ) ∈ Set.Icc (0 - Real.cos 0) (Real.pi / 2 - Real.cos (Real.pi / 2)) := by
    rw [Real.cos_zero, Real.cos_pi_div_two]
    exact ⟨by norm_num, by linarith⟩
  obtain ⟨d, hd, he⟩ := intermediate_value_Icc hp.le hcont.continuousOn hz
  change d - Real.cos d = 0 at he
  have hfix : d = Real.cos d := sub_eq_zero.mp he
  have hd0 : d ≠ 0 := by
    intro e
    simp [e] at hfix
  have hdpi : d ≠ Real.pi/2 := by
    intro e
    rw [e, Real.cos_pi_div_two] at hfix
    linarith
  refine ⟨d, ⟨⟨lt_of_le_of_ne hd.1 (Ne.symm hd0), lt_of_le_of_ne hd.2 hdpi⟩, hfix⟩, ?_⟩
  rintro y ⟨hy, hey⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hc := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hy.1.le hd.2 h
    linarith
  · have hc := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hd.1 hy.2.le h
    linarith

def eccentricity (u : ℝ) := u / Real.cos u
def amplitude (u : ℝ) := eccentricity u * Real.sin u
def height (u : ℝ) := eccentricity u * Real.exp (-amplitude u)
def parameter (u : ℝ) : ℂ := Complex.I * ↑(height u)
def upperLog (u : ℝ) : ℂ := ↑(amplitude u) + ↑u * Complex.I
def lowerLog (u : ℝ) : ℂ := ↑(amplitude u) - ↑u * Complex.I
def phasePair (u : ℝ) : ℂ × ℂ := (Complex.exp (upperLog u), Complex.exp (lowerLog u))

private theorem ecc_mul_cos {u : ℝ} (hc : Real.cos u ≠ 0) :
    eccentricity u * Real.cos u = u := div_mul_cancel₀ _ hc

private theorem imag_rotation (s c : ℂ) :
    Complex.I * (c + s * Complex.I) = -s + c * Complex.I := by
  calc Complex.I * (c + s * Complex.I) = c * Complex.I + s * (Complex.I * Complex.I) := by ring
       _ = -s + c * Complex.I := by rw [Complex.I_mul_I]; ring

/-- The physical parameter times each opposite phase gives its actual exponent. -/
theorem centerline_lifts {u : ℝ} (hc : Real.cos u ≠ 0) :
    parameter u * (phasePair u).2 = upperLog u ∧
    -parameter u * (phasePair u).1 = lowerLog u := by
  have hc' : (eccentricity u : ℂ) * ↑(Real.cos u) = ↑u := by
    exact_mod_cast ecc_mul_cos hc
  have hs' : (eccentricity u : ℂ) * ↑(Real.sin u) = ↑(amplitude u) := by
    simp [amplitude]
  have hparam : parameter u =
      Complex.I * ↑(eccentricity u) * Complex.exp (-(amplitude u : ℂ)) := by
    simp [parameter, height, Complex.ofReal_exp, mul_assoc]
  have hup : Complex.exp (-(amplitude u : ℂ)) * Complex.exp (upperLog u) =
      (Real.cos u : ℂ) + ↑(Real.sin u) * Complex.I := by
    rw [← Complex.exp_add]
    simp [upperLog, Complex.exp_mul_I]
  have hlo : Complex.exp (-(amplitude u : ℂ)) * Complex.exp (lowerLog u) =
      (Real.cos u : ℂ) + (-(Real.sin u : ℂ)) * Complex.I := by
    rw [← Complex.exp_add]
    have he : -(amplitude u : ℂ) + lowerLog u = (-(u : ℂ)) * Complex.I := by
      dsimp [lowerLog]; ring
    rw [he, Complex.exp_mul_I]
    simp
  constructor
  · change parameter u * Complex.exp (lowerLog u) = upperLog u
    rw [hparam, mul_assoc, hlo, mul_comm Complex.I, mul_assoc, imag_rotation]
    simp only [neg_neg, mul_add, ← mul_assoc, hc', hs', upperLog]
  · change -parameter u * Complex.exp (upperLog u) = lowerLog u
    rw [neg_mul, hparam, mul_assoc, hup, mul_comm Complex.I, mul_assoc, imag_rotation]
    simp only [mul_add, mul_neg, ← mul_assoc, hs', hc', lowerLog]
    ring

theorem centerline_fixed {u : ℝ} (hc : Real.cos u ≠ 0) :
    step (parameter u) (phasePair u) = phasePair u := by
  obtain ⟨hp, hm⟩ := centerline_lifts hc
  exact Prod.ext (congrArg Complex.exp hp) (congrArg Complex.exp hm)

theorem centerline_multiplier {u : ℝ} (hc : Real.cos u ≠ 0) :
    deriv (scalarReturn (parameter u)) (phasePair u).1 = ↑(eccentricity u ^ 2) := by
  have hr := (fixed_return_multiplier (centerline_fixed hc)).2
  obtain ⟨hp, hm⟩ := centerline_lifts hc
  change deriv (scalarReturn (parameter u)) (phasePair u).1 =
    (parameter u * (phasePair u).2) * (-parameter u * (phasePair u).1) at hr
  rw [hr, hp, hm]
  have htrig : amplitude u ^ 2 + u ^ 2 = eccentricity u ^ 2 := by
    calc amplitude u ^ 2 + u ^ 2 =
          (eccentricity u * Real.sin u)^2 + (eccentricity u * Real.cos u)^2 := by
            rw [ecc_mul_cos hc]; rfl
         _ =
          eccentricity u ^ 2 * ((Real.sin u)^2 + (Real.cos u)^2) := by
            ring
         _ = eccentricity u ^ 2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
  calc upperLog u * lowerLog u =
       (amplitude u : ℂ)^2 - (u : ℂ)^2 * Complex.I^2 := by unfold upperLog lowerLog; ring
       _ = ↑(amplitude u ^ 2 + u ^ 2) := by rw [Complex.I_sq]; push_cast; ring
       _ = ↑(eccentricity u ^ 2) := congrArg (fun r : ℝ => (r : ℂ)) htrig

private theorem ecc_derivative {u : ℝ} (hc : Real.cos u ≠ 0) :
    HasDerivAt eccentricity ((Real.cos u + u * Real.sin u) / Real.cos u ^ 2) u := by
  convert (hasDerivAt_id u).div (Real.hasDerivAt_cos u) hc using 1
  dsimp [eccentricity]
  ring

/-- The slope factorizes, so the location of its zero can be decided exactly. -/
theorem height_hasDerivAt {u : ℝ} (hc : Real.cos u ≠ 0) :
    HasDerivAt height
      (Real.exp (-amplitude u) * ((Real.cos u)^2-u^2) / (Real.cos u)^3) u := by
  have he := ecc_derivative hc
  have ha := he.mul (Real.hasDerivAt_sin u)
  have hh := he.mul ha.neg.exp
  change HasDerivAt height _ u at hh
  convert hh using 1
  change _ = _ * Real.exp (-amplitude u) +
    eccentricity u * (Real.exp (-amplitude u) * (-(_ * Real.sin u + eccentricity u * Real.cos u)))
  unfold eccentricity
  field_simp [hc]
  ring_nf
  simp only [show Real.sin u ^ 2 = 1 - Real.cos u ^ 2 by linarith [Real.sin_sq_add_cos_sq u]]
  ring

theorem stationary_iff_dottie {u : ℝ} (hu : u ∈ Set.Ioo 0 (Real.pi/2)) :
    deriv height u = 0 ↔ u = Real.cos u := by
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [hu.1, Real.pi_div_two_pos], hu.2⟩
  rw [(height_hasDerivAt hc.ne').deriv, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have hx := (mul_eq_zero.mp h).resolve_left (Real.exp_ne_zero _)
      nlinarith [hu.1]
    · exact False.elim ((pow_ne_zero 3 hc.ne') h)
  · intro h
    exact Or.inl (by rw [show (Real.cos u)^2 - u^2 = 0 by rw [← h]; ring, mul_zero])

/-- At the Dottie parameter the centerline contains a fixed phase pair and
its positive-rooted return derivative is exactly one. -/
theorem dottie_fixed_multiplier {d : ℝ} (hd : d ∈ Set.Ioo 0 (Real.pi/2)) (he : d = Real.cos d) :
    step (parameter d) (phasePair d) = phasePair d ∧
    deriv (scalarReturn (parameter d)) (phasePair d).1 = 1 ∧
    height d = Real.exp (-Real.sin d) := by
  have hc : Real.cos d ≠ 0 := by rw [← he]; exact ne_of_gt hd.1
  have hε : eccentricity d = 1 := by unfold eccentricity; rw [← he, div_self (ne_of_gt hd.1)]
  refine ⟨centerline_fixed hc, ?_, ?_⟩
  · rw [centerline_multiplier hc, hε]; simp
  · simp [height, amplitude, hε]

/-- Nondegeneracy of the fold, in the original lift parameter. The Taylor
coefficient of the quadratic term is half this second derivative. -/
theorem dottie_second_derivative {d : ℝ} (hd : d ∈ Set.Ioo 0 (Real.pi/2))
    (he : d = Real.cos d) :
    deriv (deriv height) d = -2 * Real.exp (-Real.sin d) * (1 + Real.sin d) / d^2 := by
  have hd0 := ne_of_gt hd.1
  have hc : Real.cos d ≠ 0 := he ▸ hd0
  let f : ℝ → ℝ := fun u => Real.exp (-amplitude u) / (Real.cos u)^3
  let g : ℝ → ℝ := fun u => (Real.cos u)^2 - u^2
  have hlocal : deriv height =ᶠ[𝓝 d] fun u => f u * g u := by
    filter_upwards [Real.continuous_cos.continuousAt.eventually_ne hc] with u hu
    rw [(height_hasDerivAt hu).deriv]
    dsimp [f, g]
    ring
  have ha := (ecc_derivative hc).mul (Real.hasDerivAt_sin d)
  have hf : DifferentiableAt ℝ f d :=
    ha.neg.exp.differentiableAt.div ((Real.hasDerivAt_cos d).differentiableAt.pow 3) (pow_ne_zero _ hc)
  have hg : HasDerivAt g (-2*d*(1+Real.sin d)) d := by
    convert ((Real.hasDerivAt_cos d).pow 2).sub ((hasDerivAt_id d).pow 2) using 1
    dsimp
    rw [← he]
    ring
  have hgd : g d = 0 := by dsimp [g]; rw [← he, sub_self]
  have had : amplitude d = Real.sin d := by
    unfold amplitude eccentricity
    rw [← he, div_self hd0, one_mul]
  rw [hlocal.deriv_eq, (hf.hasDerivAt.mul hg).deriv, hgd, mul_zero, zero_add]
  dsimp [f]
  rw [had, ← he]
  field_simp
  ring

theorem dottie_curvature_neg {d : ℝ} (hd : d ∈ Set.Ioo 0 (Real.pi/2))
    (he : d = Real.cos d) : deriv (deriv height) d < 0 := by
  have hs : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd.1 (by linarith [hd.2, Real.pi_pos])
  rw [dottie_second_derivative hd he]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)) (by linarith))
    (sq_pos_of_pos hd.1)

end SuperZeta.Dottie
