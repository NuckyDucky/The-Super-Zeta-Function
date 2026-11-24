import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Convert a signed prime-power window to the coordinate w = 2*s.
The input function is supplied in the original norm variable. -/

namespace SuperZeta.CrossleyQuarter

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

def squarePull (R : ℝ → ℝ) (X : ℝ) : ℝ := R (Real.sqrt X)

def compact (q : ℝ) (R : ℝ → ℝ) (X : ℝ) : ℝ := -R X + 3*R (X/q) - 2*R (X/q^2)

theorem compact_squarePull (R : ℝ → ℝ) (X : ℝ) :
    compact 4 (squarePull R) X = squarePull (compact 2 R) X := by
  unfold compact squarePull
  rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
    Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 4^2)]
  norm_num

/-- A pointwise upper bound on arbitrarily late intervals of a fixed stretch. -/
def LateWindow (G : ℝ → ℝ) (θ stretch : ℝ) : Prop :=
  ∀ A : ℝ, ∃ Y ≥ max A 2, ∀ x ∈ Icc Y (Y^stretch), G x ≤ x^θ

private theorem sq_rpow {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x^2)^a = (x^a)^2 := by
  rw [← Real.rpow_two x, ← Real.rpow_mul hx, mul_comm (2:ℝ) a,
    Real.rpow_mul hx, Real.rpow_two]

private theorem sq_rpow_half {x θ : ℝ} (hx : 0 ≤ x) :
    (x^2)^(θ/2) = x^θ := by
  rw [← Real.rpow_two x, ← Real.rpow_mul hx, show 2*(θ/2) = θ by ring]

/-- The exponents halve and the stretch of the pointwise window stays fixed. -/
theorem lateWindow_square_iff (G : ℝ → ℝ) (θ stretch : ℝ) :
    LateWindow (squarePull G) (θ/2) stretch ↔ LateWindow G θ stretch := by
  constructor
  · intro h A
    let Y₀ := max A 2
    have hy₀ : 0 ≤ Y₀ := le_trans (by norm_num) (le_max_right A 2)
    obtain ⟨Y,hY,hW⟩ := h (Y₀^2)
    have hy : 0 ≤ Y := le_trans (by positivity : 0 ≤ Y₀^2) (le_trans (le_max_left _ _) hY)
    have hstart := Real.sqrt_le_sqrt (le_trans (le_max_left (Y₀^2) 2) hY)
    rw [Real.sqrt_sq hy₀] at hstart
    refine ⟨Real.sqrt Y,hstart,fun x hx => ?_⟩
    have hx₀ : 0 ≤ x := (Real.sqrt_nonneg _).trans hx.1
    have hb : x^2 ∈ Icc Y (Y^stretch) := by
      constructor
      · rw [← Real.sq_sqrt hy]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg Y) hx.1 2
      · rw [← Real.sq_sqrt hy, sq_rpow (Real.sqrt_nonneg Y)]
        exact pow_le_pow_left₀ hx₀ hx.2 2
    simpa only [squarePull, Real.sqrt_sq hx₀, sq_rpow_half hx₀] using hW (x^2) hb
  · intro h A
    obtain ⟨Y,hY,hW⟩ := h A
    have hy : 0 ≤ Y := le_trans (by norm_num : (0:ℝ) ≤ 2) ((le_max_right A 2).trans hY)
    have hYY : Y ≤ Y^2 := by nlinarith only [((le_max_right A 2).trans hY : 2 ≤ Y), sq_nonneg (Y-1)]
    refine ⟨Y^2,hY.trans hYY,fun X hX => ?_⟩
    have hX₀ : 0 ≤ X := (sq_nonneg Y).trans hX.1
    have hlo := Real.sqrt_le_sqrt hX.1
    rw [Real.sqrt_sq hy] at hlo
    have hhi := Real.sqrt_le_sqrt hX.2
    rw [sq_rpow hy, Real.sqrt_sq (Real.rpow_nonneg hy _)] at hhi
    have hp := sq_rpow_half (θ := θ) (Real.sqrt_nonneg X)
    rw [Real.sq_sqrt hX₀] at hp
    calc
      squarePull G X ≤ (Real.sqrt X)^θ := hW _ ⟨hlo,hhi⟩
      _ = X^(θ/2) := hp.symm

/-- Prime variables are logarithmic here. Halving the Mellin coordinate doubles
the logarithmic cutoff. The integral contributes the exact factor two. -/
def logMellin (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ u in Ioi (0:ℝ), (g u : ℂ) * Complex.exp (-s*u)

theorem logMellin_double_cutoff (g : ℝ → ℝ) (s : ℂ) :
    logMellin (fun u => g (u/2)) s = 2 * logMellin g (2*s) := by
  let f := fun u : ℝ => (g u : ℂ) * Complex.exp (-(2*s)*u)
  have hf : (fun u : ℝ => (g (u/2) : ℂ) * Complex.exp (-s*u)) =
      fun u => f (u*(1/2)) := by
    funext u
    unfold f
    rw [show u*(1/2) = u/2 by ring]
    congr 1
    push_cast
    congr 1
    ring
  unfold logMellin
  rw [hf]
  simpa [f, Complex.real_smul] using
    integral_comp_mul_right_Ioi f 0 (by norm_num : (0:ℝ) < 1/2)

/-- The Jacobian in the Mellin transform cancels the half-address scaling
of the displacement, preserving the residue. -/
theorem residue_at_half_address {F : ℂ → ℂ} {w residue : ℂ}
    (h : Tendsto (fun z => (z-w)*F z) (𝓝[≠] w) (𝓝 residue)) :
    Tendsto (fun z => (z-w/2)*(2*F (2*z))) (𝓝[≠] (w/2)) (𝓝 residue) := by
  have he : (2:ℂ)*(w/2) = w := by ring
  have hs : Tendsto (fun z : ℂ => 2*z) (𝓝[≠] (w/2)) (𝓝[≠] w) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun z : ℂ => 2*z) (w/2) := continuousAt_const.mul continuousAt_id
      simpa only [he] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z ≠ w/2 at hz
      change 2*z ≠ w
      intro eq
      exact hz ((eq_div_iff (by norm_num : (2:ℂ) ≠ 0)).2 (by simpa only [mul_comm z 2] using eq))
  apply (h.comp hs).congr'
  filter_upwards with z
  simp only [Function.comp_apply]
  ring

#print axioms compact_squarePull
#print axioms lateWindow_square_iff
#print axioms logMellin_double_cutoff
#print axioms residue_at_half_address

end
end SuperZeta.CrossleyQuarter
