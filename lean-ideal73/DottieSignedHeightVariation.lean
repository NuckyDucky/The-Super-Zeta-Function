import DottieSignedBlockVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace QuarticModel

open Finset

private theorem height_phase_step (t : ℝ) {x y : ℝ} (hxy : x ≤ y) :
    ‖Complex.exp (Complex.I * ((t*y : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))‖ ≤ |t| * (y-x) := by
  have hsplit : Complex.I * ((t*y : ℝ) : ℂ) =
      Complex.I * ((t*x : ℝ) : ℂ) + Complex.I * ((t*(y-x) : ℝ) : ℂ) := by
    push_cast
    ring
  have hprod : Complex.exp (Complex.I * ((t*y : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((t*x : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((t*(y-x) : ℝ) : ℂ))-1) := by
    rw [hsplit, Complex.exp_add]
    ring
  rw [hprod, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(y-x)))

/-- A vertical shift of an anchored Dirichlet block rotates each coefficient.
The Abel bound uses a constant `|t|` for the phase variation. -/
theorem dottie_signed_block_height_displacement (c : ℕ → ℂ) (u : ℕ → ℝ)
    (n : ℕ) (A L t : ℝ) (hu : Monotone u) (hu₀ : 0 ≤ u 0) (huN : u n ≤ L)
    (hprefix : ∀ k ≤ n + 1, ‖∑ i ∈ range k, c i‖ ≤ A) :
    ‖∑ i ∈ range (n + 1), (Complex.exp (Complex.I * ((t*u i : ℝ) : ℂ))-1) * c i‖ ≤
      2 * A * |t| * L := by
  let f := fun x : ℝ => Complex.exp (Complex.I * ((t*x : ℝ) : ℂ))-1
  have hA : 0 ≤ A := (norm_nonneg _).trans (hprefix 0 (Nat.zero_le _))
  have hvariation (x y : ℝ) (_ : 0 ≤ x) (hxy : x ≤ y) (_ : y ≤ L) :
      ‖f y-f x‖ ≤ |t| * (y-x) := by
    dsimp only [f]
    rw [sub_sub_sub_cancel_right]
    exact height_phase_step t hxy
  have hend : ‖f (u n)‖ ≤ |t| * L := by
    have h := height_phase_step t (hu₀.trans (hu (Nat.zero_le n)))
    simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left huN (abs_nonneg _))
  refine (dottie_signed_block_lipschitz c f u n A L |t| hu hu₀ huN
    (abs_nonneg _) hvariation hprefix).trans ?_
  calc
    _ ≤ A * (|t| * L + |t| * L) := mul_le_mul_of_nonneg_left (add_le_add hend le_rfl) hA
    _ = _ := by ring

#print axioms dottie_signed_block_height_displacement

end QuarticModel
