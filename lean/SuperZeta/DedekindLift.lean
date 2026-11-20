import SuperZeta.Reciprocal
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Complex SuperZeta.Reciprocal

namespace SuperZeta.DedekindPhase

/-- Every logarithm of -τ furnishes the actual two exponents for the
project's ordered map.  The shift d records which logarithm was used. -/
theorem from_log_sheet {τ d : ℂ} (h1 : τ ≠ 1) (hd : d ≠ 0)
    (hsheet : exp d = -τ) :
    let V := d / (1 - τ)
    let U := τ * V
    let L := U / exp V
    step L (exp U, exp V) = (exp U, exp V) ∧
      lifts L (exp U, exp V) = (U,V) ∧ U / V = τ ∧ V - U = d := by
  let V := d / (1 - τ)
  let U := τ * V
  let L := U / exp V
  change step L (exp U, exp V) = _ ∧ lifts L (exp U, exp V) = _ ∧ U / V = τ ∧ V - U = d
  have hden : 1 - τ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hV : V ≠ 0 := div_ne_zero hd hden
  have hdiff : V - U = d := by
    change d / (1 - τ) - τ * (d / (1 - τ)) = d
    field_simp
    ring
  have hratio : exp V / exp U = -τ := by rw [← exp_sub, hdiff, hsheet]
  have hmul : exp V = (-τ) * exp U := (div_eq_iff (exp_ne_zero U)).mp hratio
  have hU : L * exp V = U := div_mul_cancel₀ _ (exp_ne_zero V)
  have hsecond : -L * exp U = V := by
    change -(U / exp V) * exp U = V
    field_simp [exp_ne_zero]
    rw [hmul]
    dsimp [U]
    ring
  exact ⟨(fixed_iff _ _ _).mpr ⟨by rw [hU], by rw [hsecond]⟩,
    Prod.ext hU hsecond, mul_div_cancel_right₀ τ hV, hdiff⟩

/-- A principal-sheet realization for every point of the open upper half-plane. -/
theorem upper_half_plane (τ : ℂ) (h : 0 < τ.im) :
    ∃ L U V : ℂ, step L (exp U, exp V) = (exp U, exp V) ∧
      lifts L (exp U, exp V) = (U,V) ∧ U / V = τ ∧ V - U = log (-τ) := by
  have h0 : τ ≠ 0 := by rintro rfl; simp at h
  have h1 : τ ≠ 1 := by rintro rfl; simp at h
  have he := exp_log (neg_ne_zero.mpr h0)
  have hd : log (-τ) ≠ 0 := by
    intro z
    rw [z, exp_zero] at he
    have hi := congrArg Complex.im he
    simp at hi
    simp [hi] at h
  exact ⟨_, _, _, from_log_sheet h1 hd he⟩

/-- Starting with an actual fixed pair recovers the same U,V,L from (U/V,V-U). -/
theorem recover_fixed_pair {L P Q : ℂ} (h : step L (P,Q) = (P,Q))
    (hV : -L * P ≠ 0) (hτ : L * Q / (-L * P) ≠ 1) :
    let U := L * Q
    let V := -L * P
    let τ := U / V
    let d := V - U
    exp d = -τ ∧ d / (1 - τ) = V ∧ τ * (d / (1 - τ)) = U ∧ U / exp V = L := by
  obtain ⟨hp, hq⟩ := (fixed_iff _ _ _).mp h
  have hp0 : P ≠ 0 := hp.trans_ne (exp_ne_zero _)
  have hq0 : Q ≠ 0 := hq.trans_ne (exp_ne_zero _)
  have hL0 : L ≠ 0 := by
    intro hz
    simp [hz] at hV
  let U := L * Q
  let V := -L * P
  change exp (V - U) = -(U/V) ∧ (V-U)/(1-U/V) = V ∧
    U/V*((V-U)/(1-U/V)) = U ∧ U / exp V = L
  have hmul : U/V * V = U := div_mul_cancel₀ _ hV
  have hrec : (V-U)/(1-U/V) = V := by
    apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm hτ))).mpr
    rw [mul_sub, mul_one, mul_comm V (U/V), hmul]
  refine ⟨?_, hrec, by rw [hrec, hmul], ?_⟩
  · rw [exp_sub, ← hq, ← hp]
    apply (div_eq_iff hp0).mpr
    dsimp [U,V]
    field_simp [hL0, hp0]
    ring
  · rw [← hq]
    exact mul_div_cancel_right₀ _ hq0

/-- At a fixed pair with Gaussian ratio, a marked lattice generator has
coordinates m+n i when divided by the second actual exponent. -/
theorem gaussian_generator_reading {L P Q : ℂ}
    (hV : -L * P ≠ 0) (hτ : L * Q / (-L * P) = I) (m n : ℤ) :
    ((m : ℂ)*(-L*P)+(n : ℂ)*(L*Q))/(-L*P) = m+n*I := by
  rw [add_div, mul_div_cancel_right₀ _ hV, mul_div_assoc, hτ]

end SuperZeta.DedekindPhase
