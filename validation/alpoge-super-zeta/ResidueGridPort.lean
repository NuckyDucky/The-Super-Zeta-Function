import OrdinaryInteractions

namespace AlpogeSuperZeta

open Complex HurwitzZeta Filter Set
open scoped Topology BigOperators

noncomputable section

/-- A single translated reference reading in the ordinary doubled
coordinate, scaled by the modulus. -/
def residueMode {N : ℕ} [NeZero N] (a : ZMod N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (-(2 * s)) * hurwitzZeta (ZMod.toAddCircle a) (2 * s)

def residueReading {N : ℕ} [NeZero N] (weights : ZMod N → ℂ) (s : ℂ) : ℂ :=
  ∑ a : ZMod N, weights a * residueMode a s

theorem residue_read_eq_LFunction {N : ℕ} [NeZero N] (weights : ZMod N → ℂ) (s : ℂ) :
    residueReading weights s = ZMod.LFunction weights (2 * s) := by
  rw [residueReading, ZMod.LFunction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold residueMode
  ring

/-- The original corrected Super Zeta is the odd residue reading. -/
theorem corrected_eq_mod_two_residue {s : ℂ} (hp : 2 * s ≠ 1) :
    corrected s = 2 * (Real.pi : ℂ) ^ (-(2 * s)) * (2 : ℂ) ^ (2 * s) *
      residueReading (fun a : ZMod 2 => (1 : DirichletCharacter ℂ 2) a) s := by
  rw [corrected_eq_triv_char_two hp, residue_read_eq_LFunction]
  rfl

/-- The residue of a weighted spectral reading at the pulled-back pole
is half the average weight. -/
theorem residue_read_at_half {N : ℕ} [NeZero N] (weights : ZMod N → ℂ) :
    Tendsto (fun s : ℂ => (s - 1 / 2) * residueReading weights s)
      (𝓝[≠] (1 / 2)) (𝓝 ((∑ a : ZMod N, weights a / (N : ℂ)) / 2)) := by
  have h : ContinuousWithinAt (fun s : ℂ => 2 * s) {1 / 2}ᶜ (1 / 2) :=
    (continuous_const.mul continuous_id).continuousWithinAt
  have scale : Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (1 / 2)) (𝓝[≠] 1) := by
    convert h.tendsto_nhdsWithin (s := {1 / 2}ᶜ) (t := {1}ᶜ) (by
      intro x hx
      simp only [mem_compl_iff, mem_singleton_iff] at hx ⊢
      intro hx'
      exact hx (by linear_combination hx' / 2)) using 1
    norm_num
  have hL := ((ZMod.LFunction_residue_one weights).comp scale).div_const (2 : ℂ)
  refine hL.congr' (Eventually.of_forall ?_)
  intro s
  simp only [Function.comp_apply, residue_read_eq_LFunction]
  ring

/-- Zero sum of the weights cancels the common Hurwitz pole entirely. -/
theorem zero_sum_residue_read_entire {N : ℕ} [NeZero N] {weights : ZMod N → ℂ}
    (h₀ : ∑ a : ZMod N, weights a = 0) : Differentiable ℂ (residueReading weights) := by
  rw [show residueReading weights = ZMod.LFunction weights ∘ (fun s : ℂ => 2 * s)
    from funext (residue_read_eq_LFunction weights)]
  exact (ZMod.differentiable_LFunction_of_sum_zero h₀).comp (by fun_prop)

theorem nontrivial_character_read_entire {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (residueReading fun a : ZMod N => χ a) :=
  zero_sum_residue_read_entire (χ.sum_eq_zero_of_ne_one hχ)

/-- Apply the exact published character-zero statement after the
residue reading has been identified with the corresponding L-function. -/
theorem character_read_zero_on_quarter_line (hD : DirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2)
    (hz : residueReading (fun a : ZMod N => χ a) s = 0) : s.re = 1 / 4 := by
  have hr : (2 * s).re = 2 * s.re := by simp [Complex.mul_re]
  rw [residue_read_eq_LFunction] at hz
  have h := hD N χ (2 * s) (by linarith) (by linarith) hz
  linarith

#print axioms residue_read_eq_LFunction
#print axioms corrected_eq_mod_two_residue
#print axioms residue_read_at_half
#print axioms zero_sum_residue_read_entire
#print axioms nontrivial_character_read_entire
#print axioms character_read_zero_on_quarter_line

end
end AlpogeSuperZeta
