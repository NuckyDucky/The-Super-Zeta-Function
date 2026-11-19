import SuperZeta.Oriented.LiuConnection
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace DottieOriented.FifthReference

open Complex HurwitzZeta DirichletCharacter
open DottieOriented.LiuConnection

noncomputable section

private instance prime_five : Fact (Nat.Prime 5) := ⟨by decide⟩

def legendreTable (j : ZMod 5) : ℤ :=
  if j = 0 then 0 else if j = 1 ∨ j = 4 then 1 else -1

/-- The quadratic Dirichlet character modulo five, specified by its finite table. -/
def chi5 : DirichletCharacter ℂ 5 where
  toFun j := (legendreTable j : ℂ)
  map_one' := by norm_num [legendreTable]
  map_mul' a b := by
    have h : ∀ i j : ZMod 5, legendreTable (i*j) = legendreTable i * legendreTable j := by decide
    rw [h, Int.cast_mul]
  map_nonunit' a ha := by
    have hz : a = 0 := by simpa only [isUnit_iff_ne_zero, not_ne_iff] using ha
    simp [hz, legendreTable]

private theorem principal (j : ZMod 5) : (1 : DirichletCharacter ℂ 5) j = if j=0 then 0 else 1 := by
  by_cases h : j=0
  · subst j
    rw [if_pos rfl]
    exact MulChar.map_nonunit _ (by simp)
  · rw [if_neg h, MulChar.one_apply (isUnit_iff_ne_zero.mpr h)]

private theorem split_weight (j : ZMod 5) :
    (1 : DirichletCharacter ℂ 5) j + chi5 j =
       (if j=1 then 2 else 0) + (if j=4 then 2 else 0) := by
  rw [principal]
  change (if j=0 then 0 else 1) + (legendreTable j : ℂ) = _
  have hz1 : (0:ZMod 5) ≠ 1 := by decide
  have hz4 : (0:ZMod 5) ≠ 4 := by decide
  have h14 : (1:ZMod 5) ≠ 4 := by decide
  by_cases a : j=0
  · subst j; simp [legendreTable, hz4]
  by_cases b : j=1
  · subst j; norm_num [legendreTable, h14]
  by_cases c : j=4
  · subst j; norm_num [legendreTable, b, a]
  simp [legendreTable, a, b, c]

private theorem sum_split (H : ZMod 5 → ℂ) :
    (∑ j : ZMod 5, ((1 : DirichletCharacter ℂ 5) j * H j + chi5 j * H j)) =
      2 * H 1 + 2 * H 4 := by
  simp_rw [← add_mul, split_weight, add_mul, ite_mul, zero_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem fifth_reference {w : ℂ} (hw : w ≠ 1) :
    reference (1/5 : ℝ) w = (Real.pi:ℂ)^(-w) * (5:ℂ)^w / 2 *
      ((1-(5:ℂ)^(-w))*riemannZeta w + chi5.LFunction w) := by
  have hs : (1-(5:ℂ)^(-w))*riemannZeta w = (1 : DirichletCharacter ℂ 5).LFunction w := by
    simpa [Nat.Prime.primeFactors (by decide : Nat.Prime 5)] using
      (LFunctionTrivChar_eq_mul_riemannZeta (N:=5) hw).symm
  rw [hs]
  simp only [DirichletCharacter.LFunction, ZMod.LFunction]
  rw [← mul_add, ← Finset.sum_add_distrib, sum_split]
  have one : ZMod.toAddCircle (1 : ZMod 5) = ((1/5 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply, show (1:ZMod 5).val = 1 by decide]
    norm_num
  have four : ZMod.toAddCircle (4 : ZMod 5) = ((4/5 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply]; rfl
  rw [one, four, reference, show (1-1/5 : ℝ) = 4/5 by norm_num]
  norm_num only [Nat.cast_ofNat]
  rw [cpow_neg (5:ℂ)]
  have h5 : (5:ℂ)^w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  field_simp [h5]
  ring

/-- At a Riemann zero, the fifths reference vanishes exactly when the quadratic
Dirichlet L-function also vanishes there. -/
theorem fifth_at_riemann_zero {w : ℂ} (hw : w ≠ 1) (hz : riemannZeta w = 0) :
    reference (1/5 : ℝ) w = 0 ↔ chi5.LFunction w = 0 := by
  rw [fifth_reference hw, hz, mul_zero, zero_add, mul_eq_zero]
  have hπ : (Real.pi:ℂ)^(-w) ≠ 0 := cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h5 : (5:ℂ)^w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  simp [div_ne_zero (mul_ne_zero hπ h5) (by norm_num : (2:ℂ) ≠ 0)]

end
end DottieOriented.FifthReference

