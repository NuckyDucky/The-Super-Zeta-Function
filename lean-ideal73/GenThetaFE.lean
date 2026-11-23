/- Adapted from DrMurphyIsIn/real-dirichlet-dbn-lean v1.0.0, Apache-2.0.
   See murphy-gauss/LICENSE and murphy-gauss/UPSTREAM-NOTICE.md.
   The version-specific changes specialize the dependency chain to the odd conductor. -/

import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
open Real Complex
namespace DBN.Gen
variable {N : ℕ} [NeZero N]
/-- **Step B.** Splitting a two-sided sum into residue classes mod `N`. -/
theorem hasSum_residue {f : ℤ → ℂ} {a : ℂ} (ha : HasSum f a) {g : Fin N → ℂ}
    (hg : ∀ j : Fin N, HasSum (fun m : ℤ ↦ f (m * N + j)) (g j)) : a = ∑ j, g j := by
  set e : Fin N × ℤ ≃ ℤ := (Equiv.prodComm (Fin N) ℤ).trans (Int.divModEquiv N).symm with he
  have h1 : HasSum (f ∘ e) a := e.hasSum_iff.mpr ha
  have h2 : HasSum g a := h1.prod_fiberwise fun j ↦ by
    simpa [he, Function.comp_def] using hg j
  exact h2.unique (hasSum_fintype g)

/-- `j ↦ (j : ZMod N)` is a bijection `Fin N → ZMod N`. -/
theorem bijective_fin_cast : Function.Bijective (fun j : Fin N ↦ ((j : ℕ) : ZMod N)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b hab ↦ ?_, by simp⟩
  have h := congrArg ZMod.val hab
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h
  exact Fin.ext h

omit [NeZero N] in
theorem natCast_cpow_half : (N : ℂ) ^ (1 / 2 : ℂ) = (((N : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [ofReal_cpow (Nat.cast_nonneg _)]; push_cast; rfl
end DBN.Gen
