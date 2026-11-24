import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-! The integral Gaussian coordinate basis used in the field package. -/

namespace QuarticModel

open Module

private def gaussianCoordinates : GaussianInt ≃+ ℤ × ℤ where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv z := by cases z; rfl
  right_inv p := by cases p; rfl
  map_add' _ _ := rfl

noncomputable def gaussianIntegralBasis : Basis (Fin 2) ℤ GaussianInt :=
  (Basis.finTwoProd ℤ).map gaussianCoordinates.toIntLinearEquiv.symm

instance : Module.Free ℤ GaussianInt := Module.Free.of_basis gaussianIntegralBasis
instance : Module.Finite ℤ GaussianInt := Module.Finite.of_basis gaussianIntegralBasis

theorem gaussian_finiteQuotient (I : Ideal GaussianInt) (hI : I ≠ ⊥) :
    Finite (GaussianInt ⧸ I) :=
  Ring.HasFiniteQuotients.finiteQuotient hI

#print axioms gaussian_finiteQuotient

end QuarticModel
