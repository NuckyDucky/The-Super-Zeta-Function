import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Nat.Choose.Basic

/-! Scalar evaluation blocks for fixed Frobenius interpolation minors. -/

namespace AlpogeSuperZeta

open Finset Matrix

/-- The coefficient of `T^order` in `(x + T)^degree`. -/
def monomialJet {R : Type*} [CommRing R] (degree order : ℕ) (x : R) : R :=
  (degree.choose order : R) * x ^ (degree - order)

/-- Repeated nodes `0,0,0,1,1,1,...,4,4` in the Newton order. -/
def scalarJetScaffold (R : Type*) [CommRing R] : Matrix (Fin 14) (Fin 14) R :=
  fun r c => monomialJet r.val (c.val % 3) (Nat.cast (c.val / 3) : R)

private def newtonCoefficients : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
    let previous := newtonCoefficients n
    (0 :: previous).zipWith (· - ·)
      ((previous.map fun a => (Int.ofNat (n / 3)) * a) ++ [0])

private def newtonChange : Matrix (Fin 14) (Fin 14) ℤ :=
  fun r c => (newtonCoefficients r.val)[c.val]?.getD 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1200000 in
private theorem newton_change_verified :
    (∀ r c : Fin 14, (if r.val < c.val then newtonChange r c else 0) = 0) ∧
      ∀ r : Fin 14, newtonChange r r = 1 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem newton_jet_verified :
    (∀ r c : Fin 14, c < r → (newtonChange * scalarJetScaffold ℤ) r c = 0) ∧
      ∀ r : Fin 14, (newtonChange * scalarJetScaffold ℤ) r r =
        ((r.val / 3).factorial : ℤ) ^ 3 := by
  decide +kernel

private theorem scalarJetScaffold_int_det :
    (scalarJetScaffold ℤ).det = 986049380773527552 := by
  have hL : newtonChange.IsLowerTriangular := by
    intro r c h
    simpa only [if_pos (show r.val < c.val from h)] using newton_change_verified.1 r c
  have hU : (newtonChange * scalarJetScaffold ℤ).IsUpperTriangular := newton_jet_verified.1
  have hdet : newtonChange.det = 1 := by
    rw [det_of_isLowerTriangular _ hL]
    simp only [newton_change_verified.2, Finset.prod_const_one]
  calc
    _ = newtonChange.det * (scalarJetScaffold ℤ).det := by rw [hdet, one_mul]
    _ = (newtonChange * scalarJetScaffold ℤ).det := (det_mul _ _).symm
    _ = _ := by
      rw [det_of_isUpperTriangular hU]
      simp only [newton_jet_verified.2]
      decide +kernel

theorem scalarJetScaffold_det (R : Type*) [CommRing R] :
    (scalarJetScaffold R).det = 986049380773527552 := by
  have hmap : (Int.castRingHom R).mapMatrix (scalarJetScaffold ℤ) = scalarJetScaffold R := by
    ext r c
    change (Int.castRingHom R) (monomialJet r.val (c.val % 3) (Nat.cast (c.val / 3) : ℤ)) =
      monomialJet r.val (c.val % 3) (Nat.cast (c.val / 3) : R)
    simp only [monomialJet, map_mul, map_pow, map_natCast]
  rw [← hmap, ← RingHom.map_det, scalarJetScaffold_int_det]
  norm_num

/-- One value at each scalar node from zero through thirteen. -/
def scalarValueScaffold (R : Type*) [CommRing R] : Matrix (Fin 14) (Fin 14) R :=
  fun r c => (c.val : R) ^ r.val

theorem scalarValueScaffold_det (R : Type*) [CommRing R] :
    (scalarValueScaffold R).det = 792786697595796795607377086400871488552960000000000000 := by
  change (vandermonde (fun c : Fin 14 => (c.val : R)))ᵀ.det = _
  rw [det_transpose, det_vandermonde_id_eq_superFactorial]
  have h : Nat.superFactorial 13 = 792786697595796795607377086400871488552960000000000000 := by
    decide +kernel
  rw [h]
  norm_num

#print axioms scalarJetScaffold_det
#print axioms scalarValueScaffold_det

end AlpogeSuperZeta
