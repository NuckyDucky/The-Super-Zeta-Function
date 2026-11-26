import GaussianFrobeniusJetScaffold
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic

/-! A fixed interpolation matrix for the identity and central Frobenius labels.
Its rows are the thirteen positive powers of X, the constant, and Y.
The two nonrational nodes retain both the quartic radical and the Gaussian unit.
-/

namespace AlpogeSuperZeta

open QuadraticAlgebra Matrix

abbrev JetRealOrder (R : Type*) [CommRing R] :=
  QuadraticAlgebra R 26509772707289 0

def jetQuarticRadicand (R : Type*) [CommRing R] : JetRealOrder R :=
  2 * (-5045155 + ω)

abbrev JetQuarticOrder (R : Type*) [CommRing R] :=
  QuadraticAlgebra (JetRealOrder R) (jetQuarticRadicand R) 0

abbrev JetGaussianOrder (R : Type*) [CommRing R] :=
  QuadraticAlgebra (JetQuarticOrder R) (-1) 0

def jetBeta (R : Type*) [CommRing R] : JetGaussianOrder R :=
  algebraMap (JetQuarticOrder R) (JetGaussianOrder R) ω

def jetI (R : Type*) [CommRing R] : JetGaussianOrder R := ω

abbrev JetRows := Fin 14 ⊕ Unit
abbrev JetColumns := (Fin 14 ⊕ Bool) × Fin 3

private def jetNode (R : Type*) [CommRing R] (negateBeta : Bool) :
    Fin 14 ⊕ Bool → JetGaussianOrder R
  | .inl c => (c.val : JetGaussianOrder R)
  | .inr false => if negateBeta then -jetBeta R else jetBeta R
  | .inr true => jetI R

/-- The first graph coordinate is the node. The second applies the chosen
label, which fixes the Gaussian unit in both cases. -/
def archivedJetMatrix (R : Type*) [CommRing R] (central : Bool) :
    Matrix JetRows JetColumns (JetGaussianOrder R)
  | .inl r, (c, j) => monomialJet r.val j.val (jetNode R false c)
  | .inr _, (c, j) => if j.val = 0 then jetNode R central c else 0

def archivedJetMinor (R : Type*) [CommRing R] (central : Bool) (cols : JetRows → JetColumns) :
    Matrix JetRows JetRows (JetGaussianOrder R) :=
  fun r c => archivedJetMatrix R central r (cols c)

private def tripleColumns (probe : Bool) : JetRows → JetColumns
  | .inl c => (.inl ⟨c.val / 3, by omega⟩, ⟨c.val % 3, by omega⟩)
  | .inr _ => (.inr probe, 0)

private def valueColumns : JetRows → JetColumns
  | .inl c => (.inl c, 0)
  | .inr _ => (.inl 0, 1)

private theorem tripleColumns_injective (probe : Bool) : Function.Injective (tripleColumns probe) := by
  cases probe <;> decide +kernel

private theorem valueColumns_injective : Function.Injective valueColumns := by
  decide +kernel

private theorem determinant_with_last_row_subtracted {R : Type*} [CommRing R]
    (A : Matrix JetRows JetRows R) (r : Fin 14)
    (h : ∀ c : Fin 14, A (.inr ()) (.inl c) = A (.inl r) (.inl c)) :
    A.det = (Matrix.of fun i j : Fin 14 => A (.inl i) (.inl j)).det *
      (A (.inr ()) (.inr ()) - A (.inl r) (.inr ())) := by
  let B : Matrix JetRows JetRows R := updateRow A (.inr ()) (A (.inr ()) + (-1 : R) • A (.inl r))
  have hdet : B.det = A.det :=
    det_updateRow_add_smul_self A (show (Sum.inr () : JetRows) ≠ Sum.inl r from Sum.inr_ne_inl) (-1)
  let upperLeft : Matrix (Fin 14) (Fin 14) R := .of fun i j => A (.inl i) (.inl j)
  let upperRight : Matrix (Fin 14) Unit R := .of fun i _ => A (.inl i) (.inr ())
  let lowerRight : Matrix Unit Unit R := .of fun _ _ =>
    A (.inr ()) (.inr ()) - A (.inl r) (.inr ())
  have hB : B = fromBlocks upperLeft upperRight 0 lowerRight := by
    ext i j
    cases i with
    | inl i =>
      change updateRow A (.inr ()) _ (.inl i) j = _
      rw [updateRow_ne (by simp : (Sum.inl i : JetRows) ≠ Sum.inr ())]
      cases j <;> rfl
    | inr i =>
      cases i
      change updateRow A (.inr ()) _ (.inr ()) j = _
      rw [updateRow_self]
      cases j with
      | inl j =>
        change A (.inr ()) (.inl j) + (-1 : R) * A (.inl r) (.inl j) = 0
        rw [h j]
        ring
      | inr j =>
        cases j
        change A (.inr ()) (.inr ()) + (-1 : R) * A (.inl r) (.inr ()) =
          A (.inr ()) (.inr ()) - A (.inl r) (.inr ())
        ring
  calc
    A.det = B.det := hdet.symm
    _ = (fromBlocks upperLeft upperRight 0 lowerRight).det := congrArg Matrix.det hB
    _ = upperLeft.det * lowerRight.det := det_fromBlocks_zero₂₁ upperLeft upperRight lowerRight
    _ = _ := by rw [det_unique lowerRight]; rfl

private theorem noMinor_if_equal_rows {R : Type*} [CommRing R] (central : Bool) (r : Fin 14)
    (h : ∀ c, archivedJetMatrix R central (.inr ()) c = archivedJetMatrix R central (.inl r) c) :
    ∀ cols, (archivedJetMinor R central cols).det = 0 := by
  intro cols
  apply det_zero_of_row_eq (i := Sum.inr ()) (j := Sum.inl r) Sum.inr_ne_inl
  funext c
  exact h (cols c)

private theorem tripleMinor_det {R : Type*} [CommRing R] (central probe : Bool) (r : Fin 14)
    (hrow : ∀ c : Fin 14,
      archivedJetMatrix R central (.inr ()) (tripleColumns probe (.inl c)) =
        archivedJetMatrix R central (.inl r) (tripleColumns probe (.inl c))) :
    (archivedJetMinor R central (tripleColumns probe)).det =
      986049380773527552 * (jetNode R central (.inr probe) - jetNode R false (.inr probe) ^ r.val) := by
  rw [determinant_with_last_row_subtracted _ r hrow]
  have hleft : (Matrix.of fun i j : Fin 14 =>
      archivedJetMinor R central (tripleColumns probe) (.inl i) (.inl j)) =
      scalarJetScaffold (JetGaussianOrder R) := rfl
  have hlast : archivedJetMinor R central (tripleColumns probe) (.inr ()) (.inr ()) -
      archivedJetMinor R central (tripleColumns probe) (.inl r) (.inr ()) =
      jetNode R central (.inr probe) - jetNode R false (.inr probe) ^ r.val := by
    change jetNode R central (.inr probe) - monomialJet r.val 0 (jetNode R false (.inr probe)) = _
    simp [monomialJet]
  rw [hleft, scalarJetScaffold_det, hlast]

private theorem valueMinor_det (R : Type*) [CommRing R] (central : Bool) :
    (archivedJetMinor R central valueColumns).det =
      -(792786697595796795607377086400871488552960000000000000 : JetGaussianOrder R) := by
  have hrow : ∀ c : Fin 14, archivedJetMatrix R central (.inr ()) (valueColumns (.inl c)) =
      archivedJetMatrix R central (.inl ⟨1, by decide⟩) (valueColumns (.inl c)) := by
    intro c
    simp [archivedJetMatrix, monomialJet, valueColumns, jetNode]
  rw [determinant_with_last_row_subtracted _ ⟨1, by decide⟩ hrow]
  have hleft : (Matrix.of fun i j : Fin 14 => archivedJetMinor R central valueColumns (.inl i) (.inl j)) =
      scalarValueScaffold (JetGaussianOrder R) := by
    funext i j
    simp [scalarValueScaffold, archivedJetMinor, archivedJetMatrix, valueColumns, jetNode, monomialJet]
  rw [hleft, scalarValueScaffold_det]
  simp [archivedJetMinor, archivedJetMatrix, valueColumns, monomialJet]

def HasUnitJetMinor (R : Type*) [CommRing R] (central : Bool) : Prop :=
  ∃ cols : JetRows → JetColumns, Function.Injective cols ∧ IsUnit (archivedJetMinor R central cols).det

set_option maxRecDepth 20000 in
theorem archivedJetMinor_5 :
    (∀ cols, (archivedJetMinor (ZMod 5) false cols).det = 0) ∧ HasUnitJetMinor (ZMod 5) true := by
  constructor
  · apply noMinor_if_equal_rows _ ⟨5, by decide⟩
    decide +kernel
  · refine ⟨tripleColumns false, tripleColumns_injective false, ?_⟩
    rw [tripleMinor_det _ _ ⟨5, by decide⟩ (by decide +kernel)]
    apply IsUnit.of_mul_eq_one (jetBeta (ZMod 5) ^ 3)
    decide +kernel

set_option maxRecDepth 20000 in
theorem archivedJetMinor_7 (central : Bool) : HasUnitJetMinor (ZMod 7) central := by
  cases central <;>
    refine ⟨tripleColumns true, tripleColumns_injective true, ?_⟩ <;>
    rw [tripleMinor_det _ _ ⟨7, by decide⟩ (by decide +kernel)] <;>
    apply IsUnit.of_mul_eq_one (4 * jetI (ZMod 7)) <;> decide +kernel

set_option maxRecDepth 20000 in
theorem archivedJetMinor_13 :
    HasUnitJetMinor (ZMod 13) false ∧ (∀ cols, (archivedJetMinor (ZMod 13) true cols).det = 0) := by
  constructor
  · refine ⟨tripleColumns false, tripleColumns_injective false, ?_⟩
    rw [tripleMinor_det _ _ ⟨13, by decide⟩ (by decide +kernel)]
    apply IsUnit.of_mul_eq_one (6 * jetBeta (ZMod 13) ^ 11)
    decide +kernel
  · apply noMinor_if_equal_rows _ ⟨13, by decide⟩
    decide +kernel

theorem archivedJetMinor_61 (central : Bool) : HasUnitJetMinor (ZMod 61) central := by
  refine ⟨valueColumns, valueColumns_injective, ?_⟩
  rw [valueMinor_det]
  apply IsUnit.of_mul_eq_one (-41)
  decide +kernel

theorem archivedJetMinor_73 (central : Bool) : HasUnitJetMinor (ZMod 73) central := by
  refine ⟨valueColumns, valueColumns_injective, ?_⟩
  rw [valueMinor_det]
  apply IsUnit.of_mul_eq_one (-70)
  decide +kernel

#print axioms archivedJetMinor_5
#print axioms archivedJetMinor_7
#print axioms archivedJetMinor_13
#print axioms archivedJetMinor_61
#print axioms archivedJetMinor_73

end AlpogeSuperZeta
