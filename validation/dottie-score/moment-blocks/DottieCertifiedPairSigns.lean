import DottieWitnessPairBlocks

/-! Certify the paired Gaussian signs once and reuse them with any integer weight. -/

namespace QuarticModel

open private witnessedRowSign witnessedRowSign_correct single_pair_term
  unpackWitnessPairs unpackWitnessPairs_length from DottieWitnessPairBlocks
open private applyPairedWeight from DottieStructuralPairBlocks

set_option autoImplicit false

private def signRadix : ℕ := 8

private def readPairSign (packed : ℕ) : ℤ :=
  ((packed % signRadix : ℕ) : ℤ) - 2

private def verifyPairSigns (a : ℕ) : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], _, packed => packed == 0
  | (x, y) :: codes, b, packed =>
    match witnessedRowSign (a+1) (b+1) x, witnessedRowSign (b+1) (a+1) y with
    | some s, some t =>
      if s+t = readPairSign packed then verifyPairSigns a codes (b+1) (packed/signRadix)
      else false
    | _, _ => false

/-- Check the compact signs against the two conductor witnesses in each pair. -/
def dottiePackedPairSignsCheck (a lo len witnesses signs : ℕ) : Bool :=
  verifyPairSigns a (unpackWitnessPairs len witnesses) lo signs

private def foldPairSigns (f : ℕ → ℤ) (a : ℕ) : ℕ → ℕ → ℕ → ℤ → ℤ
  | 0, _, _, total => total
  | len+1, b, packed, total =>
    let term := applyPairedWeight (readPairSign packed) (fun () => f ((a+1)^2+(b+1)^2))
    foldPairSigns f a len (b+1) (packed/signRadix) (total+term)

/-- Evaluate a weight on the checked signs, given one three-bit digit per pair. -/
def dottiePackedPairSignBlock (f : ℕ → ℤ) (a lo len signs : ℕ) : ℤ :=
  foldPairSigns f a len lo signs 0

private theorem foldPairSigns_correct (f : ℕ → ℤ) (a : ℕ) (codes : List (ℕ × ℕ))
    {b packed : ℕ} (total : ℤ) (h : verifyPairSigns a codes b packed = true) :
    foldPairSigns f a codes.length b packed total =
      total + dottiePairRowBlock f a b codes.length := by
  induction codes generalizing b packed total with
  | nil => simp [foldPairSigns, dottiePairRowBlock]
  | cons code codes ih =>
    obtain ⟨x, y⟩ := code
    cases hs : witnessedRowSign (a+1) (b+1) x with
    | none => simp [verifyPairSigns, hs] at h
    | some s =>
      cases ht : witnessedRowSign (b+1) (a+1) y with
      | none => simp [verifyPairSigns, hs, ht] at h
      | some t =>
        have hCheck : s+t = readPairSign packed ∧
            verifyPairSigns a codes (b+1) (packed/signRadix) = true := by
          simpa [verifyPairSigns, hs, ht] using h
        have hTerm : applyPairedWeight (readPairSign packed)
            (fun () => f ((a+1)^2+(b+1)^2)) = dottiePairRowBlock f a b 1 := by
          rw [← hCheck.1, ← witnessedRowSign_correct hs, ← witnessedRowSign_correct ht]
          exact (single_pair_term f a b).symm
        rw [List.length_cons, foldPairSigns, hTerm, ih _ hCheck.2, add_assoc]
        rw [← dottiePairRowBlock_add, Nat.add_comm 1 codes.length]

/-- A certified sign block gives the exact paired sum for every choice of weight. -/
theorem dottie_pair_block_eq_of_checked_signs {a lo len witnesses signs : ℕ}
    (h : dottiePackedPairSignsCheck a lo len witnesses signs = true) (f : ℕ → ℤ) :
    dottiePairRowBlock f a lo len = dottiePackedPairSignBlock f a lo len signs := by
  have he := foldPairSigns_correct f a (unpackWitnessPairs len witnesses) 0 h
  rw [unpackWitnessPairs_length, zero_add] at he
  exact he.symm

#print axioms dottie_pair_block_eq_of_checked_signs

end QuarticModel
