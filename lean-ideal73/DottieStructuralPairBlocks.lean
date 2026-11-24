import DottieStructuralJacobi
import DottiePairedRows

/-! Reduce the same paired row blocks with structural recursion in the
character. The existing row integers remain the certificate targets. -/

namespace QuarticModel

open private pairedTerm positiveSign swapCoordinates positiveNorm from DottieSymmetricScore

private def applyPairedWeight (sign : ℤ) (weight : Unit → ℤ) : ℤ :=
  match sign with
  | .ofNat 0 => 0
  | .ofNat (n+1) => Int.ofNat (n+1) * weight ()
  | .negSucc n => Int.negSucc n * weight ()

private theorem applyPairedWeight_eq (sign : ℤ) (weight : Unit → ℤ) :
    applyPairedWeight sign weight = if sign = 0 then 0 else sign * weight () := by
  cases sign with
  | ofNat n =>
    cases n with
    | zero => simp [applyPairedWeight]
    | succ n =>
      have hn : Int.ofNat (n+1) ≠ 0 := by
        intro he
        change Int.ofNat (n+1) = Int.ofNat 0 at he
        exact Nat.succ_ne_zero n (Int.ofNat.inj he)
      rw [if_neg hn]
      rfl
  | negSucc n => simp [applyPairedWeight]

private def pairTermWithSign (signAt : ℤ → ℤ → ℤ) (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  let sign := signAt ((a : ℤ)+1) ((b : ℤ)+1) + signAt ((b : ℤ)+1) ((a : ℤ)+1)
  applyPairedWeight sign (fun () => f ((a+1)^2+(b+1)^2))

def dottiePairRowBlockWithSign (signAt : ℤ → ℤ → ℤ) (f : ℕ → ℤ) (a lo len : ℕ) : ℤ :=
  (List.range len).foldl (fun s j => s + pairTermWithSign signAt f a (lo+j)) 0

theorem dottie_pair_row_block_with_sign_eq (signAt : ℤ → ℤ → ℤ)
    (h : ∀ x y, signAt x y = dottieRowSign x y) (f : ℕ → ℤ) (a lo len : ℕ) :
    dottiePairRowBlockWithSign signAt f a lo len = dottiePairRowBlock f a lo len := by
  simp only [dottiePairRowBlockWithSign, dottiePairRowBlock, pairTermWithSign,
    applyPairedWeight_eq, h, pairedTerm, positiveSign, swapCoordinates, positiveNorm]
  rfl

#print axioms dottie_pair_row_block_with_sign_eq

end QuarticModel
