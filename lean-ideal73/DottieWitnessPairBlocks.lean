import DottieLargeSignWitness
import DottieStructuralPairBlocks

/-! Recompute a paired block using independently checked witnesses at the
largest conductor prime and the certified masks at the two small primes. -/

namespace QuarticModel

open private residueSign mask41 mask457 structuralJacobi structuralJacobi_eq
  from DottieStructuralJacobi
open private fastJacobiSym.eq from Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
open private applyPairedWeight pairTermWithSign from DottieStructuralPairBlocks

private def smallSignProduct (a b : ℕ) : ℤ :=
  residueSign mask41 (((a : ℤ) + (b : ℤ)*32)%41).natAbs *
    residueSign mask457 (((a : ℤ) + (b : ℤ)*109)%457).natAbs

private def witnessedRowSign (a b code : ℕ) : Option ℤ :=
  let small := smallSignProduct a b
  if small = 0 then some 0 else
    (dottieLargeSignWitness (a+b*516876951) code).map (small * ·)

private theorem witnessedRowSign_correct {a b code : ℕ} {s : ℤ}
    (h : witnessedRowSign a b code = some s) :
    dottieRowSign a b = s := by
  rw [← dottieLookupRowSign_eq, dottieLookupRowSign]
  change (if smallSignProduct a b = 0 then _ else _) = s
  by_cases hz : smallSignProduct a b = 0
  · rw [witnessedRowSign, if_pos hz] at h
    cases h
    rw [if_pos hz]
  · rw [if_neg hz]
    rw [witnessedRowSign, if_neg hz] at h
    cases he : dottieLargeSignWitness (a+b*516876951) code with
    | none => simp [he] at h
    | some big =>
      rw [he] at h
      have hs : smallSignProduct a b * big = s := Option.some.inj h
      rw [structuralJacobi_eq _ 1414835497 (by decide) (by decide), ← fastJacobiSym.eq]
      have hb := dottie_large_sign_of_witness he
      push_cast at hb
      rw [hb]
      exact hs

private def witnessedFold (f : ℕ → ℤ) (a : ℕ) :
    List (ℕ × ℕ) → ℕ → ℤ → Option ℤ
  | [], _, total => some total
  | (x,y)::codes, b, total => do
    let s ← witnessedRowSign (a+1) (b+1) x
    let t ← witnessedRowSign (b+1) (a+1) y
    let term := applyPairedWeight (s+t) (fun () => f ((a+1)^2+(b+1)^2))
    witnessedFold f a codes (b+1) (total+term)

def dottieWitnessPairBlock (f : ℕ → ℤ) (a lo : ℕ) (codes : List (ℕ × ℕ)) : Option ℤ :=
  witnessedFold f a codes lo 0

private theorem single_pair_term (f : ℕ → ℤ) (a b : ℕ) :
    dottiePairRowBlock f a b 1 =
      applyPairedWeight (dottieRowSign (↑(a+1) : ℤ) (↑(b+1) : ℤ) +
        dottieRowSign (↑(b+1) : ℤ) (↑(a+1) : ℤ)) (fun () => f ((a+1)^2+(b+1)^2)) := by
  rw [← dottie_pair_row_block_with_sign_eq dottieRowSign (fun _ _ => rfl)]
  simp [dottiePairRowBlockWithSign, pairTermWithSign]

private theorem witnessedFold_correct (f : ℕ → ℤ) (a : ℕ) (codes : List (ℕ × ℕ))
    {b : ℕ} {total target : ℤ} (h : witnessedFold f a codes b total = some target) :
    total + dottiePairRowBlock f a b codes.length = target := by
  induction codes generalizing b total target with
  | nil =>
    have ht := Option.some.inj h
    simpa [dottiePairRowBlock] using ht
  | cons code codes ih =>
    obtain ⟨x,y⟩ := code
    rw [witnessedFold] at h
    cases hs : witnessedRowSign (a+1) (b+1) x with
    | none => simp [hs] at h
    | some s =>
      cases ht : witnessedRowSign (b+1) (a+1) y with
      | none => simp [hs, ht] at h
      | some t =>
        simp only [hs, ht] at h
        have he := ih h
        rw [← witnessedRowSign_correct hs, ← witnessedRowSign_correct ht,
          ← single_pair_term] at he
        rw [List.length_cons, Nat.add_comm codes.length 1, dottiePairRowBlock_add, ← add_assoc]
        exact he

theorem dottie_pair_block_of_witness {f : ℕ → ℤ} {a lo len : ℕ}
    {codes : List (ℕ × ℕ)} {target : ℤ}
    (hlen : codes.length = len) (h : dottieWitnessPairBlock f a lo codes = some target) :
    dottiePairRowBlock f a lo len = target := by
  simpa only [zero_add, hlen] using witnessedFold_correct f a codes h

private def witnessWordBase : ℕ := 4294967296

private def unpackWitnessPairs : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | len+1, packed =>
    let next := packed / witnessWordBase
    (packed % witnessWordBase, next % witnessWordBase) ::
      unpackWitnessPairs len (next / witnessWordBase)

private theorem unpackWitnessPairs_length (len packed : ℕ) :
    (unpackWitnessPairs len packed).length = len := by
  induction len generalizing packed with
  | zero => rfl
  | succ len ih => simp [unpackWitnessPairs, ih]

def dottiePackedWitnessPairBlock (f : ℕ → ℤ) (a lo len packed : ℕ) : Option ℤ :=
  dottieWitnessPairBlock f a lo (unpackWitnessPairs len packed)

theorem dottie_pair_block_of_packed_witness {f : ℕ → ℤ} {a lo len packed : ℕ} {target : ℤ}
    (h : dottiePackedWitnessPairBlock f a lo len packed = some target) :
    dottiePairRowBlock f a lo len = target :=
  dottie_pair_block_of_witness (unpackWitnessPairs_length len packed) h

#print axioms dottie_pair_block_of_witness
#print axioms dottie_pair_block_of_packed_witness

end QuarticModel
