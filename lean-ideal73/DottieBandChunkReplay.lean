import DottieBandCoefficientChecks
import DottieBandFactorCheck
import DottieRetainedBandBounds

/-! Validate a contiguous list of signed coefficients and join its exact
prefix extrema with adjacent lists. The final bound is the integer input
to the retained contour estimate. -/

namespace QuarticModel

open Finset
set_option autoImplicit false

structure DottieBandSummary where
  total : ℤ
  lower : ℤ
  upper : ℤ
  deriving DecidableEq

def DottieBandSummary.empty : DottieBandSummary := ⟨0,0,0⟩

def DottieBandSummary.single (c : ℤ) : DottieBandSummary :=
  ⟨c,min 0 c,max 0 c⟩

def DottieBandSummary.append (x y : DottieBandSummary) : DottieBandSummary :=
  ⟨x.total+y.total,min x.lower (x.total+y.lower),max x.upper (x.total+y.upper)⟩

structure DottieBandChunk (a len : ℕ) (s : DottieBandSummary) : Prop where
  terminal : (∑ i ∈ range len, archivedLatticeCoeff (a+i)) = s.total
  bounded : ∀ k ≤ len, s.lower ≤ (∑ i ∈ range k, archivedLatticeCoeff (a+i)) ∧
    (∑ i ∈ range k, archivedLatticeCoeff (a+i)) ≤ s.upper

theorem dottie_band_empty_chunk (a : ℕ) : DottieBandChunk a 0 DottieBandSummary.empty := by
  constructor
  · simp [DottieBandSummary.empty]
  · intro k hk
    have he : k = 0 := by omega
    simp [he,DottieBandSummary.empty]

theorem dottie_band_single_chunk {a : ℕ} {c : ℤ} (h : archivedLatticeCoeff a = c) :
    DottieBandChunk a 1 (DottieBandSummary.single c) := by
  constructor
  · simp [DottieBandSummary.single,h]
  · intro k hk
    interval_cases k <;> simp [DottieBandSummary.single,h]

theorem dottie_band_append_chunks {a m n : ℕ} {x y : DottieBandSummary}
    (hx : DottieBandChunk a m x) (hy : DottieBandChunk (a+m) n y) :
    DottieBandChunk a (m+n) (x.append y) := by
  have hs (j : ℕ) : (∑ i ∈ range (m+j), archivedLatticeCoeff (a+i)) =
      x.total + ∑ i ∈ range j, archivedLatticeCoeff (a+m+i) := by
    rw [Finset.sum_range_add,hx.terminal]
    simp only [Nat.add_assoc]
  constructor
  · rw [hs,hy.terminal]
    rfl
  · intro k hk
    by_cases hkm : k ≤ m
    · obtain ⟨hl,hu⟩ := hx.bounded k hkm
      exact ⟨(min_le_left _ _).trans hl,hu.trans (le_max_left _ _)⟩
    · have hpart : k-m ≤ n := by omega
      obtain ⟨hl,hu⟩ := hy.bounded (k-m) hpart
      have hsplit : (∑ i ∈ range k, archivedLatticeCoeff (a+i)) =
          x.total + ∑ i ∈ range (k-m), archivedLatticeCoeff (a+m+i) := by
        simpa only [show m+(k-m) = k by omega] using hs (k-m)
      rw [hsplit]
      exact ⟨(min_le_right _ _).trans (add_le_add le_rfl hl),
        (add_le_add le_rfl hu).trans (le_max_right _ _)⟩

theorem dottie_band_integer_sums_of_chunk {a b : ℕ} {s : DottieBandSummary} {A M : ℤ}
    (h : DottieBandChunk a (b-a+1) s) (hl : -A ≤ s.lower) (hu : s.upper ≤ A)
    (ht : |s.total| ≤ M) : DottieBandIntegerSums a b A M := by
  refine ⟨?_,by simpa only [h.terminal] using ht⟩
  intro k hk
  obtain ⟨hlk,huk⟩ := h.bounded k (by omega)
  exact abs_le.mpr ⟨hl.trans hlk,huk.trans hu⟩

inductive DottieBandRow where
  | zero (twos divisor : ℕ) (signCode : Option ℕ)
  | factored (twos : ℕ) (factors : List DottieBandFactor) (value : ℤ)

def DottieBandRow.value : DottieBandRow → ℤ
  | .zero .. => 0
  | .factored _ _ c => c

def DottieBandRow.check (primeOk : ℕ → Bool) (n : ℕ) : DottieBandRow → Bool
  | .zero twos m signCode => dottieBandZeroCheck n twos m signCode
  | .factored twos factors value => dottieBandFactoredRowCheck primeOk n twos factors value

def dottieBandCheckRows (primeOk : ℕ → Bool) : ℕ → List DottieBandRow → Option DottieBandSummary
  | _, [] => some DottieBandSummary.empty
  | a, row::rows =>
    if row.check primeOk a then
      (dottieBandCheckRows primeOk (a+1) rows).map (DottieBandSummary.single row.value).append
    else none

theorem dottie_band_check_rows_sound {primeOk : ℕ → Bool}
    (hprime : ∀ p, primeOk p = true → p.Prime)
    {a : ℕ} {rows : List DottieBandRow} {s : DottieBandSummary}
    (h : dottieBandCheckRows primeOk a rows = some s) : DottieBandChunk a rows.length s := by
  induction rows generalizing a s with
  | nil =>
    have he : DottieBandSummary.empty = s := Option.some.inj h
    subst s
    exact dottie_band_empty_chunk a
  | cons row rows ih =>
    rw [dottieBandCheckRows] at h
    by_cases hcheck : row.check primeOk a = true
    · rw [if_pos hcheck] at h
      have hv : archivedLatticeCoeff a = row.value := by
        cases row with
        | zero twos m code => exact dottie_band_zero_check_sound hcheck
        | factored twos factors c => exact dottie_band_factored_row_check_sound hprime hcheck
      cases htail : dottieBandCheckRows primeOk (a+1) rows with
      | none => simp [htail] at h
      | some t =>
        rw [htail] at h
        have he : (DottieBandSummary.single row.value).append t = s := Option.some.inj h
        subst s
        simpa only [List.length_cons,Nat.add_comm rows.length 1] using
          dottie_band_append_chunks (dottie_band_single_chunk hv) (ih htail)
    · simp [hcheck] at h

#print axioms dottie_band_append_chunks
#print axioms dottie_band_integer_sums_of_chunk
#print axioms dottie_band_check_rows_sound

end QuarticModel
