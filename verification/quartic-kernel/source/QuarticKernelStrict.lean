import QuarticKernelPrefix
namespace QuarticKernel

private def spanStats (lo hi : ℕ) : AnnulusStats :=
  if hi ≤ 65536 then annulusStats lo hi else sweepAnnulusStats lo hi

private theorem spanStats_eq (lo hi : ℕ) : spanStats lo hi = annulusStats lo hi := by
  unfold spanStats
  rw [sweepAnnulusStats_eq]
  split <;> rfl

/-- Force the integer accumulators at each step of the kernel reduction. -/
def checkSpansStrict (i : ℕ) (s : ℤ) : List ℕ → SpanResult
  | [] => (s, 0, true)
  | w :: ws =>
    match spanStats i (i+w) with
    | (count, weight, negative) =>
      forceNat (i+w) fun endPoint =>
      forceInt (s+count) fun endValue =>
      match checkSpansStrict endPoint endValue ws with
      | (last, tailWeight, ok) =>
        forceInt ((w:ℤ)*s + weight + tailWeight) fun totalWeight =>
        (last, totalWeight, decide (1 ≤ s + if w = 1 then count else negative) && ok)

theorem checkSpansStrict_eq (i : ℕ) (s : ℤ) (ws : List ℕ) :
    checkSpansStrict i s ws = checkSpans i s ws := by
  induction ws generalizing i s with
  | nil => rfl
  | cons w ws ih =>
    simp only [checkSpansStrict,spanStats_eq,checkSpans]
    generalize annulusStats i (i+w) = stats
    obtain ⟨count,weight,negative⟩ := stats
    simp only [forceNat_eq,forceInt_eq,ih]
    generalize checkSpans (i+w) (s+count) ws = result
    obtain ⟨last,tailWeight,ok⟩ := result
    rfl

#print axioms checkSpansStrict_eq
end QuarticKernel


