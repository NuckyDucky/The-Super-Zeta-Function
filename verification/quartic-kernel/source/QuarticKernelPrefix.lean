import QuarticKernelAnnulus
import QuarticShellArray

namespace QuarticKernel

def spanWidth : List ℕ → ℕ
  | [] => 0
  | w::ws => w + spanWidth ws

/-- A singleton uses its exact final prefix. Across a longer span, the
total of the negative readings bounds every possible deficit. -/
private def spanPositive (s : ℤ) (w : ℕ) (t : AnnulusStats) : Bool :=
  decide (1 ≤ s + if w = 1 then t.1 else t.2.2)

private theorem spanPositive_sound (i w : ℕ) (s : ℤ) (h : prefixSum i = s)
    (ok : spanPositive s w (annulusStats i (i+w)) = true) :
    ∀ j, i < j → j ≤ i+w → 1 ≤ prefixSum j := by
  unfold spanPositive at ok
  have hc := of_decide_eq_true ok
  intro j hj hk
  by_cases hw : w = 1
  · rw [if_pos hw] at hc
    have hj' : j = i+w := by omega
    rw [hj', annulusStats_final i (i+w) (Nat.le_add_right _ _), h]
    exact hc
  · rw [if_neg hw] at hc
    exact hc.trans (h ▸ annulusStats_prefix i (i+w) j hj.le hk)

abbrev SpanResult := ℤ × ℤ × Bool

def checkSpans (i : ℕ) (s : ℤ) : List ℕ → SpanResult
  | [] => (s, 0, true)
  | w :: ws =>
    let t := annulusStats i (i+w)
    let tail := checkSpans (i+w) (s+t.1) ws
    (tail.1, (w:ℤ)*s + t.2.1 + tail.2.1, spanPositive s w t && tail.2.2)

theorem checkSpans_final (i : ℕ) (s : ℤ) (ws : List ℕ) (h : prefixSum i = s) :
    prefixSum (i+spanWidth ws) = (checkSpans i s ws).1 := by
  induction ws generalizing i s with
  | nil => simpa [spanWidth,checkSpans] using h
  | cons w ws ih =>
    simp only [spanWidth,checkSpans]
    rw [← Nat.add_assoc]
    apply ih
    rw [annulusStats_final i (i+w) (Nat.le_add_right _ _), h]

theorem checkSpans_weight (i : ℕ) (s : ℤ) (ws : List ℕ) (h : prefixSum i = s) :
    (∑ j ∈ Finset.range (spanWidth ws), prefixSum (i+j+1)) = (checkSpans i s ws).2.1 := by
  induction ws generalizing i s with
  | nil => simp [spanWidth,checkSpans]
  | cons w ws ih =>
    simp only [spanWidth, checkSpans, Finset.sum_range_add]
    have hfix : (∑ j ∈ Finset.range w, prefixSum (i+j+1)) =
        (w:ℤ)*s + (annulusStats i (i+w)).2.1 := by
      have A := annulusStats_weighted i (i+w) (Nat.le_add_right i w)
      simpa only [Nat.add_sub_cancel_left,h] using A
    have hprefix := annulusStats_final i (i+w) (Nat.le_add_right i w)
    rw [h] at hprefix
    simp_rw [show ∀ j : ℕ, i+(w+j)+1 = (i+w)+j+1 by intros; omega]
    rw [hfix, ih (i+w) _ hprefix]

theorem checkSpans_positive (i : ℕ) (s : ℤ) (ws : List ℕ) (h : prefixSum i = s)
    (ok : (checkSpans i s ws).2.2 = true) :
    ∀ j, i < j → j ≤ i+spanWidth ws → 1 ≤ prefixSum j := by
  induction ws generalizing i s with
  | nil =>
    intro j hj hk
    simp only [spanWidth,Nat.add_zero] at hk
    omega
  | cons w ws ih =>
    simp only [checkSpans,Bool.and_eq_true] at ok
    intro j hj hk
    by_cases hz : j ≤ i+w
    · exact spanPositive_sound i w s h ok.1 j hj hz
    · have hprefix := annulusStats_final i (i+w) (Nat.le_add_right i w)
      rw [h] at hprefix
      apply ih (i+w) _ hprefix ok.2 j (lt_of_not_ge hz)
      simpa only [spanWidth,Nat.add_assoc] using hk

/-- Numerical checkpoints can be checked separately and joined without
reevaluating any of the character sums in the assembly proof. -/
inductive KernelBinChain : ℕ → ℤ → List ShellBin → ℤ → Prop where
  | nil (i : ℕ) (s : ℤ) : KernelBinChain i s [] s
  | cons {i : ℕ} {s t u : ℤ} {g : ShellBin} {gs : List ShellBin}
      (ws : List ℕ) (hw : 0 < g.width) (hsize : spanWidth ws = g.width)
      (hcheck : checkSpans i s ws = (t, (g.weight:ℤ), true))
      (tail : KernelBinChain (i+g.width) t gs u) :
      KernelBinChain i s (g::gs) u

theorem KernelBinChain.append {i : ℕ} {s t u : ℤ} {as bs : List ShellBin}
    (h₁ : KernelBinChain i s as t) (h₂ : KernelBinChain (i+binCount as) t bs u) :
    KernelBinChain i s (as++bs) u := by
  induction h₁ with
  | nil => simpa [binCount] using h₂
  | cons ws hw hsize hcheck _ ih =>
    apply KernelBinChain.cons ws hw hsize hcheck
    exact ih (by simpa only [binCount,Nat.add_assoc] using h₂)

theorem KernelBinChain.sound {i : ℕ} {s t : ℤ} {gs : List ShellBin}
    (hc : KernelBinChain i s gs t) (hi : prefixSum i = s) :
    BinsCorrect i gs ∧ prefixSum (i+binCount gs) = t ∧
      (∀ j, i < j → j ≤ i+binCount gs → 1 ≤ prefixSum j) := by
  induction hc with
  | nil =>
    simp only [BinsCorrect,binCount,Nat.add_zero,hi,true_and]
    intro j hj hk
    omega
  | @cons i s t u g gs ws hw hsize hcheck _ ih =>
    have hfinal : prefixSum (i+g.width) = t := by
      simpa only [hsize,hcheck] using checkSpans_final i s ws hi
    have hweight : (g.weight:ℤ) = ∑ j ∈ Finset.range g.width, prefixSum (i+j+1) := by
      simpa only [hsize,hcheck] using (checkSpans_weight i s ws hi).symm
    have hpos : ∀ j, i < j → j ≤ i+g.width → 1 ≤ prefixSum j := by
      have ok : (checkSpans i s ws).2.2 = true := by rw [hcheck]
      simpa only [hsize] using checkSpans_positive i s ws hi ok
    obtain ⟨hrest,hout,hot⟩ := ih hfinal
    refine ⟨⟨hw,hweight,hrest⟩, by simpa only [binCount,Nat.add_assoc] using hout, ?_⟩
    intro j hj hk
    by_cases hh : j ≤ i+g.width
    · exact hpos j hj hh
    · exact hot j (lt_of_not_ge hh) (by simpa only [binCount,Nat.add_assoc] using hk)

#print axioms checkSpans_final
#print axioms checkSpans_weight
#print axioms checkSpans_positive
#print axioms KernelBinChain.sound

end QuarticKernel
