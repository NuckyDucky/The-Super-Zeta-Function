import ComplexStripCrossingCount
import ComplexStripSingleZero

/-! Compose closed zero-free boxes and signed crossings into cumulative
counts. Reflection covers the negative heights. -/

namespace FieldTarget

open Complex Set

namespace NonzeroEntireFunction

def HasStripZeroIncrement (F : NonzeroEntireFunction) (a b : ℝ) (n : ℕ) : Prop :=
  ∀ P : ℂ → Prop, (∀ w : ℂ, w.re = 1 / 2 → P w) →
    F.stripZeroCount b P = F.stripZeroCount a P + 2 * n

theorem hasStripZeroIncrement_of_ne_zero (F : NonzeroEntireFunction) {a b : ℝ}
    (hab : a ≤ b) (hReflect : ∀ w, F (1 - w) = F w)
    (hZero : ∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Ioc a b → F w ≠ 0) :
    F.HasStripZeroIncrement a b 0 := by
  have hSet : F.stripZeros b = F.stripZeros a := by
    ext w
    simp only [mem_stripZeros]
    constructor
    · rintro ⟨hlo, hhi, hB, hz⟩
      refine ⟨hlo, hhi, ?_, hz⟩
      by_contra! hw
      by_cases hp : 0 ≤ w.im
      · rw [abs_of_nonneg hp] at hw hB
        exact hZero w ⟨hlo, hhi⟩ ⟨hw, hB⟩ hz
      · rw [abs_of_neg (lt_of_not_ge hp)] at hw hB
        have hr : (1 - w).re ∈ Ioo (0 : ℝ) 1 := by
          rw [Complex.sub_re, Complex.one_re]
          exact ⟨by linarith only [hhi], by linarith only [hlo]⟩
        have hi : (1 - w).im ∈ Ioc a b := by
          simpa only [mem_Ioc, Complex.sub_im, Complex.one_im, zero_sub] using And.intro hw hB
        exact hZero (1 - w) hr hi ((hReflect w).trans hz)
    · rintro ⟨hlo, hhi, hA, hz⟩
      exact ⟨hlo, hhi, hA.trans hab, hz⟩
  intro P _
  simp only [stripZeroCount, hSet, Nat.mul_zero, Nat.add_zero]

theorem hasStripZeroIncrement_of_signed_crossing (F : NonzeroEntireFunction)
    {a b l r d : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hHalf : (1 / 2 : ℝ) ∈ Icc l r)
    (hReflect : ∀ w, F (1 - w) = F w)
    (hReal : ∀ t ∈ Icc a b, (F ⟨1 / 2, t⟩).im = 0)
    (hA : 0 < d * (F ⟨1 / 2, a⟩).re) (hB : d * (F ⟨1 / 2, b⟩).re < 0)
    (hSlope : ∀ w : ℂ, w.re ∈ Icc l r → w.im ∈ Icc a b →
      0 < d * (deriv F.toFun w).im)
    (hCore : ∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Icc a b →
      F w = 0 → w.re ∈ Icc l r) : F.HasStripZeroIncrement a b 1 := by
  obtain ⟨t, ht, hSimple, hOnly⟩ := unique_simple_zero_of_signed_crossing
    (f := F.toFun) (fun w _ _ ↦ F.differentiable.analyticAt w) hHalf hab hA hB hSlope hReal
  intro P hP
  exact F.stripZeroCount_add_reflected_crossing ha ht.1 ht.2.le hReflect
    (fun w hw hi ↦ ⟨fun hz ↦ (hOnly w (hCore w hw ⟨hi.1.le, hi.2⟩ hz)
      ⟨hi.1.le, hi.2⟩).mp hz, fun h ↦ by
      subst w
      exact (hOnly _ hHalf (Ioo_subset_Icc_self ht)).mpr rfl⟩) hSimple P hP

theorem HasStripZeroIncrement.trans {F : NonzeroEntireFunction} {a b c : ℝ} {m n : ℕ}
    (h₁ : F.HasStripZeroIncrement a b m) (h₂ : F.HasStripZeroIncrement b c n) :
    F.HasStripZeroIncrement a c (m + n) := by
  intro P hP
  rw [h₂ P hP, h₁ P hP, Nat.mul_add, Nat.add_assoc]

theorem hasStripZeroIncrement_of_mesh (F : NonzeroEntireFunction)
    (height : ℕ → ℝ) (crossings : ℕ → ℕ) (n : ℕ)
    (hStep : ∀ k < n, F.HasStripZeroIncrement (height k) (height (k + 1)) (crossings k)) :
    F.HasStripZeroIncrement (height 0) (height n) (∑ k ∈ Finset.range n, crossings k) := by
  induction n with
  | zero => simp [HasStripZeroIncrement]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (ih (fun k hk ↦ hStep k (Nat.lt_succ_of_lt hk))).trans (hStep n (Nat.lt_succ_self _))

end NonzeroEntireFunction

#print axioms NonzeroEntireFunction.hasStripZeroIncrement_of_ne_zero
#print axioms NonzeroEntireFunction.hasStripZeroIncrement_of_signed_crossing
#print axioms NonzeroEntireFunction.hasStripZeroIncrement_of_mesh

end FieldTarget
