import DedekindFiniteStripCounts

/-! A positive simple crossing and its reflection extend a cumulative count. -/

namespace FieldTarget

open Complex Set
open scoped BigOperators

noncomputable section

private theorem orderNat_one_sub_of_reflection (F : NonzeroEntireFunction)
    (hReflect : ∀ w : ℂ, F (1 - w) = F w) (w : ℂ) :
    analyticOrderNatAt F.toFun (1 - w) = analyticOrderNatAt F.toFun w := by
  let reflect (z : ℂ) := 1 - z
  have hr : HasDerivAt reflect (-1) w := (hasDerivAt_id w).const_sub (1 : ℂ)
  have ha : AnalyticAt ℂ reflect w :=
    ((differentiable_const (1 : ℂ)).sub differentiable_id).analyticAt w
  have hder : deriv reflect w ≠ 0 := by rw [hr.deriv]; norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := F.toFun) ha hder
  have he : F.toFun ∘ reflect = F.toFun := funext hReflect
  rw [he] at h
  exact congrArg ENat.toNat h.symm

theorem NonzeroEntireFunction.stripZeroCount_add_reflected_crossing (F : NonzeroEntireFunction)
    {T U t : ℝ} (hT : 0 ≤ T) (ht : T < t) (hU : t ≤ U)
    (hReflect : ∀ w : ℂ, F (1 - w) = F w)
    (hOnly : ∀ w : ℂ, w.re ∈ Ioo (0 : ℝ) 1 → w.im ∈ Ioc T U →
      (F w = 0 ↔ w = ⟨1 / 2, t⟩))
    (hSimple : analyticOrderNatAt F.toFun ⟨1 / 2, t⟩ = 1)
    (P : ℂ → Prop) (hP : ∀ w : ℂ, w.re = 1 / 2 → P w) :
    F.stripZeroCount U P = F.stripZeroCount T P + 2 := by
  classical
  let p : ℂ := ⟨1 / 2, t⟩
  let q : ℂ := 1 - p
  have hpRe : p.re = 1 / 2 := rfl
  have hqRe : q.re = 1 / 2 := by
    change 1 - p.re = 1 / 2
    rw [hpRe]
    norm_num
  have hpIm : p.im = t := rfl
  have hqIm : q.im = -t := by simp [q, hpIm]
  have hpHeight : T < |p.im| := by rw [hpIm, abs_of_pos (hT.trans_lt ht)]; exact ht
  have hqHeight : T < |q.im| := by rw [hqIm, abs_neg, abs_of_pos (hT.trans_lt ht)]; exact ht
  have hNe : p ≠ q := by
    intro hpq
    have h := congrArg Complex.im hpq
    rw [hpIm, hqIm] at h
    linarith only [h, ht, hT]
  have hpZero : F p = 0 :=
    (hOnly p (by rw [hpRe]; constructor <;> norm_num) (by rw [hpIm]; exact ⟨ht, hU⟩)).mpr rfl
  have hqZero : F q = 0 := (hReflect p).trans hpZero
  have hShape : F.stripZeros U = F.stripZeros T ∪ {p, q} := by
    ext w
    rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      NonzeroEntireFunction.mem_stripZeros, NonzeroEntireFunction.mem_stripZeros]
    constructor
    · rintro ⟨hl, hr, hAbs, hz⟩
      by_cases hLow : |w.im| ≤ T
      · exact .inl ⟨hl, hr, hLow, hz⟩
      · right
        have hHigh := lt_of_not_ge hLow
        by_cases hPos : 0 ≤ w.im
        · rw [abs_of_nonneg hPos] at hAbs hHigh
          exact .inl ((hOnly w ⟨hl, hr⟩ ⟨hHigh, hAbs⟩).mp hz)
        · rw [abs_of_neg (lt_of_not_ge hPos)] at hAbs hHigh
          have hRe : (1 - w).re ∈ Ioo (0 : ℝ) 1 := by
            rw [Complex.sub_re, Complex.one_re]
            exact ⟨by linarith only [hr], by linarith only [hl]⟩
          have hIm : (1 - w).im ∈ Ioc T U := by
            simpa only [mem_Ioc, Complex.sub_im, Complex.one_im, zero_sub] using And.intro hHigh hAbs
          have h := (hOnly (1 - w) hRe hIm).mp ((hReflect w).trans hz)
          change 1 - w = p at h
          right
          change w = 1 - p
          rw [← h]
          ring
    · rintro (⟨hl, hr, hAbs, hz⟩ | rfl | rfl)
      · exact ⟨hl, hr, hAbs.trans (ht.le.trans hU), hz⟩
      · rw [hpRe, hpIm, abs_of_pos (hT.trans_lt ht)]
        exact ⟨by norm_num, by norm_num, hU, hpZero⟩
      · rw [hqRe, hqIm, abs_neg, abs_of_pos (hT.trans_lt ht)]
        exact ⟨by norm_num, by norm_num, hU, hqZero⟩
  have hDisjoint : Disjoint (F.stripZeros T) ({p, q} : Finset ℂ) := by
    apply Finset.disjoint_left.mpr
    intro w hw
    have h := ((F.mem_stripZeros T w).mp hw).2.2.1
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact (not_le_of_gt hpHeight) h
    · exact (not_le_of_gt hqHeight) h
  have hFilter : ({p, q} : Finset ℂ).filter P = {p, q} := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hP _ hpRe
    · exact hP _ hqRe
  have hOrderQ : analyticOrderNatAt F.toFun q = 1 :=
    (orderNat_one_sub_of_reflection F hReflect p).trans hSimple
  simp only [NonzeroEntireFunction.stripZeroCount, hShape, Finset.filter_union, hFilter,
    Finset.sum_union (hDisjoint.mono_left (Finset.filter_subset P (F.stripZeros T))), Finset.sum_pair hNe,
    show analyticOrderNatAt F.toFun p = 1 from hSimple, hOrderQ]

#check @NonzeroEntireFunction.stripZeroCount_add_reflected_crossing
#print axioms NonzeroEntireFunction.stripZeroCount_add_reflected_crossing

end
end FieldTarget
