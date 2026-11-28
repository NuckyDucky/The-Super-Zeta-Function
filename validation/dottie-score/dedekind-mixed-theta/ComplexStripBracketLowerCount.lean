import DedekindFiniteStripCounts

/-! Disjoint sign-change brackets yield a lower bound relative to a checked
checkpoint, with reflection accounting for the negative heights. -/

namespace FieldTarget

open Complex Set

noncomputable section

theorem NonzeroEntireFunction.stripZeroCount_ge_of_disjoint_brackets
    {ι : Type*} [Fintype ι] (F : NonzeroEntireFunction) {T U : ℝ}
    (hT : 0 ≤ T) (hTU : T ≤ U) (a b : ι → ℝ)
    (hNear : ∀ i, T ≤ a i) (hFar : ∀ i, b i ≤ U)
    (hDisjoint : Pairwise (fun i j ↦ Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (hRoot : ∀ i, ∃ t ∈ Ioo (a i) (b i), F ⟨1 / 2, t⟩ = 0)
    (hReflect : ∀ w, F (1 - w) = F w)
    (P : ℂ → Prop) (hP : ∀ w, w.re = 1 / 2 → P w) :
    F.stripZeroCount T P + 2 * Fintype.card ι ≤ F.stripZeroCount U P := by
  classical
  choose t ht hzero using hRoot
  have htpos (i : ι) : 0 < t i := hT.trans_lt ((hNear i).trans_lt (ht i).1)
  have htinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    exact (Set.disjoint_left.mp (hDisjoint hne)) (ht i) (hij.symm ▸ ht j)
  let z (p : ι × Bool) : ℂ := ⟨1 / 2, if p.2 then t p.1 else -t p.1⟩
  have hz (i : ι) (e : Bool) : F (z (i, e)) = 0 := by
    cases e
    · have h : z (i, false) = 1 - (⟨1 / 2, t i⟩ : ℂ) := by
        apply Complex.ext <;> norm_num [z]
      rw [h, hReflect]
      exact hzero i
    · exact hzero i
  have hIm (i : ι) (e : Bool) : |(z (i, e)).im| = t i := by
    cases e <;> simp [z, abs_of_pos (htpos i)]
  have hinj : Function.Injective z := by
    rintro ⟨i, e⟩ ⟨j, f⟩ hij
    have habs := congrArg (fun w : ℂ ↦ |w.im|) hij
    rw [hIm, hIm] at habs
    have heq := htinj habs
    subst j
    cases e <;> cases f
    · rfl
    · have h := congrArg Complex.im hij
      simp [z] at h
      linarith only [h, htpos i]
    · have h := congrArg Complex.im hij
      simp [z] at h
      linarith only [h, htpos i]
    · rfl
  let base := (F.stripZeros T).filter P
  let more := Finset.univ.image z
  let weight := analyticOrderNatAt F.toFun
  have hMore (w : ℂ) (hw : w ∈ more) :
      w ∈ (F.stripZeros U).filter P ∧ T < |w.im| := by
    obtain ⟨⟨i, e⟩, _, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨Finset.mem_filter.mpr ⟨(F.mem_stripZeros U _).mpr ?_, hP _ rfl⟩, ?_⟩
    · refine ⟨by norm_num [z], by norm_num [z], ?_, hz i e⟩
      rw [hIm]
      exact (ht i).2.le.trans (hFar i)
    · rw [hIm]
      exact (hNear i).trans_lt (ht i).1
  have hd : Disjoint base more := by
    refine Finset.disjoint_left.mpr (fun w hbase hmore ↦ ?_)
    exact (hMore w hmore).2.not_ge ((F.mem_stripZeros T w).mp (Finset.mem_filter.mp hbase).1).2.2.1
  have hsub : base ∪ more ⊆ (F.stripZeros U).filter P := by
    intro w hw
    rcases Finset.mem_union.mp hw with hb | hm
    · obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hb
      obtain ⟨hx, hX, hh, hz⟩ := (F.mem_stripZeros T w).mp hb
      exact Finset.mem_filter.mpr ⟨(F.mem_stripZeros U w).mpr ⟨hx, hX, hh.trans hTU, hz⟩, hp⟩
    · exact (hMore w hm).1
  have hcard : more.card = 2 * Fintype.card ι := by
    unfold more
    rw [Finset.card_image_of_injective _ hinj]
    simp [mul_comm]
  have hweight : more.card ≤ ∑ w ∈ more, weight w := by
    rw [← show (∑ _ ∈ more, (1 : ℕ)) = more.card by simp]
    apply Finset.sum_le_sum
    intro w hw
    have hnz := ((F.mem_stripZeros U w).mp (Finset.mem_filter.mp (hMore w hw).1).1).2.2.2
    exact Nat.pos_of_ne_zero (fun hn ↦ ((F.orderNat_eq_zero_iff w).mp hn) hnz)
  have hsum : (∑ w ∈ base ∪ more, weight w) ≤ ∑ w ∈ (F.stripZeros U).filter P, weight w :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ Nat.zero_le _)
  rw [Finset.sum_union hd] at hsum
  rw [← hcard]
  exact (Nat.add_le_add_left hweight _).trans hsum

#print axioms NonzeroEntireFunction.stripZeroCount_ge_of_disjoint_brackets

end

end FieldTarget
