import ComplexStripSingleZero
import DedekindDiscriminant23CharacterComplex
import DedekindDiscriminant23CharacterReflectedCounts

namespace FieldTarget

open Complex Set

noncomputable section

private theorem characterFold_order_reflect (w : ℂ) :
    analyticOrderNatAt discriminant23CharacterFold (1 - w) =
      analyticOrderNatAt discriminant23CharacterFold w := by
  let reflect (z : ℂ) := 1 - z
  have hr : HasDerivAt reflect (-1) w := (hasDerivAt_id w).const_sub (1 : ℂ)
  have ha : AnalyticAt ℂ reflect w := by
    exact ((differentiable_const (1 : ℂ)).sub differentiable_id).analyticAt w
  have hder : deriv reflect w ≠ 0 := by rw [hr.deriv]; norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := discriminant23CharacterFold) ha hder
  have he : discriminant23CharacterFold ∘ reflect = discriminant23CharacterFold :=
    funext discriminant23_characterFold_one_sub
  rw [he] at h
  exact congrArg ENat.toNat h.symm

private theorem characterFold_one_positive_zero_of_model_signs
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (7 / 6) (9 / 2) →
      1 / 100000 < (discriminant23CharacterComplexModel w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (83 / 16) (11 / 2) →
      (discriminant23CharacterComplexModel w).re < -(1 / 100000))
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (9 / 2) (83 / 16) →
      1 / 100000 < (deriv discriminant23CharacterComplexModel w).im) :
    ∃ t ∈ Ioo (9 / 2 : ℝ) (83 / 16),
      analyticOrderNatAt discriminant23CharacterFold ⟨1 / 2, t⟩ = 1 ∧
      ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc 0 (11 / 2) →
        (discriminant23CharacterFold w = 0 ↔ w = ⟨1 / 2, t⟩) := by
  have hmodel (w : ℂ) (hr : w.re ∈ Icc (0 : ℝ) 1) :
      |(discriminant23CharacterFold w).re - (discriminant23CharacterComplexModel w).re| ≤
        1 / 100000 := by
    rw [← Complex.sub_re]
    exact (abs_re_le_norm _).trans
      (discriminant23_characterComplexModel_error (by linarith only [hr.1]) (by linarith only [hr.2]))
  refine strip_zero_unique_of_signed_bands discriminant23CharacterFold_differentiable
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · intro w hr ht
    by_cases ht₀ : w.im ≤ 7 / 6
    · have habs : |w.im| ≤ 7 / 6 := by rwa [abs_of_nonneg ht.1]
      linarith only [(discriminant23_fold_bounds_to_seven_sixths hr.1 hr.2 habs).2]
    · linarith only [hBelow w hr ⟨by linarith only [ht₀], ht.2⟩, (abs_le.mp (hmodel w hr)).1]
  · intro w hr ht
    linarith only [hAbove w hr ht, (abs_le.mp (hmodel w hr)).2]
  · intro w hr ht
    have hε := discriminant23_characterComplexModel_iteratedDeriv_error 1 hr.1 hr.2
    simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one] at hε
    have hd := (abs_im_le_norm _).trans hε
    rw [Complex.sub_im] at hd
    linarith only [hSlope w hr ht, (abs_le.mp hd).1]
  · intro t _
    exact discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl

/-- Three uniform model signs suffice for the first complete nonzero
character count, with the negative height supplied by reflection. -/
theorem discriminant23_character_counts_at_eleven_halves_of_model_signs
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (7 / 6) (9 / 2) →
      1 / 100000 < (discriminant23CharacterComplexModel w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (83 / 16) (11 / 2) →
      (discriminant23CharacterComplexModel w).re < -(1 / 100000))
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (9 / 2) (83 / 16) →
      1 / 100000 < (deriv discriminant23CharacterComplexModel w).im) :
    discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) = 2 := by
  classical
  obtain ⟨t, ht, hOrder, hUnique⟩ := characterFold_one_positive_zero_of_model_signs hBelow hAbove hSlope
  let p : ℂ := ⟨1 / 2, t⟩
  let q : ℂ := 1 - p
  have hpRe : p.re = 1 / 2 := rfl
  have hqRe : q.re = 1 / 2 := by
    change 1 - p.re = 1 / 2
    rw [hpRe]
    norm_num
  have hpIm : p.im = t := rfl
  have hqIm : q.im = -t := by simp [q, hpIm]
  have hNe : p ≠ q := by
    intro hpq
    have he := congrArg Complex.im hpq
    rw [hpIm, hqIm] at he
    linarith only [he, ht.1]
  have ht₀ : 0 ≤ t := by linarith only [ht.1]
  have ht₁ : t ≤ 11 / 2 := by linarith only [ht.2]
  have hpZero : discriminant23CharacterFold p = 0 :=
    (hUnique p (by rw [hpRe]; constructor <;> norm_num) (by rw [hpIm]; exact ⟨ht₀, ht₁⟩)).mpr rfl
  have hqZero : discriminant23CharacterFold q = 0 := by
    change discriminant23CharacterFold (1 - p) = 0
    rw [discriminant23_characterFold_one_sub, hpZero]
  have hFinset : discriminant23CharacterCountingFunction.stripZeros (11 / 2) = {p, q} := by
    ext w
    rw [NonzeroEntireFunction.mem_stripZeros, Finset.mem_insert, Finset.mem_singleton]
    change (0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ 11 / 2 ∧ discriminant23CharacterFold w = 0) ↔ _
    constructor
    · rintro ⟨h₀, h₁, hAbs, hZero⟩
      by_cases htpos : 0 ≤ w.im
      · exact .inl ((hUnique w ⟨h₀.le, h₁.le⟩
          ⟨htpos, (le_abs_self _).trans hAbs⟩).mp hZero)
      · have hrRe : (1 - w).re = 1 - w.re := by simp
        have hrIm : (1 - w).im = -w.im := by simp
        have hrHeight : (1 - w).im ∈ Icc (0 : ℝ) (11 / 2) := by
          rw [hrIm]
          exact ⟨by linarith only [htpos], by linarith only [(abs_le.mp hAbs).1]⟩
        have hh : 1 - w = p := (hUnique (1 - w) (by
          rw [hrRe]
          exact ⟨by linarith only [h₁], by linarith only [h₀]⟩) hrHeight).mp
          (by rw [discriminant23_characterFold_one_sub, hZero])
        right
        change w = 1 - p
        rw [← hh]
        ring
    · rintro (rfl | rfl)
      · rw [hpRe, hpIm, abs_of_nonneg ht₀]
        exact ⟨by norm_num, by norm_num, ht₁, hpZero⟩
      · rw [hqRe, hqIm, abs_neg, abs_of_nonneg ht₀]
        exact ⟨by norm_num, by norm_num, ht₁, hqZero⟩
  have hOrderP : analyticOrderNatAt discriminant23CharacterCountingFunction.toFun p = 1 := hOrder
  have hOrderQ : analyticOrderNatAt discriminant23CharacterCountingFunction.toFun q = 1 :=
    (characterFold_order_reflect p).trans hOrder
  have hFilter : ({p, q} : Finset ℂ).filter (fun w ↦ w.re = 1 / 2) = {p, q} := by
    apply Finset.filter_eq_self.mpr
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hpRe
    · exact hqRe
  constructor
  · simp [NonzeroEntireFunction.stripZeroCount, hFinset, Finset.sum_pair hNe, hOrderP, hOrderQ]
  · simp only [NonzeroEntireFunction.stripZeroCount, hFinset, hFilter, Finset.sum_pair hNe, hOrderP, hOrderQ]

#check @discriminant23_character_counts_at_eleven_halves_of_model_signs
#print axioms discriminant23_character_counts_at_eleven_halves_of_model_signs

end
end FieldTarget
