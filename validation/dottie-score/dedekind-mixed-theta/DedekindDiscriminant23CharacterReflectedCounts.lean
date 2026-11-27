import DedekindDiscriminant23CharacterBracket

namespace FieldTarget

open MeasureTheory Set

noncomputable section

theorem discriminant23_characterFold_one_sub (w : ℂ) :
    discriminant23CharacterFold (1 - w) = discriminant23CharacterFold w := by
  have h (x : ℝ) : discriminant23FoldWeight (1 - w) x = discriminant23FoldWeight w x := by
    rw [discriminant23FoldWeight, discriminant23FoldWeight,
      show (1 - w) - 1 = -w by ring, show -(1 - w) = w - 1 by ring, add_comm]
  simp_rw [discriminant23CharacterFold, discriminant23_classLambdaZero_eq_fold, h]

theorem discriminant23_character_line_count_ge_two {T : ℝ} (hT : 11 / 2 ≤ T) :
    2 ≤ discriminant23CharacterCountingFunction.stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  classical
  obtain ⟨t, ht, hz, _⟩ := discriminant23_dedekind_zero_between_five_and_eleven_halves
  let z : ℂ := ⟨1 / 2, t⟩
  let z' : ℂ := ⟨1 / 2, -t⟩
  let f := discriminant23CharacterCountingFunction
  have hpos : 0 < t := by linarith [ht.1]
  have hreflect : 1 - z = z' := by
    apply Complex.ext <;> norm_num [z, z']
  have hz' : f z' = 0 := by
    change discriminant23CharacterFold z' = 0
    rw [← hreflect, discriminant23_characterFold_one_sub]
    exact hz
  have hne : z ≠ z' := by
    intro e
    have him := congrArg Complex.im e
    change t = -t at him
    linarith
  have hstrip (w : ℂ) (hw : w.re = 1 / 2) (hht : |w.im| ≤ T) (hzero : f w = 0) :
      w ∈ (f.stripZeros T).filter (fun w ↦ w.re = 1 / 2) := by
    have hRePos : 0 < w.re := by rw [hw]; norm_num
    have hReLt : w.re < 1 := by rw [hw]; norm_num
    exact Finset.mem_filter.mpr ⟨(f.mem_stripZeros T w).mpr ⟨hRePos, hReLt, hht, hzero⟩, hw⟩
  have hHeight : |t| ≤ T := by
    rw [abs_of_nonneg hpos.le]
    exact ht.2.le.trans hT
  have hz_mem := hstrip z rfl hHeight hz
  have hz'_mem : z' ∈ (f.stripZeros T).filter (fun w ↦ w.re = 1 / 2) := by
    apply hstrip z' rfl _ hz'
    change |-t| ≤ T
    simpa only [abs_neg] using hHeight
  have hSub : ({z, z'} : Finset ℂ) ⊆ (f.stripZeros T).filter (fun w ↦ w.re = 1 / 2) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hz_mem
    · exact hz'_mem
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg
    (f := analyticOrderNatAt f.toFun) hSub (fun _ _ _ ↦ Nat.zero_le _)
  rw [Finset.sum_pair hne] at hsum
  have horder (w : ℂ) (hzero : f w = 0) : 0 < analyticOrderNatAt f.toFun w :=
    Nat.pos_iff_ne_zero.mpr (fun h ↦ ((f.orderNat_eq_zero_iff w).mp h) hzero)
  change 2 ≤ ∑ w ∈ (f.stripZeros T).filter (fun w ↦ w.re = 1 / 2), analyticOrderNatAt f.toFun w
  have ha := horder z hz
  have hb := horder z' hz'
  omega

theorem discriminant23_dedekind_line_count_ge_four {T : ℝ} (hT : 11 / 2 ≤ T) :
    4 ≤ (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount T
      (fun w ↦ w.re = 1 / 2) := by
  rw [discriminant23_stripZeroCount_eq_base_add_character]
  have h := discriminant23_character_line_count_ge_two hT
  omega

#check @discriminant23_dedekind_line_count_ge_four
#print axioms discriminant23_characterFold_one_sub
#print axioms discriminant23_character_line_count_ge_two
#print axioms discriminant23_dedekind_line_count_ge_four

end

end FieldTarget
