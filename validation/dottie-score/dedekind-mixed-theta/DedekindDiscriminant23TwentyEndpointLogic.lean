import ComplexStripBracketLowerCount
import DedekindDiscriminant23NineteenHalvesBand

/-! The marked height cells and the lower count supplied by their endpoint signs. -/

namespace FieldTarget

open Set

noncomputable section

def discriminant23TwentyHeight (k : ℕ) : ℝ := 19 / 2 + (k : ℝ) / 16

def discriminant23TwentyDirection (k : ℕ) : ℤ :=
  if k ∈ ([12, 54, 111, 137] : List ℕ) then -1
  else if k ∈ ([30, 82, 121, 153] : List ℕ) then 1 else 0

def discriminant23TwentyCrossingIndex (i : Fin 8) : ℕ :=
  ([12, 30, 54, 82, 111, 121, 137, 153] : List ℕ).getD i.val 0

def Discriminant23TwentyEndpointSigns : Prop :=
  ∀ k < 168, discriminant23TwentyDirection k ≠ 0 →
    let d := discriminant23TwentyDirection k
    0 < (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, discriminant23TwentyHeight k⟩).re ∧
      (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, discriminant23TwentyHeight (k + 1)⟩).re < 0

private theorem crossing_index_bounds : ∀ i : Fin 8,
    discriminant23TwentyCrossingIndex i < 168 ∧
      discriminant23TwentyDirection (discriminant23TwentyCrossingIndex i) ≠ 0 := by
  decide +kernel

private theorem crossing_index_complete : ∀ k : Fin 168,
    discriminant23TwentyDirection k.val ≠ 0 →
      ∃ i : Fin 8, discriminant23TwentyCrossingIndex i = k.val := by
  decide +kernel

private theorem crossing_index_separated : ∀ i j : Fin 8, i ≠ j →
    discriminant23TwentyCrossingIndex i + 1 ≤ discriminant23TwentyCrossingIndex j ∨
      discriminant23TwentyCrossingIndex j + 1 ≤ discriminant23TwentyCrossingIndex i := by
  decide +kernel

theorem discriminant23_twentyEndpointSigns_of_marked
    (h : ∀ i : Fin 8,
      let k := discriminant23TwentyCrossingIndex i
      let d := discriminant23TwentyDirection k
      0 < (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, discriminant23TwentyHeight k⟩).re ∧
        (d : ℝ) * (discriminant23CharacterFold
          ⟨1 / 2, discriminant23TwentyHeight (k + 1)⟩).re < 0) :
    Discriminant23TwentyEndpointSigns := by
  intro k hk hd
  obtain ⟨i, hi⟩ := crossing_index_complete ⟨k, hk⟩ hd
  simpa only [hi] using h i

private theorem twentyHeight_monotone : Monotone discriminant23TwentyHeight := by
  intro a b hab
  unfold discriminant23TwentyHeight
  gcongr

private theorem character_zero_of_signed_endpoints {a b : ℝ} (hab : a ≤ b) {d : ℤ} (hd : d ≠ 0)
    (ha : 0 < (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, a⟩).re)
    (hb : (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, b⟩).re < 0) :
    ∃ t ∈ Ioo a b, discriminant23CharacterFold ⟨1 / 2, t⟩ = 0 := by
  let f (t : ℝ) := (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, t⟩).re
  have hPoint : Continuous (fun t : ℝ ↦ (⟨1 / 2, t⟩ : ℂ)) := by
    convert (continuous_const.add (Complex.continuous_ofReal.mul continuous_const) :
      Continuous fun t : ℝ ↦ (1 / 2 : ℂ) + (t : ℂ) * Complex.I) using 1
    funext t
    apply Complex.ext <;> simp
  have hcont : Continuous f :=
    continuous_const.mul (Complex.continuous_re.comp
      (discriminant23CharacterFold_differentiable.continuous.comp hPoint))
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo' hab hcont.continuousOn
    (show (0 : ℝ) ∈ Ioo (f b) (f a) from ⟨hb, ha⟩)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  exact ⟨t, ht, Complex.ext ((mul_eq_zero.mp hzero).resolve_left hd')
    (discriminant23_characterFold_im_eq_zero_on_line (w := ⟨1 / 2, t⟩) rfl)⟩

theorem discriminant23_twenty_character_counts_ge_of_endpointSigns
    (h : Discriminant23TwentyEndpointSigns) :
    22 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun _ ↦ True) ∧
      22 ≤ discriminant23CharacterCountingFunction.stripZeroCount 20 (fun w ↦ w.re = 1 / 2) := by
  let a (i : Fin 8) := discriminant23TwentyHeight (discriminant23TwentyCrossingIndex i)
  let b (i : Fin 8) := discriminant23TwentyHeight (discriminant23TwentyCrossingIndex i + 1)
  have hNear (i : Fin 8) : (19 / 2 : ℝ) ≤ a i := by
    dsimp [a, discriminant23TwentyHeight]
    exact le_add_of_nonneg_right (by positivity)
  have hFar (i : Fin 8) : b i ≤ (20 : ℝ) := by
    have hi : discriminant23TwentyCrossingIndex i + 1 ≤ 168 := (crossing_index_bounds i).1
    exact (twentyHeight_monotone hi).trans_eq (by norm_num [discriminant23TwentyHeight])
  have hDisjoint : Pairwise (fun i j ↦ Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    rcases crossing_index_separated i j hij with hij' | hji'
    · exact (not_lt_of_ge (twentyHeight_monotone hij')) (hy.1.trans hx.2)
    · exact (not_lt_of_ge (twentyHeight_monotone hji')) (hx.1.trans hy.2)
  have hRoot (i : Fin 8) : ∃ t ∈ Ioo (a i) (b i), discriminant23CharacterFold ⟨1 / 2, t⟩ = 0 := by
    obtain ⟨hk, hd⟩ := crossing_index_bounds i
    obtain ⟨ha, hb⟩ := h (discriminant23TwentyCrossingIndex i) hk hd
    exact character_zero_of_signed_endpoints (twentyHeight_monotone (Nat.le_succ _)) hd ha hb
  have hadd (P : ℂ → Prop) (hP : ∀ w : ℂ, w.re = 1 / 2 → P w) :=
    discriminant23CharacterCountingFunction.stripZeroCount_ge_of_disjoint_brackets
      (T := 19 / 2) (U := 20) (by norm_num) (by norm_num) a b hNear hFar hDisjoint hRoot
      discriminant23_characterFold_one_sub P hP
  constructor
  · have hc := hadd (fun _ ↦ True) (fun _ _ ↦ trivial)
    norm_num [discriminant23_character_counts_at_nineteen_halves.1] at hc
    exact hc
  · have hc := hadd (fun w ↦ w.re = 1 / 2) (fun _ he ↦ he)
    norm_num [discriminant23_character_counts_at_nineteen_halves.2] at hc
    exact hc

theorem discriminant23_twenty_field_counts_ge_of_endpointSigns
    (h : Discriminant23TwentyEndpointSigns) :
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun _ ↦ True) + 44 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun _ ↦ True) ∧
    (mixedThetaCountingFunction (discriminant23QuadraticSubfield : Type)).stripZeroCount 20
        (fun w ↦ w.re = 1 / 2) + 44 ≤
      (mixedThetaCountingFunction Discriminant23GaloisField).stripZeroCount 20 (fun w ↦ w.re = 1 / 2) := by
  obtain ⟨hFull, hLine⟩ := discriminant23_twenty_character_counts_ge_of_endpointSigns h
  constructor
  · rw [discriminant23_stripZeroCount_eq_base_add_character]
    omega
  · rw [discriminant23_stripZeroCount_eq_base_add_character]
    omega

#print axioms discriminant23_twentyEndpointSigns_of_marked
#print axioms discriminant23_twenty_character_counts_ge_of_endpointSigns
#print axioms discriminant23_twenty_field_counts_ge_of_endpointSigns

end

end FieldTarget
