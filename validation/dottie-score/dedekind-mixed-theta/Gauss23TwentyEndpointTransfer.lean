import DedekindDiscriminant23TwentyEndpointLogic
import Gauss23ReducedPhase

/-! Transfer the rational interval tests at the marked endpoints to the height mesh. -/

namespace FieldTarget

private theorem twentyHeight_abs_le {k : ℕ} (hk : k ≤ 168) :
    |discriminant23TwentyHeight k| ≤ 20 := by
  have hK : (k : ℝ) ≤ 168 := by exact_mod_cast hk
  unfold discriminant23TwentyHeight
  rw [abs_of_nonneg (by positivity)]
  linarith only [hK]

private theorem twentyDirection_eq_one_or_neg_one (k : ℕ) (hd : discriminant23TwentyDirection k ≠ 0) :
    discriminant23TwentyDirection k = 1 ∨ discriminant23TwentyDirection k = -1 := by
  by_cases hn : k ∈ ([12, 54, 111, 137] : List ℕ)
  · exact Or.inr (by simp [discriminant23TwentyDirection, hn])
  · by_cases hp : k ∈ ([30, 82, 121, 153] : List ℕ)
    · exact Or.inl (by simp [discriminant23TwentyDirection, hn, hp])
    · exact (hd (by simp [discriminant23TwentyDirection, hn, hp])).elim

theorem discriminant23_signed_endpoints_of_clearances (k : ℕ) (hk : k < 168)
    (hd : discriminant23TwentyDirection k ≠ 0)
    (hA : gauss23ClearsError (152 + (k : ℤ)) 16
      (if discriminant23TwentyDirection k = 1 then true else false))
    (hB : gauss23ClearsError (153 + (k : ℤ)) 16
      (if discriminant23TwentyDirection k = 1 then false else true)) :
    let d := discriminant23TwentyDirection k
    0 < (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, discriminant23TwentyHeight k⟩).re ∧
      (d : ℝ) * (discriminant23CharacterFold ⟨1 / 2, discriminant23TwentyHeight (k + 1)⟩).re < 0 := by
  have ht₀ : ((↑(152 + (k : ℤ)) : ℝ) / (16 : ℝ)) = discriminant23TwentyHeight k := by
    push_cast
    unfold discriminant23TwentyHeight
    ring
  have ht₁ : ((↑(153 + (k : ℤ)) : ℝ) / (16 : ℝ)) = discriminant23TwentyHeight (k + 1) := by
    push_cast
    unfold discriminant23TwentyHeight
    push_cast
    ring
  have hT₀ : |((↑(152 + (k : ℤ)) : ℝ) / (16 : ℝ))| ≤ 20 := ht₀ ▸ twentyHeight_abs_le hk.le
  have hT₁ : |((↑(153 + (k : ℤ)) : ℝ) / (16 : ℝ))| ≤ 20 :=
    ht₁ ▸ twentyHeight_abs_le (Nat.succ_le_of_lt hk)
  dsimp only
  rcases twentyDirection_eq_one_or_neg_one k hd with hpos | hneg
  · have h₀ := gauss23_critical_sign_of_interval (152 + (k : ℤ)) (d := 16)
      (by decide) true hT₀ (by simpa only [hpos, ↓reduceIte] using hA)
    have h₁ := gauss23_critical_sign_of_interval (153 + (k : ℤ)) (d := 16)
      (by decide) false hT₁ (by simpa only [hpos, ↓reduceIte] using hB)
    simp only [Int.cast_ofNat, gauss23CriticalPoint, ht₀, ht₁, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
    rw [hpos]
    simpa only [Int.cast_one, one_mul] using And.intro h₀ h₁
  · have h₀ := gauss23_critical_sign_of_interval (152 + (k : ℤ)) (d := 16)
      (by decide) false hT₀ (by simpa [hneg] using hA)
    have h₁ := gauss23_critical_sign_of_interval (153 + (k : ℤ)) (d := 16)
      (by decide) true hT₁ (by simpa [hneg] using hB)
    simp only [Int.cast_ofNat, gauss23CriticalPoint, ht₀, ht₁, Bool.false_eq_true, ↓reduceIte] at h₀ h₁
    rw [hneg]
    constructor <;> push_cast <;> linarith only [h₀, h₁]

#print axioms discriminant23_signed_endpoints_of_clearances

end FieldTarget
