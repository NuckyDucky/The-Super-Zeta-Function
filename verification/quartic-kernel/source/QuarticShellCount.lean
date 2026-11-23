import QuarticKernel

open scoped BigOperators

namespace QuarticKernel

private def hit (n j : ℕ) : Prop :=
  (j+1)^2 + (n-(j+1)^2).sqrt^2 = n

private instance (n j : ℕ) : Decidable (hit n j) := by
  unfold hit
  infer_instance

private def shell (n : ℕ) : Finset ℕ := (Finset.range n.sqrt).filter (hit n)

private theorem coeff_abs_le_shell (n : ℕ) : |coeff n| ≤ (shell n).card := by
  have h (j : ℕ) : |row n j| ≤ if hit n j then (1:ℤ) else 0 := by
    split_ifs with hj
    · exact row_abs_le_one n j
    · have hz : ¬ ((j+1)*(j+1)+(n-(j+1)*(j+1)).sqrt*(n-(j+1)*(j+1)).sqrt=n) := by
        simpa only [hit, pow_two] using hj
      rw [show row n j = 0 by simp only [row, if_neg hz]]
      norm_num
  unfold coeff
  calc
    _ ≤ ∑ j ∈ Finset.range n.sqrt, |row n j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n.sqrt, if hit n j then (1:ℤ) else 0 :=
      Finset.sum_le_sum fun j _ => h j
    _ = ((shell n).card : ℤ) := by rw [shell, ← Finset.sum_filter]; simp

/-- The absolute coefficient mass through norm N is bounded by the number
of pairs in a square containing all the quarter-plane representatives. -/
theorem coefficient_count_bound (N : ℕ) :
    (∑ n ∈ Finset.range (N+1), |coeff n|) ≤ (2:ℤ)*N := by
  let points := (Finset.range (N+1)).sigma shell
  let target := (Finset.range N.sqrt) ×ˢ (Finset.range (N.sqrt+1))
  let key (p : Σ n : ℕ, ℕ) := (p.2, (p.1-(p.2+1)^2).sqrt)
  have hcard : points.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn key
    · intro p hp
      have hm := Finset.mem_sigma.mp hp
      have hn : p.1 ≤ N := by have := Finset.mem_range.mp hm.1; omega
      have hj := Finset.mem_range.mp (Finset.mem_filter.mp hm.2).1
      have hb : (p.1-(p.2+1)^2).sqrt ≤ N.sqrt :=
        Nat.sqrt_le_sqrt ((Nat.sub_le _ _).trans hn)
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hj.trans_le (Nat.sqrt_le_sqrt hn)),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
    · intro p hp q hq he
      have hpn := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
      have hqn := (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
      have h1 : p.2 = q.2 := congrArg Prod.fst he
      have h2 : (p.1-(p.2+1)^2).sqrt = (q.1-(q.2+1)^2).sqrt := congrArg Prod.snd he
      have hn : p.1 = q.1 := by
        have hp' : (p.2+1)^2 + (p.1-(p.2+1)^2).sqrt^2 = p.1 := hpn
        have hq' : (q.2+1)^2 + (q.1-(q.2+1)^2).sqrt^2 = q.1 := hqn
        rw [h2, h1, hq'] at hp'
        exact hp'.symm
      cases p with
      | mk np jp =>
        cases q with
        | mk nq jq =>
          dsimp only at hn h1
          subst nq
          subst jq
          rfl
  have hsq : N.sqrt * N.sqrt ≤ N := Nat.sqrt_le N
  have hroot : N.sqrt ≤ N := Nat.sqrt_le_self N
  have hb : target.card ≤ 2*N := by
    simp only [target, Finset.card_product, Finset.card_range, Nat.mul_succ]
    omega
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1), ((shell n).card : ℤ) :=
      Finset.sum_le_sum fun n _ => coeff_abs_le_shell n
    _ = (points.card : ℤ) := by simp [points, Finset.card_sigma]
    _ ≤ _ := by exact_mod_cast hcard.trans hb

#print axioms coefficient_count_bound

end QuarticKernel
