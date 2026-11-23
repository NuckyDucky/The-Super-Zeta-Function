import DottieBandPrimality

/-! A kernel-reducible Lucas check for the ranges in the retained bands.
Its caller supplies proofs of primality for the factors of p−1. -/

namespace QuarticModel

set_option autoImplicit false

private def dottieBandModPow (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | fuel+1, e =>
    let half := dottieBandModPow a m fuel (e/2)
    let square := (half*half) % m
    if e % 2 = 0 then square else (square*a) % m

private theorem dottie_band_mod_pow_correct (a m fuel e : ℕ) (h : e < 2^fuel) :
    dottieBandModPow a m fuel e = a^e % m := by
  induction fuel generalizing e with
  | zero =>
    have he : e = 0 := by simpa only [pow_zero,Nat.lt_one_iff] using h
    simp [dottieBandModPow,he]
  | succ fuel ih =>
    have hhalf : e/2 < 2^fuel := (Nat.div_lt_iff_lt_mul (by decide)).2
      (by simpa only [pow_succ] using h)
    simp only [dottieBandModPow,ih (e/2) hhalf]
    have hdiv := Nat.mod_add_div e 2
    split_ifs with he
    · have hpow : a^e = a^(e/2)*a^(e/2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      exact (Nat.mul_mod (a^(e/2)) (a^(e/2)) m).symm
    · have hre : e % 2 = 1 := by have := Nat.mod_lt e (by decide : 0 < 2); omega
      have hpow : a^e = (a^(e/2)*a^(e/2))*a := by
        rw [← pow_add, ← pow_succ]
        congr 1
        omega
      rw [hpow,Nat.mul_mod (a^(e/2)*a^(e/2)) a m,Nat.mul_mod (a^(e/2)) (a^(e/2)) m]
      simpa only [Nat.mod_mod] using Nat.mul_mod ((a^(e/2)%m)*(a^(e/2)%m)%m) a m

/-- Arithmetic portion of a Lucas node. The 64-step bound covers every
prime that can occur in the three retained Dottie bands. -/
def dottieBandLucasCheck (p g : ℕ) (factors : List ℕ) : Bool :=
  decide (1 < p ∧ p < 2^64 ∧ factors.prod = p-1) &&
    (decide (dottieBandModPow g p 64 (p-1) = 1) &&
      factors.all (fun q => decide (dottieBandModPow g p 64 ((p-1)/q) ≠ 1)))

theorem dottie_band_lucas_check_sound {p g : ℕ} {factors : List ℕ}
    (hp : ∀ q ∈ factors, q.Prime) (h : dottieBandLucasCheck p g factors = true) :
    p.Prime := by
  simp only [dottieBandLucasCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  obtain ⟨⟨hp₀,hp₁,hprod⟩,hpow,hproper⟩ := h
  have he (e : ℕ) (he : e ≤ p) :
      ((dottieBandModPow g p 64 e : ℕ) : ZMod p) = (g : ZMod p)^e := by
    rw [dottie_band_mod_pow_correct g p 64 e (he.trans_lt hp₁),ZMod.natCast_mod,Nat.cast_pow]
  have ha := he (p-1) (Nat.sub_le _ _)
  rw [hpow,Nat.cast_one] at ha
  apply dottie_lucas_of_factor_list p (g : ZMod p) factors hprod hp ha.symm
  intro q hq hf
  let e := (p-1)/q
  have hel : e ≤ p := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hc := he e hel
  change (g : ZMod p)^e = 1 at hf
  rw [hf] at hc
  have hval := congrArg ZMod.val hc
  have hr : dottieBandModPow g p 64 e < p := by
    rw [dottie_band_mod_pow_correct g p 64 e (hel.trans_lt hp₁)]
    exact Nat.mod_lt _ (by omega)
  let : Fact (1 < p) := ⟨hp₀⟩
  rw [ZMod.val_natCast_of_lt hr,ZMod.val_one] at hval
  exact hproper q hq hval

#print axioms dottie_band_lucas_check_sound

inductive DottieBandPrimeNode where
  | leaf (prime : ℕ)
  | lucas (prime generator : ℕ) (factorIndices : List ℕ)

def DottieBandPrimeNode.value : DottieBandPrimeNode → ℕ
  | .leaf p | .lucas p .. => p

def dottieBandPrimeAt (table : Array DottieBandPrimeNode) (i : ℕ) : DottieBandPrimeNode :=
  table[i]?.getD (.leaf 0)

/-- A node may use only earlier prime entries, and the arithmetic check
validates the full product of those factors. -/
def dottieBandPrimeTableCheck (table : Array DottieBandPrimeNode) (i : ℕ) : Bool :=
  match dottieBandPrimeAt table i with
  | .leaf p => decide (p ≤ 256) && decide p.Prime
  | .lucas p g refs =>
    (refs.all (fun j => decide (j < i))) &&
      dottieBandLucasCheck p g (refs.map (fun j => (dottieBandPrimeAt table j).value))

theorem dottie_band_prime_table_sound (table : Array DottieBandPrimeNode) (i : ℕ)
    (h : ∀ j ≤ i, dottieBandPrimeTableCheck table j = true) :
    (dottieBandPrimeAt table i).value.Prime := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hc := h i le_rfl
    rw [dottieBandPrimeTableCheck] at hc
    cases hn : dottieBandPrimeAt table i with
    | leaf p =>
      rw [hn] at hc
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
      exact hc.2
    | lucas p g refs =>
      rw [hn] at hc
      rw [Bool.and_eq_true] at hc
      obtain ⟨href,he⟩ := hc
      apply dottie_band_lucas_check_sound _ he
      intro q hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      have hji := of_decide_eq_true (List.all_eq_true.mp href j hj)
      exact ih j hji (fun k hk => h k (hk.trans hji.le))

#print axioms dottie_band_prime_table_sound

/-- Positive factor rows may refer to any verified root by its value and
table index. The second comparison prevents misindexed root claims. -/
def dottieBandPrimeRootOk (table : Array DottieBandPrimeNode) (roots : List (ℕ × ℕ)) (p : ℕ) : Bool :=
  roots.any (fun ref => decide (ref.1 = p ∧ ref.2 < table.size ∧
    (dottieBandPrimeAt table ref.2).value = p))

theorem dottie_band_prime_root_ok_sound {table : Array DottieBandPrimeNode} {roots : List (ℕ × ℕ)}
    (h : (List.range table.size).all (dottieBandPrimeTableCheck table) = true)
    (p : ℕ) (hp : dottieBandPrimeRootOk table roots p = true) : p.Prime := by
  simp only [dottieBandPrimeRootOk,List.any_eq_true,decide_eq_true_eq] at hp
  obtain ⟨ref,_,_,hi,hp⟩ := hp
  rw [← hp]
  exact dottie_band_prime_table_sound table ref.2 (fun j hj =>
    List.all_eq_true.mp h j (List.mem_range.mpr (hj.trans_lt hi)))

#print axioms dottie_band_prime_root_ok_sound

end QuarticModel
