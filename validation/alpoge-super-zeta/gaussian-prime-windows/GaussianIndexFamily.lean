import GaussianIndexedCutoff
import GaussianPrimitiveIndexWindow

/-! The signed common-divisor weights, with the centering contribution
stored as the single index one. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset Set QuarticModel
open scoped Classical

noncomputable section

abbrev GaussianIndexFamily :=
  Unit ⊕ (ℕ ⊕ ((Nat.Primes × ℕ) ⊕ ((Nat.Primes × ℕ) ⊕ ℕ)))

def gaussianIndexAddress : GaussianIndexFamily → ℕ
  | .inl _ => 1
  | .inr (.inl p) => p + 1
  | .inr (.inr (.inl pk)) => archivedInertTailIndex 1 1 pk
  | .inr (.inr (.inr (.inl pk))) => archivedInertTailIndex 2 0 pk
  | .inr (.inr (.inr (.inr p))) => max 1 p

def gaussianIndexCoefficient : GaussianIndexFamily → ℝ
  | .inl _ => archivedGaussianPrimitiveIndexRamp 1
  | .inr (.inl p) => 2 * archivedInertIndexWeight p 1
  | .inr (.inr (.inl pk)) => 2 * archivedInertIndexWeight pk.1.val 1
  | .inr (.inr (.inr (.inl pk))) => 2 * archivedInertIndexWeight pk.1.val 2
  | .inr (.inr (.inr (.inr p))) => -archivedIndexBaseWeight p

theorem gaussianIndexAddress_pos (i : GaussianIndexFamily) : 0 < gaussianIndexAddress i := by
  rcases i with _ | (p | (pk | (pk | p)))
  · change 0 < (1 : ℕ)
    decide
  · exact Nat.succ_pos _
  · exact archivedInertTailIndex_pos 1 1 pk
  · exact archivedInertTailIndex_pos 2 0 pk
  · exact (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)

private theorem indexBaseWeight_abs_le {p : ℕ} (hp : p.Prime) :
    |archivedIndexBaseWeight p| ≤ 2 * Real.log p := by
  have hl : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  simp only [archivedIndexBaseWeight, if_pos hp, abs_mul, abs_of_nonneg hl]
  apply mul_le_mul_of_nonneg_right _ hl
  split_ifs with h
  · let : Fact p.Prime := ⟨hp⟩
    rw [← archivedUnramifiedDegreeOneWeight_eq_base h.2.1 h.2.2]
    have hpos : 0 ≤ archivedUnramifiedDegreeOneWeight p :=
      Finset.sum_nonneg fun I _ => by split_ifs <;> norm_num
    rw [abs_of_nonneg hpos, archivedUnramifiedDegreeOneWeight]
    calc
      _ ≤ ∑ _I ∈ gaussianPrimesAbove p, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
      _ ≤ 2 := by simpa using (show ((gaussianPrimesAbove p).card : ℝ) ≤ 2 by
        exact_mod_cast (gaussianIndexPrime_shape h.2.1).1)
  · exact archivedGaussianPrimeWeight_abs_le_two p

private theorem indexBaseWeight_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => |archivedIndexBaseWeight n| / ((max 1 n : ℕ) : ℝ) ^ a) := by
  have h := ((LSeriesSummable_vonMangoldt (s := (a : ℂ))
    (by simpa using ha)).norm).mul_left (2 : ℝ)
  refine h.of_nonneg_of_le (fun _ =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_)
  by_cases hp : n.Prime
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rw [max_eq_right hp.one_lt.le, LSeries.norm_term_eq, if_neg hp.ne_zero, vonMangoldt_apply_prime hp,
      Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (indexBaseWeight_abs_le hp) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [archivedIndexBaseWeight, if_neg hp, abs_zero, zero_div]
    exact mul_nonneg (by norm_num) (norm_nonneg _)

private theorem indexShiftWeight_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun p : ℕ => |2 * archivedInertIndexWeight p 1| / ((p + 1 : ℕ) : ℝ) ^ a) := by
  have h := archivedInertIndexWeight_one_summable (by linarith : 0 < a - 1)
  rw [show 1 + (a - 1) = a by ring] at h
  refine (h.mul_left (2 : ℝ)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  by_cases hn : n = 0
  · subst n
    norm_num [archivedInertIndexWeight, archivedGoodIndexPrime]
  · rw [← mul_div_assoc, abs_of_nonneg (mul_nonneg (by norm_num) (archivedInertIndexWeight_nonneg _ _))]
    refine div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) (archivedInertIndexWeight_nonneg _ _))
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _) ?_
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ n) (by linarith)

private theorem indexTailWeight_summable (f k : ℕ) (hfk : f + k = 2)
    {a : ℝ} (ha : 1 < a) :
    Summable (fun pk : Nat.Primes × ℕ =>
      |2 * archivedInertIndexWeight pk.1.val f| / (archivedInertTailIndex f k pk : ℝ) ^ a) := by
  refine ((archivedInertTail_summable f k hfk (by linarith : 1 / 2 < a)).mul_left (2 : ℝ)).congr
    fun pk => ?_
  rw [← mul_div_assoc, abs_of_nonneg
    (mul_nonneg (by norm_num) (archivedInertIndexWeight_nonneg _ _))]

set_option maxHeartbeats 500000 in
theorem gaussianIndexFamily_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun i => |gaussianIndexCoefficient i| / (gaussianIndexAddress i : ℝ) ^ a) := by
  let f (i : GaussianIndexFamily) := |gaussianIndexCoefficient i| / (gaussianIndexAddress i : ℝ) ^ a
  have h0 : Summable (f ∘ Sum.inl) := (hasSum_fintype _).summable
  have h1 : Summable (fun p => f (.inr (.inl p))) := indexShiftWeight_summable ha
  have h2 : Summable (fun pk => f (.inr (.inr (.inl pk)))) := indexTailWeight_summable 1 1 rfl ha
  have h3 : Summable (fun pk => f (.inr (.inr (.inr (.inl pk))))) :=
    indexTailWeight_summable 2 0 rfl ha
  have h4 : Summable (fun p => f (.inr (.inr (.inr (.inr p))))) := by
    simpa only [f, gaussianIndexCoefficient, gaussianIndexAddress, abs_neg] using
      indexBaseWeight_summable ha
  have h34 := Summable.sum (fun i => f (.inr (.inr (.inr i)))) h3 h4
  have h234 := Summable.sum (fun i => f (.inr (.inr i))) h2 h34
  have h1234 := Summable.sum (fun i => f (.inr i)) h1 h234
  exact Summable.sum f h0 h1234

private theorem indexFiniteRamp_hasSum (b : ℕ → ℝ) (N : ℕ → ℕ)
    (hN : ∀ n, n ≤ N n) {x : ℝ} :
    HasSum (fun n => b n * indexRampWeight x (N n))
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), b n * indexRampWeight x (N n)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hn' : ⌊x⌋₊ < n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
  have hcast : (n : ℝ) ≤ (N n : ℝ) := by exact_mod_cast hN n
  have hlt := (Nat.lt_of_floor_lt hn').trans_le hcast
  have hp : 0 < N n := by have := hN n; omega
  have hz : indexRampWeight x (N n) = 0 := IndexedCutoff.ramp.weight_zero_of_le hp hlt.le
  rw [hz, mul_zero]

private theorem archivedIndexRamp_parts (x : ℝ) :
    archivedGaussianPrimitiveIndexRamp x =
      2 * ((∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        archivedInertIndexWeight n 1 * indexRampWeight x (n + 1)) +
        (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 1 *
          indexRampWeight x (archivedInertTailIndex 1 1 pk)) +
        (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 2 *
          indexRampWeight x (archivedInertTailIndex 2 0 pk))) -
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight x n) +
      archivedGaussianPrimitiveIndexRamp 1 * x := by
  have hm (n : ℕ) : archivedInertIndexWeight n 1 * indexRampWeight 1 (n + 1) = 0 := by
    have hz : indexRampWeight 1 (n + 1) = 0 :=
      IndexedCutoff.ramp.weight_zero_of_le (Nat.succ_pos _) (by exact_mod_cast Nat.succ_pos n)
    rw [hz, mul_zero]
  have ht (f k : ℕ) (pk : Nat.Primes × ℕ) : archivedInertIndexWeight pk.1.val f *
      indexRampWeight 1 (archivedInertTailIndex f k pk) = 0 := by
    have hp := archivedInertTailIndex_pos f k pk
    have hz : indexRampWeight 1 (archivedInertTailIndex f k pk) = 0 :=
      IndexedCutoff.ramp.weight_zero_of_le hp (by exact_mod_cast hp)
    rw [hz, mul_zero]
  have hb (n : ℕ) : archivedIndexBaseWeight n * indexRampWeight 1 n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [archivedIndexBaseWeight]
    · have hz : indexRampWeight 1 n = 0 :=
        IndexedCutoff.ramp.weight_zero_of_le hn (by exact_mod_cast hn)
      rw [hz, mul_zero]
  unfold archivedGaussianPrimitiveIndexRamp
  change 2 * ((∑ n ∈ Finset.range (⌊x⌋₊ + 1), archivedInertIndexWeight n 1 *
      indexRampWeight x (n + 1)) + (∑' pk : Nat.Primes × ℕ, _) + (∑' pk : Nat.Primes × ℕ, _)) -
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight x n) -
      _ * x + 2 * x * _ = _ + (2 * ((∑ n ∈ Finset.range (⌊(1 : ℝ)⌋₊ + 1),
      archivedInertIndexWeight n 1 * indexRampWeight 1 (n + 1)) +
      (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 1 *
        indexRampWeight 1 (archivedInertTailIndex 1 1 pk)) +
      (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 2 *
        indexRampWeight 1 (archivedInertTailIndex 2 0 pk))) -
      (∑ n ∈ Finset.range (⌊(1 : ℝ)⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight 1 n) -
      _ * 1 + 2 * 1 * _) * x
  simp only [hm, ht, hb, Finset.sum_const_zero, tsum_zero]
  ring

set_option maxHeartbeats 500000 in
theorem gaussianIndexFamily_ramp {x : ℝ} (hx : 1 ≤ x) :
    indexedCutoffSum .ramp gaussianIndexCoefficient gaussianIndexAddress x =
      archivedGaussianPrimitiveIndexRamp x - archivedGaussianPrimitiveIndexRamp 1 := by
  let f : GaussianIndexFamily → ℝ :=
    fun i => gaussianIndexCoefficient i * IndexedCutoff.ramp.weight x (gaussianIndexAddress i)
  have h0 : HasSum (f ∘ Sum.inl) (archivedGaussianPrimitiveIndexRamp 1 * (x - 1)) := by
    change HasSum (fun _ : Unit => archivedGaussianPrimitiveIndexRamp 1 * indexRampWeight x 1) _
    rw [indexRampWeight, Nat.cast_one, div_one, max_eq_left (sub_nonneg.mpr hx)]
    simp
  have h1 : HasSum (fun n => f (.inr (.inl n)))
      (2 * ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        archivedInertIndexWeight n 1 * indexRampWeight x (n + 1)) := by
    simpa only [f, gaussianIndexCoefficient, gaussianIndexAddress, IndexedCutoff.weight, mul_assoc] using
      (indexFiniteRamp_hasSum (fun n => archivedInertIndexWeight n 1) (· + 1) Nat.le_succ
        (x := x)).mul_left (2 : ℝ)
  have h2 (t k : ℕ) (htk : t + k = 2) :
      HasSum (fun pk : Nat.Primes × ℕ => (2 * archivedInertIndexWeight pk.1.val t) *
          indexRampWeight x (archivedInertTailIndex t k pk))
        (2 * ∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val t *
          indexRampWeight x (archivedInertTailIndex t k pk)) := by
    have h := indexedCutoffSum_summable_at .ramp (fun pk : Nat.Primes × ℕ =>
      archivedInertIndexWeight pk.1.val t) (archivedInertTailIndex t k)
      (archivedInertTailIndex_pos t k) (a := 2) (by norm_num) hx (by
        simpa only [abs_of_nonneg (archivedInertIndexWeight_nonneg _ _)] using
          archivedInertTail_summable t k htk (θ := 2) (by norm_num))
    simpa only [IndexedCutoff.weight, mul_assoc] using h.hasSum.mul_left (2 : ℝ)
  have hb (n : ℕ) : f (.inr (.inr (.inr (.inr n)))) =
      -(archivedIndexBaseWeight n * indexRampWeight x n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [f, gaussianIndexCoefficient, archivedIndexBaseWeight]
    · simp [f, gaussianIndexCoefficient, gaussianIndexAddress, IndexedCutoff.weight,
        max_eq_right (show 1 ≤ n from hn)]
  have h3 : HasSum (fun n => f (.inr (.inr (.inr (.inr n)))))
      (-(∑ n ∈ Finset.range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight x n)) := by
    simpa only [hb, id_eq] using (indexFiniteRamp_hasSum archivedIndexBaseWeight id
      (fun _ => le_rfl) (x := x)).neg
  have h34 := HasSum.sum (f := fun i => f (.inr (.inr (.inr i)))) (h2 2 0 rfl) h3
  have h234 := HasSum.sum (f := fun i => f (.inr (.inr i))) (h2 1 1 rfl) h34
  have h1234 := HasSum.sum (f := fun i => f (.inr i)) h1 h234
  have hsum := HasSum.sum (f := f) h0 h1234
  change (∑' i, f i) = _
  rw [hsum.tsum_eq, archivedIndexRamp_parts x]
  ring

#print axioms gaussianIndexFamily_summable
#print axioms gaussianIndexFamily_ramp

end
end AlpogeSuperZeta
