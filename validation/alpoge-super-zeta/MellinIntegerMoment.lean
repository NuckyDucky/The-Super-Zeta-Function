import MellinIntegerArithmetic
import MellinRationalSum

/-! The integer block computation gives the exact rational Mellin moments. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinInteger

open SuperZeta.CauchyPanelQuadrature

def sampleReading (rows : ℕ → Block) (b : Bool) (i : ℕ) (j : Fin 25) : ℚ :=
  (sampleAt (rows (i/64) j.val) b (i%64) : ℚ)/10^14

def momentValue (numerator : Int) (k : Nat) : ℚ :=
  (numerator : ℚ)/(128*(weightDenominator : ℚ)*524288^k*k.factorial*10^14)

private theorem integerRule : ∀ j : Fin 25,
    node j = (nodeNumerators.getD j.val 0 : ℚ)/4096 ∧
    weight j = (weightNumerator j.val : ℚ)/weightDenominator := by
  decide +kernel

theorem coordinate_eq (i : ℕ) (j : Fin 25) :
    mellinPanelNode i j = (coordinateNumerator i j.val : ℚ)/524288 := by
  rw [mellinPanelNode, mellinPanelCenter, (integerRule j).1, coordinateNumerator]
  push_cast
  ring

private theorem sumN_eq (f : Nat → Int) (n : Nat) :
    sumN f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [sumN, Finset.sum_range_succ, ih]

private theorem scanColumn_eq (f : Nat → Sample → Int) (start : Nat) (column : Column) :
    scanColumn f start column =
      ∑ i ∈ Finset.range column.length, f (start+i) (column.getD i (0,0)) := by
  induction column generalizing start with
  | nil => simp [scanColumn]
  | cons head tail ih =>
    rw [scanColumn, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    rw [add_comm (f start head)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_right_comm start 1 i, Nat.add_assoc]

private theorem scannedMoment_eq (column : Column) (block j : Nat) (b : Bool) (k : Nat)
    (h : column.length = 64) : scannedMoment column block j b k = columnMoment column block j b k := by
  simp only [scannedMoment, scanColumn_eq, h, columnMoment, sumN_eq, sampleAt, Nat.zero_add]

private theorem sum_range_blocks (f : ℕ → Int) (blocks size : ℕ) :
    (∑ i ∈ Finset.range (blocks*size), f i) =
      ∑ B ∈ Finset.range blocks, ∑ i ∈ Finset.range size, f (B*size+i) := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

private def integerTerm (rows : ℕ → Block) (b : Bool) (k i j : Nat) : Int :=
  weightNumerator j * ((-2 * coordinateNumerator i j)^k * sampleAt (rows (i/64) j) b (i%64))

private theorem sum_rows_eq (rows : ℕ → Block) (b : Bool) (k : Nat) :
    sumN (fun B => rawMoment (rows B) B b k) 37 =
      ∑ i ∈ Finset.range 2368, ∑ j : Fin 25, integerTerm rows b k i j.val := by
  rw [sumN_eq, show (2368 : ℕ) = 37*64 by decide, sum_range_blocks]
  refine Finset.sum_congr rfl fun B _ => ?_
  simp only [rawMoment, columnMoment, sumN_eq, Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 64 := Finset.mem_range.mp hi
  have hdiv : (64*B+i)/64 = B := by
    rw [add_comm (64*B) i, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hi', zero_add]
  have hmod : (64*B+i)%64 = i := by
    rw [add_comm (64*B) i, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
  simp only [integerTerm, mul_comm B 64, hdiv, hmod]

private def rowDenominator (k : ℕ) : ℚ := (weightDenominator : ℚ)*524288^k*k.factorial*10^14

private theorem row_term_eq (rows : ℕ → Block) (b : Bool) (k i : Nat) (j : Fin 25) :
    weight j * ((-2*mellinPanelNode i j)^k/k.factorial) * sampleReading rows b i j =
      (integerTerm rows b k i j.val : ℚ)/rowDenominator k := by
  rw [(integerRule j).2, coordinate_eq, sampleReading, integerTerm, rowDenominator]
  push_cast
  rw [show (-2:ℚ)*((coordinateNumerator i j.val:ℚ)/524288) =
    (-2*(coordinateNumerator i j.val:ℚ))/524288 by ring, div_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem sample_moment_exact (rows : ℕ → Block) (b : Bool) (k : Nat) :
    rationalMellinMoment (sampleReading rows b) k =
      momentValue (sumN (fun B => rawMoment (rows B) B b k) 37) k := by
  rw [sum_rows_eq, momentValue, rationalMellinMoment]
  change (1/128)*∑ i ∈ Finset.range 2368, ∑ j : Fin 25,
      weight j * ((-2*mellinPanelNode i j)^k/k.factorial) * sampleReading rows b i j = _
  simp_rw [row_term_eq, div_eq_mul_inv, ← Finset.sum_mul]
  simp only [Int.cast_sum]
  rw [show (128:ℚ)*weightDenominator*524288^k*k.factorial*10^14 =
      128*rowDenominator k by unfold rowDenominator; ring, mul_inv]
  ring

set_option maxRecDepth 2000 in
theorem sample_moment_from_blocks (rows : ℕ → Block) (counts : ℕ → ℕ → Array Int)
    (totals : ℕ → Array Int)
    (h : ∀ B < 37, ∀ j < 25, checkedColumn (rows B j) (counts B j) B j = true)
    (hTotals : ∀ B < 37, checkedBlockTotals (counts B) (totals B) = true)
    (b : Bool) (k : Nat) (hk : k < 4) :
    rationalMellinMoment (sampleReading rows b) k =
      momentValue (sumN (fun B => reportedMoment (totals B) b k) 37) k := by
  rw [sample_moment_exact]
  have hb : sumN (fun B => rawMoment (rows B) B b k) 37 =
    sumN (fun B => reportedMoment (totals B) b k) 37 := by
    simp only [sumN_eq]
    refine Finset.sum_congr rfl fun B hB => ?_
    have hB' := Finset.mem_range.mp hB
    rw [← checkedBlockTotals_correct (hTotals B hB') b hk]
    simp only [rawMoment, weightedReported, sumN_eq]
    refine Finset.sum_congr rfl fun j hj => congrArg (weightNumerator j * ·) ?_
    have hcol := h B hB' j (Finset.mem_range.mp hj)
    rw [← scannedMoment_eq _ B j b k (checkedColumn_length hcol)]
    exact checkedColumn_correct hcol b hk
  rw [hb]

def totalValue (totals : ℕ → Array Int) (b : Bool) (k : ℕ) : ℚ :=
  momentValue (sumN (fun B => reportedMoment (totals B) b k) 37) k

#print axioms integerRule
#print axioms sample_moment_exact
#print axioms sample_moment_from_blocks

end DottieOriented.NativeSpectrum.MellinInteger
end
