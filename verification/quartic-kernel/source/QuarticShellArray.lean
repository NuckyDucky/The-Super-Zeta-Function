import QuarticWeightedCoefficients

namespace QuarticKernel

private def foldRange (step : Array ℤ → ℕ → Array ℤ) (n : ℕ) (xs : Array ℤ) : Array ℤ :=
  (List.range n).foldl step xs

private theorem foldRange_succ (step) (n : ℕ) (xs : Array ℤ) :
    foldRange step (n+1) xs = step (foldRange step n xs) n := by
  simp [foldRange, List.range_succ, List.foldl_append]

private def readCount (xs : Array ℤ) (k : ℕ) : ℤ :=
  xs[k]?.getD 0

private theorem foldRange_read {N k : ℕ} (step : Array ℤ → ℕ → Array ℤ)
    (changeCount : ℕ → ℤ) (xs : Array ℤ) (n : ℕ)
    (size_ok : xs.size = N+1)
    (step_ok : ∀ ys j, ys.size = N+1 →
      (step ys j).size = N+1 ∧ readCount (step ys j) k = readCount ys k + changeCount j) :
    (foldRange step n xs).size = N+1 ∧
      readCount (foldRange step n xs) k = readCount xs k + ∑ j ∈ Finset.range n, changeCount j := by
  induction n with
  | zero => simpa [foldRange] using size_ok
  | succ n ih =>
    rw [foldRange_succ, Finset.sum_range_succ]
    obtain ⟨hs, hv⟩ := step_ok _ n ih.1
    exact ⟨hs, by rw [hv, ih.2, add_assoc]⟩

private def increment (xs : Array ℤ) (i : ℕ) (value : ℤ) : Array ℤ :=
  xs.modify i (· + value)

private theorem increment_read {k : ℕ} (xs : Array ℤ) (i : ℕ) (value : ℤ)
    (hk : k < xs.size) :
    readCount (increment xs i value) k = readCount xs k + if i = k then value else 0 := by
  simp only [increment, readCount, Array.getElem?_modify, Array.getElem?_eq_getElem hk]
  split <;> simp

private def jacobiCache (p : ℕ) : Array ℤ :=
  Array.ofFn (fun i : Fin p => jacobiSym (i.val : ℤ) p)

private def cache41 : Array ℤ := jacobiCache 41
private def cache457 : Array ℤ := jacobiCache 457

private theorem cache_eq (p v : ℕ) (hp : 0 < p) :
    ((jacobiCache p)[v % p]?.getD 0) = jacobiSym (v:ℤ) p := by
  unfold jacobiCache
  rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact Nat.mod_lt _ hp),
    Option.getD_some, Array.getElem_ofFn, Int.natCast_emod, ← jacobiSym.mod_left]

private def fastReading (a b : ℕ) : ℤ :=
  cache41[(a+32*b) % 41]?.getD 0 * cache457[(a+109*b) % 457]?.getD 0 *
    jacobiSym ((a:ℤ)+516876951*b) 1414835497

private theorem fastReading_eq (a b : ℕ) : fastReading a b = evalMark a b := by
  have p₁ : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have p₂ : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  have p₃ : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩
  rw [evalMark_eq, fastReading, cache41, cache457, cache_eq 41 _ (by decide), cache_eq 457 _ (by decide)]
  simp only [SuperZeta.FieldWeights.conductorReading, jacobiSym.legendreSym.to_jacobiSym,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp only [mul_comm (32 : ℤ), mul_comm (109 : ℤ), mul_comm (516876951 : ℤ)]

private def scatterRow (N : ℕ) (xs : Array ℤ) (a : ℕ) : Array ℤ :=
  foldRange (fun ys b => increment ys ((a+1)^2+b^2) (fastReading (a+1) b))
    ((N-(a+1)^2).sqrt+1) xs

private def shellArray (N : ℕ) : Array ℤ :=
  foldRange (scatterRow N) N.sqrt (Array.replicate (N+1) 0)

private theorem scatterRow_read {N k : ℕ} (hk : k ≤ N) (xs : Array ℤ) (a : ℕ)
    (hs : xs.size = N+1) :
    (scatterRow N xs a).size = N+1 ∧ readCount (scatterRow N xs a) k =
      readCount xs k + ∑ b ∈ Finset.range ((N-(a+1)^2).sqrt+1),
        (if (a+1)^2+b^2 = k then evalMark (a+1) b else 0) := by
  apply foldRange_read _ _ _ _ hs
  intro ys b hys
  refine ⟨by simp [increment, hys], ?_⟩
  simpa only [fastReading_eq] using increment_read ys ((a+1)^2+b^2) (fastReading (a+1) b) (by omega : k < ys.size)

set_option maxHeartbeats 1200000 in
/-- Every executable slot agrees with the coefficient defined by the
quarter-lattice character sum. -/
theorem shellArray_reads_coeff {N k : ℕ} (hk : k ≤ N) :
    readCount (shellArray N) k = coeff k := by
  have h := foldRange_read (k := k) (scatterRow N)
    (fun a => ∑ b ∈ Finset.range ((N-(a+1)^2).sqrt+1),
      (if (a+1)^2+b^2 = k then evalMark (a+1) b else 0))
    (Array.replicate (N+1) 0) N.sqrt (by simp) (fun ys j hys => scatterRow_read hk ys j hys)
  have hzero : readCount (Array.replicate (N+1) 0) k = 0 := by
    have hlt : k < N+1 := by omega
    simp [readCount, Array.getElem?_replicate, hlt]
  rw [hzero, zero_add] at h
  let delta (j : ℕ) : ℤ := if j = k then 1 else 0
  have hweight := evalWeighted_eq N delta
  have hδ (j : ℕ) (v : ℤ) : v * delta j = (if j = k then v else 0) := by
    by_cases hj : j = k <;> simp [delta, hj]
  simp only [evalWeighted, hδ] at hweight
  have hmem : k ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  rw [Finset.sum_ite_eq', if_pos hmem] at hweight
  exact h.2.trans hweight

private def checkPrefixes (xs : Array ℤ) (start : ℕ) (acc : ℤ) : ℕ → Bool
  | 0 => true
  | count+1 =>
    let next := acc + readCount xs (start+1)
    if 1 ≤ next then checkPrefixes xs (start+1) next count else false

private theorem prefix_step (n : ℕ) :
    prefixSum (n+1) = prefixSum n + coeff (n+1) := Finset.sum_range_succ _ _

private theorem checkPrefixes_sound (N start count : ℕ) (hN : start+count ≤ N)
    (hc : checkPrefixes (shellArray N) start (prefixSum start) count = true) :
    ∀ j, start < j → j ≤ start+count → 1 ≤ prefixSum j := by
  induction count generalizing start with
  | zero => intro j hj hj'; omega
  | succ count ih =>
    have hnext : start+1 ≤ N := by omega
    simp only [checkPrefixes, shellArray_reads_coeff hnext, ← prefix_step] at hc
    split at hc
    · rename_i hpos
      intro j hj hcount
      by_cases he : j = start+1
      · simpa only [he] using hpos
      · exact ih (start+1) (by omega) hc j (by omega) (by omega)
    · contradiction

def prefixTest (N : ℕ) : Bool :=
  checkPrefixes (shellArray N) 0 0 N

theorem prefixTest_sound (N : ℕ) (h : prefixTest N = true) :
    ∀ j, 0 < j → j ≤ N → 1 ≤ prefixSum j := by
  have ht : checkPrefixes (shellArray N) 0 (prefixSum 0) N = true := by
    simpa [prefixSum] using h
  have hs := checkPrefixes_sound N 0 N (by omega) ht
  simpa using hs

/-- Each bin partitions a consecutive run of shell indices and records the
sum of the signed prefixes on that run. -/
structure ShellBin where
  width : ℕ
  weight : ℕ
  deriving Repr

def binCount : List ShellBin → ℕ
  | [] => 0
  | g :: gs => g.width + binCount gs

def BinsCorrect : ℕ → List ShellBin → Prop
  | _, [] => True
  | n, g :: gs =>
    0 < g.width ∧ (g.weight : ℤ) = ∑ i ∈ Finset.range g.width, prefixSum (n+i+1) ∧
      BinsCorrect (n+g.width) gs

private def scanBin (xs : Array ℤ) (i : ℕ) (s w : ℤ) : ℕ → ℤ × ℤ
  | 0 => (s,w)
  | l+1 =>
    let next := s + readCount xs (i+1)
    scanBin xs (i+1) next (w+next) l

private theorem scanBin_sound {N : ℕ} (i l : ℕ) (w : ℤ) (h : i+l ≤ N) :
    scanBin (shellArray N) i (prefixSum i) w l =
      (prefixSum (i+l), w + ∑ j ∈ Finset.range l, prefixSum (i+j+1)) := by
  induction l generalizing i w with
  | zero => simp [scanBin]
  | succ l ih =>
    have hh : i+1 ≤ N := by omega
    simp only [scanBin, shellArray_reads_coeff hh, ← prefix_step]
    rw [ih (i+1) _ (by omega), Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he (k : ℕ) : i+1+k+1=i+(k+1)+1 := by omega
    simp_rw [he]
    rw [show i+1+l = i+(l+1) by omega]
    congr 1
    abel

private def checkBins (xs : Array ℤ) (i : ℕ) (s : ℤ) : List ShellBin → Bool
  | [] => decide (s = 17505)
  | g :: gs =>
    let (next, w) := scanBin xs i s 0 g.width
    if 0 < g.width ∧ w = g.weight then checkBins xs (i+g.width) next gs else false

private theorem checkBins_sound {N : ℕ} (i : ℕ) (gs : List ShellBin) (h : i+binCount gs ≤ N)
    (hc : checkBins (shellArray N) i (prefixSum i) gs = true) :
    BinsCorrect i gs ∧ prefixSum (i+binCount gs) = 17505 := by
  induction gs generalizing i with
  | nil => simpa [checkBins, binCount, BinsCorrect] using hc
  | cons g gs ih =>
    have h₁ : i+g.width ≤ N := by simp only [binCount] at h; omega
    simp only [checkBins, scanBin_sound i g.width 0 h₁, zero_add] at hc
    split at hc
    · rename_i hg
      have h₂ : i+g.width+binCount gs ≤ N := by simpa [binCount, Nat.add_assoc] using h
      obtain ⟨hv, hp⟩ := ih (i+g.width) h₂ hc
      exact ⟨⟨hg.1,hg.2.symm,hv⟩, by simpa [binCount, Nat.add_assoc] using hp⟩
    · contradiction

/-- The last prefix is included as a width-one bin and checked by the
same exact sweep. -/
def shellTest (N : ℕ) (gs : List ShellBin) : Bool :=
  let xs := shellArray N
  checkPrefixes xs 0 0 N && checkBins xs 0 0 gs

theorem shellTest_sound (N : ℕ) (gs : List ShellBin) (hN : binCount gs ≤ N)
    (h : shellTest N gs = true) :
    (∀ j, 0 < j → j ≤ N → 1 ≤ prefixSum j) ∧
      BinsCorrect 0 gs ∧ prefixSum (binCount gs) = 17505 := by
  simp only [shellTest, Bool.and_eq_true] at h
  exact ⟨prefixTest_sound N h.1, by
    have hc : checkBins (shellArray N) 0 (prefixSum 0) gs = true := by
      simpa [prefixSum] using h.2
    simpa using checkBins_sound 0 gs (by simpa using hN) hc⟩

#print axioms shellArray_reads_coeff
#print axioms prefixTest_sound
#print axioms shellTest_sound

end QuarticKernel
