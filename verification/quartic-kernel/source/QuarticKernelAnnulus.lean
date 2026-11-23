import QuarticKernelCharacter
import QuarticWeightedCoefficients

namespace QuarticKernel

private def listSum {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) : M :=
  (List.range n).foldl (fun s k => s + f k) 0

private theorem listSum_eq {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    listSum n f = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [listSum]
  | succ n ih =>
    simpa [listSum, List.range_succ, List.foldl_append, Finset.sum_range_succ] using
      congrArg (· + f n) ih

private def splitSum {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ℕ → ℕ → ℕ → M
  | 0, start, n => if n = 0 then 0 else f start
  | d+1, start, n =>
    if n ≤ 1 then (if n = 0 then 0 else f start)
    else
      let k := n/2
      splitSum f d start k + splitSum f d (start+k) (n-k)

private theorem splitSum_eq {M : Type} [AddCommMonoid M] (f : ℕ → M)
    (d start n : ℕ) (hn : n ≤ 2^d) :
    splitSum f d start n = ∑ k ∈ Finset.range n, f (start+k) := by
  have small (a k : ℕ) (hk : k ≤ 1) :
      (if k = 0 then 0 else f a) = ∑ j ∈ Finset.range k, f (a+j) := by
    have hh : k = 0 ∨ k = 1 := by omega
    rcases hh with rfl | rfl <;> simp
  induction d generalizing start n with
  | zero =>
    rw [splitSum]
    exact small start n (by simpa using hn)
  | succ d ih =>
    rw [splitSum]
    split
    · exact small start _ ‹n ≤ 1›
    · rw [pow_succ] at hn
      dsimp only
      rw [ih start (n/2) (by omega), ih (start+n/2) (n-n/2) (by omega)]
      conv_rhs => rw [show n=n/2+(n-n/2) by omega, Finset.sum_range_add]
      simp only [Nat.add_assoc]

private def foldSum {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) : M :=
  if n ≤ 8192 then splitSum f 13 0 n else listSum n f

private theorem foldSum_eq {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    foldSum n f = ∑ k ∈ Finset.range n, f k := by
  unfold foldSum
  split
  · simpa only [Nat.zero_add] using splitSum_eq f 13 0 n ‹n ≤ 8192›
  · exact listSum_eq n f

private def sqrtDigits (n : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | d+1, a =>
    forceNat (a+2^d) fun b => if b*b ≤ n then sqrtDigits n d b else sqrtDigits n d a

private theorem sqrtDigits_eq (n d a : ℕ) (hlo : a ≤ n.sqrt) (hhi : n.sqrt < a+2^d) :
    sqrtDigits n d a = n.sqrt := by
  induction d generalizing a with
  | zero =>
    simp only [pow_zero] at hhi
    simpa only [sqrtDigits] using (show a = n.sqrt by omega)
  | succ d ih =>
    simp only [sqrtDigits,forceNat_eq,pow_succ]
    rw [pow_succ] at hhi
    split <;> rename_i h
    · exact ih _ (Nat.le_sqrt.mpr h) (by omega)
    · have hh : n.sqrt < a+2^d := Nat.lt_of_not_ge (fun t => h (Nat.le_sqrt.mp t))
      exact ih _ hlo hh

private def kernelSqrt (n : ℕ) : ℕ :=
  if n ≤ 33554432 then sqrtDigits n 13 0 else n.sqrt

private theorem kernelSqrt_eq (n : ℕ) : kernelSqrt n = n.sqrt := by
  unfold kernelSqrt
  split <;> rename_i hn
  · exact sqrtDigits_eq n 13 0 (Nat.zero_le _) (Nat.sqrt_lt.mpr (hn.trans_lt (by decide)))
  · rfl

private def squareNorm (a b : ℕ) : ℕ := (a+1)^2+b^2

private def rowStop (hi a : ℕ) : ℕ := kernelSqrt (hi-(a+1)^2)+1

private def rowStart (lo a : ℕ) : ℕ :=
  if (a+1)^2 ≤ lo then rowStop lo a else 0

private theorem rowStart_le (lo a b : ℕ) : rowStart lo a ≤ b ↔ lo < squareNorm a b := by
  unfold rowStart rowStop squareNorm
  simp only [kernelSqrt_eq]
  split <;> rename_i h
  · rw [Nat.succ_le_iff, Nat.sqrt_lt']
    omega
  · omega

private theorem rowStart_le_stop {lo hi a : ℕ} (h : lo ≤ hi) :
    rowStart lo a ≤ rowStop hi a := by
  unfold rowStart
  split
  · simp only [rowStop,kernelSqrt_eq]
    apply Nat.succ_le_succ
    exact Nat.sqrt_le_sqrt (Nat.sub_le_sub_right h _)
  · exact Nat.zero_le _

private def annulusFold {M : Type} [AddCommMonoid M] (lo hi : ℕ) (f : ℕ → ℕ → M) : M :=
  foldSum (kernelSqrt hi) fun a =>
    let start := rowStart lo a
    foldSum (rowStop hi a-start) fun i => f a (start+i)

private theorem annulusFold_eq {M : Type} [AddCommMonoid M] {lo hi : ℕ}
    (h : lo ≤ hi) (f : ℕ → ℕ → M) :
    annulusFold lo hi f = ∑ a ∈ Finset.range hi.sqrt, ∑ b ∈ Finset.range (rowStop hi a),
      if lo < squareNorm a b then f a b else 0 := by
  unfold annulusFold
  rw [foldSum_eq, kernelSqrt_eq]
  apply Finset.sum_congr rfl
  intro a _
  rw [foldSum_eq]
  conv_rhs => rw [show rowStop hi a = rowStart lo a + (rowStop hi a-rowStart lo a) by
    exact (Nat.add_sub_of_le (rowStart_le_stop h)).symm, Finset.sum_range_add]
  have hfirst : (∑ b ∈ Finset.range (rowStart lo a),
      if lo < squareNorm a b then f a b else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    exact if_neg (fun hb' => (Nat.not_le_of_lt (Finset.mem_range.mp hb)) ((rowStart_le lo a b).mpr hb'))
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro b _
  rw [if_pos ((rowStart_le lo a _).mp (Nat.le_add_right _ _))]

private theorem annulus_weight {lo hi : ℕ} (h : lo ≤ hi) (weight : ℕ → ℤ) :
    annulusFold lo hi (fun a b => kernelReading (a+1) b * weight (squareNorm a b)) =
      ∑ j ∈ Finset.range (hi-lo), coeff (lo+j+1) * weight (lo+j+1) := by
  rw [annulusFold_eq h]
  simp only [kernelReading_eq]
  have hL : (∑ a ∈ Finset.range hi.sqrt, ∑ b ∈ Finset.range (rowStop hi a),
       if lo < squareNorm a b then evalMark (a+1) b * weight (squareNorm a b) else 0) =
      evalWeighted hi (fun n => if lo < n then weight n else 0) := by
    unfold evalWeighted
    apply Finset.sum_congr rfl
    intro a _
    simp only [rowStop,kernelSqrt_eq]
    apply Finset.sum_congr rfl
    intro b _
    change (if lo < (a+1)^2+b^2 then evalMark (a+1) b * weight ((a+1)^2+b^2) else 0) =
      evalMark (a+1) b * (if lo < (a+1)^2+b^2 then weight ((a+1)^2+b^2) else 0)
    split <;> simp
  rw [hL,evalWeighted_eq]
  rw [show hi+1=lo+1+(hi-lo) by omega, Finset.sum_range_add]
  have hfirst : (∑ k ∈ Finset.range (lo+1), coeff k * (if lo < k then weight k else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hh := Finset.mem_range.mp hk
    simp [show ¬lo < k by omega]
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [if_pos (by omega), show lo+1+k=lo+k+1 by omega]

abbrev AnnulusStats := ℤ × ℤ × ℤ

def annulusStats (lo hi : ℕ) : AnnulusStats :=
  annulusFold lo hi fun a b =>
    forceInt (kernelReading (a+1) b) fun c =>
    (c, c * ((hi:ℤ)+1-(squareNorm a b:ℤ)), min c 0)

private theorem annulusFold_map {M N : Type} [AddCommMonoid M] [AddCommMonoid N]
    (H : M →+ N) (lo hi : ℕ) (f : ℕ → ℕ → M) :
    H (annulusFold lo hi f) = annulusFold lo hi (fun a b => H (f a b)) := by
  simp [annulusFold, foldSum_eq, map_sum]

private theorem annulusStats_proj (lo hi : ℕ) :
    let t := annulusStats lo hi
    t.1 = annulusFold lo hi (fun a b => kernelReading (a+1) b) ∧
    t.2.1 = annulusFold lo hi (fun a b => kernelReading (a+1) b *
      ((hi:ℤ)+1-(squareNorm a b:ℤ))) ∧
    t.2.2 = annulusFold lo hi (fun a b => min (kernelReading (a+1) b) 0) := by
  let f := fun a b =>
    let c := kernelReading (a+1) b
    (c, c * ((hi:ℤ)+1-(squareNorm a b:ℤ)), min c 0)
  let fst := AddMonoidHom.fst ℤ (ℤ×ℤ)
  let snd := AddMonoidHom.snd ℤ (ℤ×ℤ)
  have h : annulusStats lo hi = annulusFold lo hi f := by
    simp only [annulusStats,forceInt_eq,f]
  dsimp only
  rw [h]
  exact ⟨annulusFold_map fst lo hi f,
    annulusFold_map ((AddMonoidHom.fst ℤ ℤ).comp snd) lo hi f,
    annulusFold_map ((AddMonoidHom.snd ℤ ℤ).comp snd) lo hi f⟩

private theorem prefix_span (lo width : ℕ) :
    prefixSum (lo+width) = prefixSum lo + ∑ k ∈ Finset.range width, coeff (lo+k+1) := by
  rw [prefixSum, Finset.sum_range_add, prefixSum]

theorem annulusStats_final (lo hi : ℕ) (h : lo ≤ hi) :
    prefixSum hi = prefixSum lo + (annulusStats lo hi).1 := by
  have he := annulus_weight h (fun _ : ℕ => (1:ℤ))
  simp only [mul_one] at he
  rw [(annulusStats_proj lo hi).1, he]
  conv_lhs => rw [show hi = lo+(hi-lo) by omega, prefix_span]

theorem annulusStats_weighted (lo hi : ℕ) (h : lo ≤ hi) :
    (∑ j ∈ Finset.range (hi-lo), prefixSum (lo+j+1)) =
      ((hi-lo:ℕ):ℤ)*prefixSum lo+(annulusStats lo hi).2.1 := by
  rw [(annulusStats_proj lo hi).2.1, annulus_weight h (fun n => (hi:ℤ)+1-n),
    prefix_bin_weighted]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  push_cast [Nat.cast_sub h]
  ring

theorem annulusStats_prefix (lo hi j : ℕ) (hlo : lo ≤ j) (hhi : j ≤ hi) :
    prefixSum lo+(annulusStats lo hi).2.2 ≤ prefixSum j := by
  have h := hlo.trans hhi
  rw [show j = lo+(j-lo) by omega, prefix_span]
  apply add_le_add_left
  have hz : (∑ k ∈ Finset.range (hi-lo), coeff (lo+k+1) *
      (if lo+k+1 ≤ lo+(j-lo) then (1:ℤ) else 0)) =
      ∑ k ∈ Finset.range (j-lo), coeff (lo+k+1) := by
    rw [show hi-lo = (j-lo)+(hi-j) by omega, Finset.sum_range_add]
    have hfront : (∑ k ∈ Finset.range (j-lo), coeff (lo+k+1) *
        (if lo+k+1 ≤ lo+(j-lo) then (1:ℤ) else 0)) =
        ∑ k ∈ Finset.range (j-lo), coeff (lo+k+1) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hh := Finset.mem_range.mp hk
      simp [show lo+k+1 ≤ lo+(j-lo) by omega]
    have hend : (∑ k ∈ Finset.range (hi-j), coeff (lo+(j-lo+k)+1) *
        (if lo+(j-lo+k)+1 ≤ lo+(j-lo) then (1:ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [show ¬lo+(j-lo+k)+1 ≤ lo+(j-lo) by omega]
    rw [hfront,hend,add_zero]
  rw [← hz, ← annulus_weight h (fun n => if n ≤ lo+(j-lo) then (1:ℤ) else 0)]
  rw [(annulusStats_proj lo hi).2.2, annulusFold_eq h, annulusFold_eq h]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  split <;> rename_i hb
  · split
    · simpa only [mul_one] using min_le_left (kernelReading (a+1) b) (0:ℤ)
    · simpa only [mul_zero] using min_le_right (kernelReading (a+1) b) (0:ℤ)
  · exact le_rfl

#print axioms annulusStats_final
#print axioms annulusStats_weighted
#print axioms annulusStats_prefix

private def annulusPoints (lo hi : ℕ) : List (ℕ × ℕ) :=
  (List.range (kernelSqrt hi)).flatMap fun a =>
    let y := rowStart lo a
    (List.range (rowStop hi a-y)).map (fun j => (a+1,y+j))

private def sqrtDown (rad : ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => if (b+1)^2 ≤ rad then b+1 else sqrtDown rad b

private theorem sqrtDown_eq {rad top : ℕ} (h : rad.sqrt ≤ top) :
    sqrtDown rad top = rad.sqrt := by
  induction top with
  | zero => exact (Nat.eq_zero_of_le_zero h).symm
  | succ d ih =>
    unfold sqrtDown
    split <;> rename_i htest
    · exact Nat.le_antisymm (Nat.le_sqrt.mpr (by simpa [pow_two] using htest)) h
    · apply ih
      exact Nat.le_of_lt_succ (Nat.lt_of_not_ge (fun hle => htest (by
        simpa [pow_two] using Nat.le_sqrt.mp hle)))

private def annulusPointsSweep (lo hi : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, _, _, _ => []
  | n+1, a, prevL, prevH =>
    forceNat (a+1) fun coordinate =>
    let r := coordinate^2
    forceNat (sqrtDown (lo-r) prevL) fun limitL =>
    forceNat (sqrtDown (hi-r) prevH) fun limitH =>
    let y := if r ≤ lo then limitL+1 else 0
    (List.range (limitH+1-y)).map (fun j => (coordinate,y+j)) ++
      annulusPointsSweep lo hi n coordinate limitL limitH

private theorem annulusPointsSweep_eq (lo hi n a prevL prevH : ℕ)
    (hl : (lo-a^2).sqrt ≤ prevL) (hh : (hi-a^2).sqrt ≤ prevH) :
    annulusPointsSweep lo hi n a prevL prevH = (List.range n).flatMap (fun k =>
      let i := a+k
      let y := rowStart lo i
      (List.range (rowStop hi i-y)).map (fun j => (i+1,y+j))) := by
  induction n generalizing a prevL prevH with
  | zero => rfl
  | succ n ih =>
    have monotone (z : ℕ) : (z-(a+1)^2).sqrt ≤ (z-a^2).sqrt :=
      Nat.sqrt_le_sqrt (Nat.sub_le_sub_left (Nat.pow_le_pow_left (Nat.le_succ a) 2) z)
    simp only [annulusPointsSweep,forceNat_eq,sqrtDown_eq ((monotone lo).trans hl),
      sqrtDown_eq ((monotone hi).trans hh),List.range_succ_eq_map,List.flatMap_cons,
      List.flatMap_map,Function.comp_def,Nat.add_zero]
    rw [ih _ _ _ (Nat.le_refl _) (Nat.le_refl _)]
    have hadd (k : ℕ) : a+k.succ = a+1+k := by omega
    simp only [rowStart,rowStop,kernelSqrt_eq]
    congr 1
    apply congrArg (fun f => List.flatMap f (List.range n))
    funext k
    rw [hadd k]

private theorem sweep_from_origin (lo hi : ℕ) :
    annulusPointsSweep lo hi (kernelSqrt hi) 0 (kernelSqrt lo) (kernelSqrt hi) =
      annulusPoints lo hi := by
  rw [annulusPointsSweep_eq _ _ _ _ _ _ (by simp [kernelSqrt_eq]) (by simp [kernelSqrt_eq])]
  simp [annulusPoints]

private theorem sum_range_list {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.sum_append,Finset.sum_range_succ,ih]

private theorem sum_flatMap_points {α β M : Type} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons,List.sum_append,ih]

private def pointStats (hi a b : ℕ) (c : ℤ) : AnnulusStats :=
  (c, c*((hi:ℤ)+1-((a^2+b^2:ℕ):ℤ)), min c 0)

private theorem pack_pointStats (lo hi : ℕ) :
    ((annulusPoints lo hi).map fun p => pointStats hi p.1 p.2 (evalMark p.1 p.2)).sum =
      annulusStats lo hi := by
  unfold annulusPoints
  rw [sum_flatMap_points,sum_range_list]
  unfold annulusStats annulusFold
  rw [foldSum_eq]
  apply Finset.sum_congr rfl
  intro a _
  simp only [List.map_map]
  rw [sum_range_list, foldSum_eq]
  apply Finset.sum_congr rfl
  intro j _
  simp [pointStats,squareNorm,kernelReading_eq]

private def scanDirect (hi : ℕ) : List (ℕ × ℕ) → ℤ → ℤ → ℤ → AnnulusStats
  | [], t, m, n => (t,m,n)
  | (a,b)::ps, t, m, n =>
    forceInt (kernelReading a b) fun c =>
    forceInt (t+c) fun total =>
    forceInt (m+c*((hi:ℤ)+1-((a^2+b^2:ℕ):ℤ))) fun mass =>
    forceInt (n+min c 0) fun negative =>
    scanDirect hi ps total mass negative

private theorem scanDirect_eq (hi : ℕ) (ps : List (ℕ × ℕ)) (t m n : ℤ) :
    scanDirect hi ps t m n = (t,m,n) +
      ((ps.map fun z => pointStats hi z.1 z.2 (evalMark z.1 z.2)).sum) := by
  induction ps generalizing t m n with
  | nil => simp [scanDirect]
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    simp only [scanDirect,forceInt_eq,kernelReading_eq,ih,List.map_cons,List.sum_cons]
    let c := evalMark a b
    let d := c*((hi:ℤ)+1-((a^2+b^2:ℕ):ℤ))
    change (t+c,m+d,n+min c 0) + _ = (t,m,n) + (((c,d,min c 0) : AnnulusStats) + _)
    rw [← add_assoc]
    rfl

def sweepAnnulusStats (lo hi : ℕ) : AnnulusStats :=
  scanDirect hi (annulusPointsSweep lo hi (kernelSqrt hi) 0 (kernelSqrt lo) (kernelSqrt hi)) 0 0 0

theorem sweepAnnulusStats_eq (lo hi : ℕ) : sweepAnnulusStats lo hi = annulusStats lo hi := by
  rw [sweepAnnulusStats,sweep_from_origin,scanDirect_eq,pack_pointStats]
  exact zero_add _

#print axioms sweepAnnulusStats_eq

end QuarticKernel

