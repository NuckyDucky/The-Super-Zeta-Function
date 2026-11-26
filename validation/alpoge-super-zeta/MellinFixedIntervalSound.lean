import MellinFixedInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Every calculation encloses the exact real operation, including negative divisions. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

def Contains (a : Box) (x : ℝ) : Prop :=
  (a.lo:ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ (a.hi:ℝ)

private theorem scale_int_pos : 0 < scale := by decide +kernel

theorem scale_pos : (0:ℝ) < scale := by exact_mod_cast scale_int_pos

private theorem floor_le (n : Int) {d : Int} (hd : 0 < d) :
    ((n/d:Int):ℝ) ≤ (n:ℝ)/(d:ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
  exact_mod_cast Int.ediv_mul_le n hd.ne'

private theorem le_ceiling (n : Int) {d : Int} (hd : 0 < d) :
    (n:ℝ)/(d:ℝ) ≤ (ceilDiv n d:ℝ) := by
  have h := floor_le (-n) hd
  simp only [ceilDiv, Int.cast_neg, neg_div]
  simpa only [Int.cast_neg, neg_div, neg_neg] using neg_le_neg h

theorem ratio_contains (n : Int) {d : Int} (hd : 0 < d) :
    Contains (fromRatio n d) ((n:ℝ)/(d:ℝ)) := by
  have h : ((n*scale:Int):ℝ)/(d:ℝ) = (scale:ℝ)*((n:ℝ)/(d:ℝ)) := by
    push_cast
    ring
  unfold Contains fromRatio
  rw [← h]
  exact ⟨floor_le _ hd, le_ceiling _ hd⟩

theorem constant_contains (n : Int) : Contains (constant n) (n:ℝ) := by
  simp [Contains, constant, mul_comm]

theorem add_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x+y) := by
  simpa only [Contains, add, Int.cast_add, mul_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem neg_contains {a : Box} {x : ℝ} (h : Contains a x) :
    Contains (neg a) (-x) := by
  simpa only [Contains, neg, Int.cast_neg, mul_neg] using
    And.intro (neg_le_neg h.2) (neg_le_neg h.1)

theorem sub_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (sub a b) (x-y) := by
  simpa only [sub, sub_eq_add_neg] using add_contains hx (neg_contains hy)

theorem widen_contains {a : Box} {x y : ℝ} {units : Nat} (h : Contains a x)
    (he : |y-x| ≤ (units:ℝ)/(scale:ℝ)) : Contains (widen a units) y := by
  obtain ⟨hl,hu⟩ := abs_le.mp he
  have hs : (scale:ℝ)*((units:ℝ)/(scale:ℝ)) = (units:ℝ) := by field_simp [scale_pos.ne']
  have hpl := mul_le_mul_of_nonneg_left hl scale_pos.le
  have hpu := mul_le_mul_of_nonneg_left hu scale_pos.le
  obtain ⟨ha,hb⟩ := h
  simp only [mul_neg, hs, mul_sub] at hpl hpu
  simp only [Contains, widen, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  exact ⟨by linarith only [ha,hpl], by linarith only [hb,hpu]⟩

theorem divInt_contains {a : Box} {x : ℝ} {d : Int} (h : Contains a x) (hd : 0 < d) :
    Contains (divInt a d) (x/(d:ℝ)) := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  unfold Contains divInt
  rw [← mul_div_assoc]
  exact ⟨(floor_le _ hd).trans (div_le_div_of_nonneg_right h.1 hd'.le),
    (div_le_div_of_nonneg_right h.2 hd'.le).trans (le_ceiling _ hd)⟩

private theorem one_side {a b x v l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : l ≤ v*a ∧ v*a ≤ u) (hb : l ≤ v*b ∧ v*b ≤ u) :
    l ≤ v*x ∧ v*x ≤ u := by
  by_cases hv : 0 ≤ v
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_left hx.1 hv),
      (mul_le_mul_of_nonneg_left hx.2 hv).trans hb.2⟩
  · exact ⟨hb.1.trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hv)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hv)).trans ha.2⟩

private theorem corners {a b c d x y l u : ℝ} (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hac : l ≤ a*c ∧ a*c ≤ u) (had : l ≤ a*d ∧ a*d ≤ u)
    (hbc : l ≤ b*c ∧ b*c ≤ u) (hbd : l ≤ b*d ∧ b*d ≤ u) :
    l ≤ x*y ∧ x*y ≤ u := by
  have hc := one_side hx (v := c) (by simpa only [mul_comm c a] using hac)
    (by simpa only [mul_comm c b] using hbc)
  have hd := one_side hx (v := d) (by simpa only [mul_comm d a] using had)
    (by simpa only [mul_comm d b] using hbd)
  exact one_side hy (by simpa only [mul_comm x c] using hc) (by simpa only [mul_comm x d] using hd)

theorem mul_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x*y) := by
  let ll := a.lo*b.lo
  let lh := a.lo*b.hi
  let hl := a.hi*b.lo
  let hh := a.hi*b.hi
  let l := min (min ll lh) (min hl hh)
  let u := max (max ll lh) (max hl hh)
  have hll : (l:ℝ) ≤ (a.lo:ℝ)*(b.lo:ℝ) ∧ (a.lo:ℝ)*(b.lo:ℝ) ≤ (u:ℝ) := by
    refine ⟨?_,?_⟩
    · exact_mod_cast (min_le_left (min ll lh) (min hl hh)).trans (min_le_left ll lh)
    · exact_mod_cast (le_max_left ll lh).trans (le_max_left (max ll lh) (max hl hh))
  have hlh : (l:ℝ) ≤ (a.lo:ℝ)*(b.hi:ℝ) ∧ (a.lo:ℝ)*(b.hi:ℝ) ≤ (u:ℝ) := by
    refine ⟨?_,?_⟩
    · exact_mod_cast (min_le_left (min ll lh) (min hl hh)).trans (min_le_right ll lh)
    · exact_mod_cast (le_max_right ll lh).trans (le_max_left (max ll lh) (max hl hh))
  have hhl : (l:ℝ) ≤ (a.hi:ℝ)*(b.lo:ℝ) ∧ (a.hi:ℝ)*(b.lo:ℝ) ≤ (u:ℝ) := by
    refine ⟨?_,?_⟩
    · exact_mod_cast (min_le_right (min ll lh) (min hl hh)).trans (min_le_left hl hh)
    · exact_mod_cast (le_max_left hl hh).trans (le_max_right (max ll lh) (max hl hh))
  have hhh : (l:ℝ) ≤ (a.hi:ℝ)*(b.hi:ℝ) ∧ (a.hi:ℝ)*(b.hi:ℝ) ≤ (u:ℝ) := by
    refine ⟨?_,?_⟩
    · exact_mod_cast (min_le_right (min ll lh) (min hl hh)).trans (min_le_right hl hh)
    · exact_mod_cast (le_max_right hl hh).trans (le_max_right (max ll lh) (max hl hh))
  obtain ⟨hL,hU⟩ := corners hx hy hll hlh hhl hhh
  have hcancel : ((scale:ℝ)*x*((scale:ℝ)*y))/(scale:ℝ) = (scale:ℝ)*(x*y) := by
    field_simp [scale_pos.ne']
    ring
  change ((l/scale:Int):ℝ) ≤ (scale:ℝ)*(x*y) ∧
    (scale:ℝ)*(x*y) ≤ (ceilDiv u scale:ℝ)
  rw [← hcancel]
  exact ⟨(floor_le _ scale_int_pos).trans (div_le_div_of_nonneg_right hL scale_pos.le),
    (div_le_div_of_nonneg_right hU scale_pos.le).trans (le_ceiling _ scale_int_pos)⟩

theorem nonnegative_contains {a : Box} {x : ℝ} (h : Contains a x) (hx : 0 ≤ x) :
    Contains (nonnegative a) x := by
  change ((max 0 a.lo:Int):ℝ) ≤ (scale:ℝ)*x ∧ (scale:ℝ)*x ≤ (a.hi:ℝ)
  rw [Int.cast_max, Int.cast_zero, max_le_iff]
  exact ⟨⟨mul_nonneg scale_pos.le hx,h.1⟩,h.2⟩

theorem divPositive_contains {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y)
    (ha : 0 ≤ a.lo) (hb : 0 < b.lo) : Contains (divPositive a b) (x/y) := by
  have ha' : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
  have hb' : (0:ℝ) < b.lo := by exact_mod_cast hb
  have hY := hb'.trans_le hy.1
  have hbhi : 0 < b.hi := by exact_mod_cast hY.trans_le hy.2
  have hcancel : ((scale:ℝ)*x*(scale:ℝ))/((scale:ℝ)*y) = (scale:ℝ)*(x/y) := by
    have hy' : 0 < y := pos_of_mul_pos_right hY scale_pos.le
    field_simp [hy'.ne', scale_pos.ne']
    ring
  change (((a.lo*scale)/b.hi:Int):ℝ) ≤ (scale:ℝ)*(x/y) ∧
    (scale:ℝ)*(x/y) ≤ (ceilDiv (a.hi*scale) b.lo:ℝ)
  rw [← hcancel]
  constructor
  · apply (floor_le _ hbhi).trans
    push_cast
    refine (div_le_div_of_nonneg_left (mul_nonneg ha' scale_pos.le) hY hy.2).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx.1 scale_pos.le) hY.le
  · apply le_trans _ (le_ceiling _ hb)
    push_cast
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx.2 scale_pos.le) hY.le).trans ?_
    have hnonneg : (0:ℝ) ≤ a.hi := ha'.trans (hx.1.trans hx.2)
    exact div_le_div_of_nonneg_left (mul_nonneg hnonneg scale_pos.le) hb' hy.1

theorem horner_contains {a : Box} {x : ℝ} (hx : Contains a x)
    (f : Nat → Box) (c : Nat → ℝ) (hc : ∀ k, Contains (f k) (c k)) (start n : Nat) :
    Contains (horner a (coefficients f start n))
      (∑ k ∈ Finset.range n, c (start+k)*x^k) := by
  induction n generalizing start with
  | zero =>
    simpa only [coefficients, horner, Finset.range_zero, Finset.sum_empty, Int.cast_zero] using constant_contains 0
  | succ n ih =>
    have hs := add_contains (hc start) (mul_contains hx (ih (start+1)))
    convert hs using 1
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [add_comm (c start)]
    refine congrArg (· + c start) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Nat.add_right_comm start 1 i, Nat.add_assoc, pow_succ]
    ring

theorem squareSteps_contains {a : Box} {x : ℝ} (h : Contains a x) (n : Nat) :
    Contains (squareSteps n a) (x^(2^n : Nat)) := by
  induction n with
  | zero => simpa only [squareSteps, pow_zero, pow_one] using h
  | succ n ih =>
    simpa only [squareSteps, pow_succ (2:Nat), pow_mul, pow_two (x^(2^n : Nat))]
      using mul_contains ih ih

theorem fitsSample_correct {a : Box} {target : Int} {x : ℝ}
    (h : Contains a x) (hc : fitsSample a target = true) :
    |x - (target:ℝ)/10^14| ≤ 1/10^14 := by
  have hd : (target-1)*10^10 ≤ a.lo ∧ a.hi ≤ (target+1)*10^10 := of_decide_eq_true hc
  have hl : (target:ℝ)*10^10-10^10 ≤ (a.lo:ℝ) := by
    have hr : (((target-1)*10^10:Int):ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast hd.1
    push_cast at hr
    linarith only [hr]
  have hu : (a.hi:ℝ) ≤ (target:ℝ)*10^10+10^10 := by
    have hr : (a.hi:ℝ) ≤ (((target+1)*10^10:Int):ℝ) := by exact_mod_cast hd.2
    push_cast at hr
    linarith only [hr]
  obtain ⟨hlo,hhi⟩ := h
  norm_num [scale] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hl,hlo],by linarith only [hu,hhi]⟩

#print axioms mul_contains
#print axioms divPositive_contains
#print axioms horner_contains
#print axioms fitsSample_correct

end DottieOriented.NativeSpectrum.MellinFixed
end
