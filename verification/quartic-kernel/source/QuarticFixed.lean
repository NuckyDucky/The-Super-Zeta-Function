import QuarticPointwise

namespace QuarticFixed

abbrev precision : ℕ := 10^28

private noncomputable def bound (a : ℕ) : ℝ := (a:ℝ)/precision

structure Box where
  lo : ℕ
  hi : ℕ
  deriving Repr

def Contains (b : Box) (x : ℝ) : Prop :=
  bound b.lo ≤ x ∧ x ≤ bound b.hi

theorem contains_lo {b : Box} {x : ℝ} (h : Contains b x) : (b.lo:ℝ)/precision ≤ x :=
  h.1

theorem contains_hi {b : Box} {x : ℝ} (h : Contains b x) : x ≤ (b.hi:ℝ)/precision :=
  h.2

private def rangePoly (y : ℚ) : ℚ :=
  ∑ i ∈ Finset.range 28, y^i / i.factorial

private def nearExp (q : ℚ) : ℚ × ℚ :=
  let p := rangePoly (q/64)
  (p^64, (p + 29/(28*(Nat.factorial 28 : ℚ)))^64)

private theorem nearExp_spec {q : ℚ} (hq : 0 ≤ q) (hq' : q ≤ 64) :
    0 < (nearExp q).1 ∧ ((nearExp q).1 : ℝ) ≤ Real.exp (q:ℝ) ∧
      Real.exp (q:ℝ) ≤ ((nearExp q).2 : ℝ) := by
  let y : ℝ := (q:ℝ)/64
  let p : ℝ := ∑ i ∈ Finset.range 28, y^i / i.factorial
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy' : y ≤ 1 := by
    have h : (q:ℝ) ≤ 64 := by exact_mod_cast hq'
    dsimp [y]
    linarith
  have hp : 1 ≤ p := by
    have h := Finset.single_le_sum (s := Finset.range 28)
      (f := fun i : ℕ => y^i / i.factorial)
      (fun i _ => div_nonneg (pow_nonneg hy _) (by positivity))
      (Finset.mem_range.mpr (by decide : (0:ℕ) < 28))
    simpa [p] using h
  have hLo : p ≤ Real.exp y := Real.sum_le_exp_of_nonneg hy 28
  have hHi : Real.exp y ≤ p + 29 / (28*(Nat.factorial 28:ℝ)) := by
    have h := Real.exp_bound' hy hy' (show 0 < (28:ℕ) by decide)
    have hp28 := pow_le_pow_left₀ hy hy' 28
    change Real.exp y ≤ p + y^28 * ((28:ℝ)+1) / ((Nat.factorial 28:ℝ)*28) at h
    calc
      _ ≤ _ := h
      _ ≤ p + 29 / (28*(Nat.factorial 28:ℝ)) := by
        rw [mul_comm (28:ℝ) (Nat.factorial 28:ℝ)]
        gcongr
        nlinarith only [hp28]
  have hcast : ((rangePoly (q/64) : ℚ):ℝ) = p := by
    simp [rangePoly, p, y, Rat.cast_sum]
  have hpow : Real.exp (q:ℝ) = Real.exp y^64 := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hh : (1:ℚ) ≤ rangePoly (q/64) := by
      exact_mod_cast (hcast.symm ▸ hp)
    exact pow_pos ((by norm_num : (0:ℚ) < 1).trans_le hh) _
  · change ((rangePoly (q/64)^64 : ℚ):ℝ) ≤ _
    rw [Rat.cast_pow, hcast, hpow]
    exact pow_le_pow_left₀ (by linarith) hLo _
  · change _ ≤ (((rangePoly (q/64) + 29/(28*(Nat.factorial 28:ℚ)))^64 : ℚ):ℝ)
    push_cast
    rw [hcast, hpow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hHi _

private def rounded (lo hi : ℚ) : Box :=
  ⟨⌊lo * precision⌋.toNat, ⌈hi * precision⌉.toNat⟩

private theorem rounded_spec {lo hi : ℚ} {x : ℝ} (hl : 0 ≤ lo) (hh : 0 ≤ hi)
    (hlo : (lo:ℝ) ≤ x) (hhi : x ≤ (hi:ℝ)) :
    Contains (rounded lo hi) x := by
  have pf : (0:ℚ) ≤ precision := by positivity
  have h₁ : 0 ≤ ⌊lo * precision⌋ := Int.floor_nonneg.mpr (mul_nonneg hl pf)
  have h₂ : 0 ≤ ⌈hi * precision⌉ := Int.ceil_nonneg (mul_nonneg hh pf)
  have hf := Int.floor_le (lo * precision)
  have hc := Int.le_ceil (hi * precision)
  have hf' : ((⌊lo * precision⌋:ℤ):ℝ) ≤ (lo:ℝ)*precision := by exact_mod_cast hf
  have hc' : (hi:ℝ)*precision ≤ ((⌈hi * precision⌉:ℤ):ℝ) := by exact_mod_cast hc
  constructor
  · change ((⌊lo * precision⌋.toNat:ℕ):ℝ)/precision ≤ x
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h₁]
    exact ((div_le_iff₀ (by positivity : (0:ℝ) < precision)).2 hf').trans hlo
  · change x ≤ ((⌈hi * precision⌉.toNat:ℕ):ℝ)/precision
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h₂]
    exact hhi.trans ((le_div_iff₀ (by positivity : (0:ℝ) < precision)).2 hc')

def expBox (q : ℚ) : Box :=
  let r := nearExp q
  rounded r.1 r.2

theorem expBox_spec {q : ℚ} (h₀ : 0 ≤ q) (h₁ : q ≤ 64) :
    Contains (expBox q) (Real.exp (q:ℝ)) := by
  obtain ⟨hp,hlo,hhi⟩ := nearExp_spec h₀ h₁
  exact rounded_spec hp.le (by exact_mod_cast (Real.exp_pos _).le.trans hhi) hlo hhi

def expNegBox (q : ℚ) : Box :=
  let r := nearExp q
  rounded r.2⁻¹ r.1⁻¹

theorem expNegBox_spec {q : ℚ} (h₀ : 0 ≤ q) (h₁ : q ≤ 64) :
    Contains (expNegBox q) (Real.exp (-(q:ℝ))) := by
  obtain ⟨hp,hlo,hhi⟩ := nearExp_spec h₀ h₁
  have hq : 0 < (nearExp q).2 := by exact_mod_cast (Real.exp_pos _).trans_le hhi
  rw [Real.exp_neg]
  apply rounded_spec (inv_nonneg.mpr hq.le) (inv_nonneg.mpr hp.le)
  · push_cast
    exact inv_anti₀ (Real.exp_pos _) hhi
  · push_cast
    exact inv_anti₀ (by exact_mod_cast hp) hlo

def times (a b : Box) : Box :=
  ⟨a.lo*b.lo / precision, (a.hi*b.hi + (precision-1)) / precision⟩

private theorem floor_product (m n : ℕ) :
    bound (m*n/precision) ≤ bound m * bound n := by
  have h : (m*n/precision)*precision ≤ m*n := Nat.div_mul_le_self _ _
  unfold bound
  have h' : ((m*n/precision : ℕ):ℝ)*precision ≤ (m:ℝ)*n := by exact_mod_cast h
  calc
    _ = (((m*n/precision:ℕ):ℝ)*precision)/((precision:ℝ)*precision) := by
      field_simp
      ring
    _ ≤ ((m:ℝ)*n)/((precision:ℝ)*precision) := by gcongr
    _ = _ := (div_mul_div_comm _ _ _ _).symm

private theorem ceil_product (m n : ℕ) :
    bound m * bound n ≤ bound ((m*n+(precision-1))/precision) := by
  let a := m*n+(precision-1)
  have hmod := Nat.mod_lt a (show 0 < precision by decide)
  have hdiv := Nat.mod_add_div a precision
  rw [Nat.mul_comm precision (a/precision)] at hdiv
  have h : m*n ≤ a/precision*precision := by
    change a % precision < precision at hmod
    have hh : m*n + (precision-1) = a := rfl
    omega
  have h' : (m:ℝ)*n ≤ ((a/precision:ℕ):ℝ)*precision := by exact_mod_cast h
  unfold bound
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < precision * precision)).mpr
  have hsub : ((a/precision:ℕ):ℝ)/precision*(precision*precision) =
      ((a/precision:ℕ):ℝ)*precision := by field_simp; ring
  rw [hsub]
  exact h'

private theorem times_spec {a b : Box} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (times a b) (x*y) := by
  have hn (m : ℕ) : 0 ≤ bound m := by unfold bound; positivity
  constructor
  · exact (floor_product _ _).trans (mul_le_mul hx.1 hy.1 (hn _) ((hn _).trans hx.1))
  · exact (mul_le_mul hx.2 hy.2 ((hn _).trans hy.1) (hn _)).trans (ceil_product _ _)

def powBox (b : Box) (depth n : ℕ) : Box :=
  match depth with
  | 0 => ⟨precision, precision⟩
  | k+1 =>
    if n = 0 then ⟨precision, precision⟩ else
      let h := powBox b k (n/2)
      let s := times h h
      if n % 2 = 0 then s else times s b

theorem powBox_spec {b : Box} {x : ℝ} (h : Contains b x) (d n : ℕ) (hn : n < 2^d) :
    Contains (powBox b d n) (x^n) := by
  have hunit : Contains ⟨precision, precision⟩ 1 := by norm_num [Contains,bound,precision]
  induction d generalizing n with
  | zero =>
    have hz : n = 0 := by simp at hn; omega
    simpa only [hz,powBox,pow_zero] using hunit
  | succ d ih =>
    by_cases hz : n = 0
    · simpa [powBox,hz] using hunit
    have hn' : n/2 < 2^d := by rw [pow_succ] at hn; omega
    have hh := ih (n/2) hn'
    have hs := times_spec hh hh
    have heb := Nat.mod_add_div n 2
    simp only [powBox, if_neg hz]
    split
    · rename_i he
      have hnEven : n=n/2+n/2 := by omega
      convert hs using 1
      rw [← pow_add, ← hnEven]
    · rename_i ho
      have hnOdd : n=n/2+n/2+1 := by omega
      convert times_spec hs h using 1
      rw [← pow_add, ← pow_succ, ← hnOdd]

#print axioms expBox_spec
#print axioms expNegBox_spec
#print axioms powBox_spec

end QuarticFixed
