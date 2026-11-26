import GaussianSqrtTriangleWindow
import GaussianFrobeniusFactorial
import Mathlib.Data.Nat.Choose.Bounds

/-! The square-root row width makes all retained primes safe for
factorial division and bounds the excess over the leading row height. -/

namespace AlpogeSuperZeta

open Finset

noncomputable section

def gaussianSqrtJetCount (x : ℝ) : ℕ := ⌈x ^ (1 / 2 : ℝ)⌉₊

private theorem sqrtRpow_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

theorem gaussianSqrtJetCount_eq_triangleOrder {x : ℝ} (hx : 0 < x) :
    gaussianSqrtJetCount x = ⌈2 * x / gaussianSqrtTriangleScale x⌉₊ := by
  have hv : 0 < x ^ (1 / 2 : ℝ) := by positivity
  have he : 2 * x / gaussianSqrtTriangleScale x = x ^ (1 / 2 : ℝ) := by
    unfold gaussianSqrtTriangleScale
    apply (div_eq_iff (by positivity : (2 * x ^ (1 / 2 : ℝ)) ≠ 0)).mpr
    nlinarith [sqrtRpow_sq hx.le]
  rw [he, gaussianSqrtJetCount]

theorem frobeniusJet_orders_lt_iff {x k : ℝ} (hk : 0 < k) (p : ℕ) :
    (∀ j : ℕ, j < ⌈2 * x / k⌉₊ → j < p) ↔ 2 * x ≤ k * (p : ℝ) := by
  constructor
  · intro h
    by_contra! hBad
    have hlt : (p : ℝ) < 2 * x / k :=
      (lt_div_iff₀ hk).mpr (by simpa only [mul_comm] using hBad)
    exact (lt_irrefl p) (h p (Nat.lt_ceil.mpr hlt))
  · intro hb j hj
    have hlt : (j : ℝ) < 2 * x / k := Nat.lt_ceil.mp hj
    have hp : 2 * x / k ≤ (p : ℝ) := (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hb)
    exact_mod_cast hlt.trans_le hp

/-- The threshold is exact using only integrality and the lower cutoff on
the retained addresses. For an actual prime set it suffices to test its least member. -/
theorem frobeniusTriangle_retainedSupport_iff {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) :
    (∀ p : ℕ, k ≤ (p : ℝ) →
      (∀ j : ℕ, j < ⌈2 * x / k⌉₊ → j < p) ∧
      (∀ r s : ℕ, (r : ℝ) + k * (s : ℝ) < x → s < p)) ↔
      2 * x ≤ k * (⌈k⌉₊ : ℝ) := by
  constructor
  · intro h
    exact (frobeniusJet_orders_lt_iff hk ⌈k⌉₊).mp (h _ (Nat.le_ceil k)).1
  · intro h p hp
    have hceil : ⌈k⌉₊ ≤ p := Nat.ceil_le.mpr hp
    have hProduct : 2 * x ≤ k * (p : ℝ) :=
      h.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hceil) hk.le)
    refine ⟨(frobeniusJet_orders_lt_iff hk p).mpr hProduct, fun r s hs => ?_⟩
    by_contra! hps
    have hMul := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hps) hk.le
    linarith [Nat.cast_nonneg (α := ℝ) r]

theorem gaussianSqrtJet_order_lt_retainedPrime {x : ℝ}
    {p j : ℕ} (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hj : j < gaussianSqrtJetCount x) : j < p := by
  have hJ : (j : ℝ) < x ^ (1 / 2 : ℝ) := Nat.lt_ceil.mp hj
  have hScale : x ^ (1 / 2 : ℝ) ≤ gaussianSqrtTriangleScale x := by
    dsimp [gaussianSqrtTriangleScale]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  exact_mod_cast (hJ.trans_le (hScale.trans hp))

/-- A retained prime cannot produce the row Y^p in the row triangle. -/
theorem gaussianSqrtTriangle_no_Yp {x : ℝ} (hx : 0 < x) {p : ℕ}
    (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ)) :
    x ≤ gaussianSqrtTriangleScale x * (p : ℝ) := by
  let k := gaussianSqrtTriangleScale x
  have hk₀ : 0 ≤ k := by dsimp [k, gaussianSqrtTriangleScale]; positivity
  have hk : k * k = 4 * x := by
    dsimp [k, gaussianSqrtTriangleScale]
    nlinarith [sqrtRpow_sq hx.le]
  have h := mul_le_mul_of_nonneg_left hp hk₀
  change k * k ≤ k * (p : ℝ) at h
  linarith

theorem gaussianSqrtTriangle_scaledRowCount_le {x : ℝ} (hx : 2 ≤ x) :
    let k := gaussianSqrtTriangleScale x
    (2 * k / x ^ 2) * (frobeniusTriangleRows k x : ℝ) ≤ 8 := by
  let k := gaussianSqrtTriangleScale x
  have hx₀ : 0 < x := by linarith
  have hk₀ : 0 < k := by dsimp [k, gaussianSqrtTriangleScale]; positivity
  have hkx : k ≤ 2 * x := by
    dsimp [k, gaussianSqrtTriangleScale]
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h
    linarith
  have h₁ : 2 * k / x ≤ 4 := (div_le_iff₀ hx₀).mpr (by linarith)
  have h₂ : 2 / x ≤ 1 := (div_le_iff₀ hx₀).mpr (by linarith)
  have h₃ : 2 * k / x ^ 2 ≤ 2 := (div_le_iff₀ (by positivity : 0 < x ^ 2)).mpr
    (by nlinarith [mul_nonneg hx₀.le (sub_nonneg.mpr hx)])
  have hRows : (frobeniusTriangleRows k x : ℝ) ≤ x ^ 2 / (2 * k) + x + x / k + 1 := by
    linarith [(frobeniusTriangleRows_error hk₀ hx₀).2]
  change (2 * k / x ^ 2) * (frobeniusTriangleRows k x : ℝ) ≤ 8
  calc
    _ ≤ (2 * k / x ^ 2) * (x ^ 2 / (2 * k) + x + x / k + 1) :=
      mul_le_mul_of_nonneg_left hRows (by positivity)
    _ = 1 + 2 * k / x + 2 / x + 2 * k / x ^ 2 := by field_simp
    _ ≤ 8 := by linarith

/-- A rectangular array of the allowed jets needs a linear supply of nodes. -/
theorem gaussianSqrtTriangle_nodes_lower {x : ℝ} (hx : 2 ≤ x) {nodes : ℕ}
    (hCapacity : frobeniusTriangleRows (gaussianSqrtTriangleScale x) x ≤
      nodes * gaussianSqrtJetCount x) : x ≤ 8 * (nodes : ℝ) := by
  let v := x ^ (1 / 2 : ℝ)
  let k := gaussianSqrtTriangleScale x
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hv := Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hv₀ : 0 < v := by dsimp [v]; positivity
  have hk₀ : 0 < k := by dsimp [k, gaussianSqrtTriangleScale]; positivity
  have hSquare : v ^ 2 = x := sqrtRpow_sq hx₀.le
  have hJ : (gaussianSqrtJetCount x : ℝ) ≤ 2 * v := by
    have hc := Nat.ceil_lt_add_one hv₀.le
    change (⌈v⌉₊ : ℝ) ≤ 2 * v
    linarith
  have hRows : x ^ 2 / (4 * v) ≤ (frobeniusTriangleRows k x : ℝ) := by
    have h := (frobeniusTriangleRows_error hk₀ hx₀).1
    have hEq : 2 * k = 4 * v := by dsimp [k, v, gaussianSqrtTriangleScale]; ring
    rwa [hEq, sub_nonneg] at h
  have hm : (frobeniusTriangleRows k x : ℝ) ≤ (nodes : ℝ) * (gaussianSqrtJetCount x : ℝ) :=
    by exact_mod_cast hCapacity
  have hb : x ^ 2 / (4 * v) ≤ (nodes : ℝ) * (2 * v) :=
    hRows.trans (hm.trans (mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)))
  have hc := (div_le_iff₀ (show 0 < 4 * v by positivity)).mp hb
  have he : (nodes : ℝ) * (2 * v) * (4 * v) = (8 * (nodes : ℝ)) * x := by
    calc
      _ = (8 * (nodes : ℝ)) * v ^ 2 := by ring
      _ = _ := by rw [hSquare]
  rw [he, pow_two] at hc
  exact le_of_mul_le_mul_right hc hx₀

/-- At p = 1 the floor sum is the sum of the first exponents of all rows. -/
theorem gaussianSqrtTriangle_scaledFirstDegree_error {x : ℝ} (hx : 2 ≤ x) :
    let k := gaussianSqrtTriangleScale x
    |(2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k 1 : ℝ) - x / 3| ≤
      10 * x ^ (1 / 2 : ℝ) := by
  let v := x ^ (1 / 2 : ℝ)
  let k := gaussianSqrtTriangleScale x
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hv : 1 ≤ v := Real.one_le_rpow hx₁ (by norm_num)
  have hk : 1 ≤ k := by dsimp [k, gaussianSqrtTriangleScale]; change (1 : ℝ) ≤ 2 * v; linarith
  let V := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k 1 : ℝ)
  let S := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * 1)
  have hD : 0 ≤ V - S ∧ V - S ≤ 5 * k := by
    simpa only [Nat.cast_one, div_one] using
      (frobeniusTriangleDivisibility_error_le_scale hx hk (p := 1) Nat.one_pos)
  have hR : 0 ≤ x / 3 - S ∧ x / 3 - S ≤ 1 := by
    simpa only [S, Nat.cast_one, mul_one] using (squaredRampMultiples_rounding hx₀ (p := 1) Nat.one_pos)
  change |V - x / 3| ≤ 10 * v
  have hkEq : k = 2 * v := rfl
  rw [abs_le]
  constructor <;> linarith [hD.1, hD.2, hR.1, hR.2]

private theorem sqrtHasseEntry_norm_le {x H : ℝ} (hx : 2 ≤ x) (hH : 1 ≤ H)
    {r s j : ℕ} (hdeg : (r : ℝ) + gaussianSqrtTriangleScale x * (s : ℝ) < x)
    (hj : j < gaussianSqrtJetCount x) {z w : ℂ} (hz : ‖z‖ ≤ H) (hw : ‖w‖ ≤ H) :
    ‖monomialJet r j z * w ^ s‖ ≤
      Real.exp ((r : ℝ) * Real.log H + x ^ (1 / 2 : ℝ) * Real.log x +
        (x ^ (1 / 2 : ℝ) / 2) * Real.log H) := by
  let v := x ^ (1 / 2 : ℝ)
  have hx₀ : 0 < x := by linarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hH₀ := one_pos.trans_le hH
  have hr : (r : ℝ) ≤ x := by
    have hh : 0 ≤ gaussianSqrtTriangleScale x * (s : ℝ) := by
      unfold gaussianSqrtTriangleScale
      positivity
    linarith
  have hs : (s : ℝ) ≤ v / 2 := by
    have he : (2 * v) * (v / 2) = x := by nlinarith [sqrtRpow_sq hx₀.le]
    apply le_of_lt
    apply lt_of_mul_lt_mul_left _ (show 0 ≤ 2 * v by positivity)
    rw [he]
    change (r : ℝ) + (2 * v) * (s : ℝ) < x at hdeg
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hJ : (j : ℝ) ≤ v := (Nat.lt_ceil.mp hj).le
  have hChoose : (r.choose j : ℝ) ≤ x ^ v := by
    calc
      _ ≤ (r : ℝ) ^ j := by exact_mod_cast Nat.choose_le_pow r j
      _ ≤ x ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hr _
      _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hJ
  have hZ : ‖z‖ ^ (r - j) ≤ H ^ r :=
    (pow_le_pow_left₀ (norm_nonneg _) hz _).trans (pow_le_pow_right₀ hH (Nat.sub_le _ _))
  have hW : ‖w‖ ^ s ≤ H ^ (v / 2) := by
    rw [← Real.rpow_natCast ‖w‖ s]
    exact (Real.rpow_le_rpow (norm_nonneg _) hw (Nat.cast_nonneg _)).trans
      (Real.rpow_le_rpow_of_exponent_le hH hs)
  simp only [monomialJet, Complex.norm_mul, Complex.norm_natCast, Complex.norm_pow]
  calc
    _ ≤ (x ^ v * H ^ r) * H ^ (v / 2) :=
      mul_le_mul (mul_le_mul hChoose hZ (by positivity) (by positivity)) hW (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast H r, Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hH₀ (r : ℝ),
        Real.rpow_def_of_pos hH₀ (v / 2), ← Real.exp_add, ← Real.exp_add]
      congr 1
      change Real.log x * v + Real.log H * (r : ℝ) + Real.log H * (v / 2) =
        (r : ℝ) * Real.log H + v * Real.log x + (v / 2) * Real.log H
      ring

/-- A Leibniz bound at one embedding, with the first-row exponents retained exactly. -/
theorem sqrtHasseMinor_norm_le {Rows : Type*} [Fintype Rows] [DecidableEq Rows]
    {x H : ℝ} (hx : 2 ≤ x) (hH : 1 ≤ H) (degree : Rows → ℕ × ℕ)
    (order : Rows → ℕ) (z w : Rows → ℂ)
    (hdeg : ∀ r, ((degree r).1 : ℝ) + gaussianSqrtTriangleScale x * ((degree r).2 : ℝ) < x)
    (hj : ∀ c, order c < gaussianSqrtJetCount x) (hz : ∀ c, ‖z c‖ ≤ H) (hw : ∀ c, ‖w c‖ ≤ H) :
    ‖(Matrix.of fun r c => monomialJet (degree r).1 (order c) (z c) * w c ^ (degree r).2).det‖ ≤
      ((Fintype.card Rows).factorial : ℝ) * Real.exp
        ((∑ r, ((degree r).1 : ℝ)) * Real.log H +
          (Fintype.card Rows : ℝ) *
            (x ^ (1 / 2 : ℝ) * Real.log x + (x ^ (1 / 2 : ℝ) / 2) * Real.log H)) := by
  let A := Matrix.of fun r c => monomialJet (degree r).1 (order c) (z c) * w c ^ (degree r).2
  let v := x ^ (1 / 2 : ℝ)
  let L := v * Real.log x + (v / 2) * Real.log H
  let U := ∑ r, ((degree r).1 : ℝ)
  let E := Real.exp (U * Real.log H + (Fintype.card Rows : ℝ) * L)
  have hEntry (r c : Rows) : ‖A r c‖ ≤ Real.exp (((degree r).1 : ℝ) * Real.log H + L) := by
    simpa only [A, Matrix.of_apply, L, v, ← add_assoc] using
      sqrtHasseEntry_norm_le hx hH (hdeg r) (hj c) (hz c) (hw c)
  have hTerm (σ : Equiv.Perm Rows) : ‖∏ c, A (σ c) c‖ ≤ E := by
    rw [Complex.norm_prod]
    calc
      _ ≤ ∏ c, Real.exp (((degree (σ c)).1 : ℝ) * Real.log H + L) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun c _ => hEntry (σ c) c)
      _ = E := by
        rw [← Real.exp_sum, sum_add_distrib, ← sum_mul]
        have he : (∑ c, ((degree (σ c)).1 : ℝ)) = U := Equiv.sum_comp σ (fun r => ((degree r).1 : ℝ))
        simp [he, E]
  have hSign (σ : Equiv.Perm Rows) : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
  change ‖A.det‖ ≤ ((Fintype.card Rows).factorial : ℝ) * E
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm Rows, ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ c, A (σ c) c‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm Rows, E := by
      apply sum_le_sum
      intro σ _
      rw [Complex.norm_mul, hSign, one_mul]
      exact hTerm σ
    _ = _ := by simp [Fintype.card_perm]

theorem sqrtHasseMinor_normalizedLog_le {Rows : Type*} [Fintype Rows] [DecidableEq Rows]
    {x H C : ℝ} (hx : 2 ≤ x) (hH : 1 ≤ H) (hHlog : Real.log H ≤ C * Real.log x)
    (degree : Rows → ℕ × ℕ) (order : Rows → ℕ) (z w : Rows → ℂ)
    (hdeg : ∀ r, ((degree r).1 : ℝ) + gaussianSqrtTriangleScale x * ((degree r).2 : ℝ) < x)
    (hj : ∀ c, order c < gaussianSqrtJetCount x) (hz : ∀ c, ‖z c‖ ≤ H) (hw : ∀ c, ‖w c‖ ≤ H)
    (hCard : Fintype.card Rows ≤ frobeniusTriangleRows (gaussianSqrtTriangleScale x) x)
    (hDet : (Matrix.of fun r c => monomialJet (degree r).1 (order c) (z c) * w c ^ (degree r).2).det ≠ 0) :
    let scale := 2 * gaussianSqrtTriangleScale x / x ^ 2
    scale * Real.log ‖(Matrix.of fun r c => monomialJet (degree r).1 (order c) (z c) * w c ^ (degree r).2).det‖ ≤
      (scale * ∑ r, ((degree r).1 : ℝ)) * Real.log H +
        (40 + 4 * C) * x ^ (1 / 2 : ℝ) * Real.log x := by
  let k := gaussianSqrtTriangleScale x
  let v := x ^ (1 / 2 : ℝ)
  let scale := 2 * k / x ^ 2
  let m := Fintype.card Rows
  let U := ∑ r, ((degree r).1 : ℝ)
  let L := v * Real.log x + (v / 2) * Real.log H
  let D := (Matrix.of fun r c => monomialJet (degree r).1 (order c) (z c) * w c ^ (degree r).2).det
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hLogX := Real.log_nonneg hx₁
  have hLogH := Real.log_nonneg hH
  have hv : 1 ≤ v := Real.one_le_rpow hx₁ (by norm_num)
  have hk : 1 ≤ k := by change (1 : ℝ) ≤ 2 * v; linarith
  have hScale : 0 ≤ scale := by dsimp [scale]; positivity
  have hLM : scale * (m : ℝ) ≤ 8 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hCard) hScale).trans (gaussianSqrtTriangle_scaledRowCount_le hx)
  have hM : (m : ℝ) ≤ 4 * x ^ 2 := by
    change 2 * k / x ^ 2 * (m : ℝ) ≤ 8 at hLM
    have he : 2 * k / x ^ 2 * (m : ℝ) = (2 * k * (m : ℝ)) / x ^ 2 := by ring
    rw [he, div_le_iff₀ (by positivity : 0 < x ^ 2)] at hLM
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (Nat.cast_nonneg (α := ℝ) m)]
  have hmLog : Real.log (m : ℝ) ≤ 4 * Real.log x := by
    by_cases hm : m = 0
    · rw [hm, Nat.cast_zero, Real.log_zero]
      positivity
    · have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
      have h4 : (4 : ℝ) ≤ x ^ 2 := by nlinarith
      have hmpow : (m : ℝ) ≤ x ^ 4 := by
        calc
          _ ≤ 4 * x ^ 2 := hM
          _ ≤ x ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = _ := by ring
      simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hm₀ hmpow
  have hmFact : Real.log (m.factorial : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) := by
    have hm₀ : (0 : ℝ) < m.factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    simpa only [Nat.cast_pow, Real.log_pow] using
      Real.log_le_log hm₀ (show (m.factorial : ℝ) ≤ ((m ^ m : ℕ) : ℝ) by exact_mod_cast m.factorial_le_pow)
  have hLL : Real.log (m : ℝ) + L ≤ (5 + C / 2) * v * Real.log x := by
    have hCompare := mul_le_mul_of_nonneg_left hHlog (show 0 ≤ v / 2 by positivity)
    dsimp [L]
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) hLogX]
  have hMain : Real.log ‖D‖ ≤
      Real.log (m.factorial : ℝ) + U * Real.log H + (m : ℝ) * L := by
    have hNorm : 0 < ‖D‖ := norm_pos_iff.mpr hDet
    have hEstimate : ‖D‖ ≤ (m.factorial : ℝ) * Real.exp (U * Real.log H + (m : ℝ) * L) :=
      sqrtHasseMinor_norm_le hx hH degree order z w hdeg hj hz hw
    have hh := Real.log_le_log hNorm hEstimate
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hh
    linarith
  change scale * Real.log ‖D‖ ≤ scale * U * Real.log H + (40 + 4 * C) * v * Real.log x
  calc
    _ ≤ scale * (Real.log (m.factorial : ℝ) + U * Real.log H + (m : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hMain hScale
    _ ≤ scale * U * Real.log H + (scale * (m : ℝ)) * (Real.log (m : ℝ) + L) := by
      have hs := mul_le_mul_of_nonneg_left hmFact hScale
      linarith
    _ ≤ scale * U * Real.log H + (8 : ℝ) * ((5 + C / 2) * v * Real.log x) := by
      have hs := mul_le_mul hLM hLL (add_nonneg (Real.log_natCast_nonneg _) (by dsimp [L]; positivity))
        (by norm_num : (0 : ℝ) ≤ 8)
      linarith
    _ = _ := by ring

abbrev FrobeniusTriangleRow (x k : ℝ) :=
  Σ s : Fin ⌈x / k⌉₊, Fin ⌈x - k * (s.val : ℝ)⌉₊

def frobeniusTriangleDegree {x k : ℝ} (row : FrobeniusTriangleRow x k) : ℕ × ℕ :=
  (row.2.val, row.1.val)

theorem frobeniusTriangleRow_card (x k : ℝ) :
    Fintype.card (FrobeniusTriangleRow x k) = frobeniusTriangleRows k x := by
  simp [FrobeniusTriangleRow, frobeniusTriangleRows]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => ⌈x - k * (s : ℝ)⌉₊) _

theorem frobeniusTriangleRow_firstDegree (x k : ℝ) :
    (∑ r : FrobeniusTriangleRow x k, ((frobeniusTriangleDegree r).1 : ℝ)) =
      (frobeniusTriangleDivisibility x k 1 : ℝ) := by
  simp [frobeniusTriangleDegree, Fintype.sum_sigma, Fin.sum_univ_eq_sum_range,
    frobeniusTriangleDivisibility, Nat.cast_sum]
  exact Fin.sum_univ_eq_sum_range
    (fun s : ℕ => ∑ r ∈ range ⌈x - k * (s : ℝ)⌉₊, (r : ℝ)) _

theorem sqrtHasseTriangle_normalizedLog_le {x H C : ℝ} (hx : 2 ≤ x) (hH : 1 ≤ H)
    (hHlog : Real.log H ≤ C * Real.log x)
    (order : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → ℕ)
    (z w : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → ℂ)
    (hj : ∀ c, order c < gaussianSqrtJetCount x)
    (hz : ∀ c, ‖z c‖ ≤ H) (hw : ∀ c, ‖w c‖ ≤ H)
    (hDet : (Matrix.of fun r c =>
      monomialJet (frobeniusTriangleDegree r).1 (order c) (z c) * w c ^ (frobeniusTriangleDegree r).2).det ≠ 0) :
    (2 * gaussianSqrtTriangleScale x / x ^ 2) *
        Real.log ‖(Matrix.of fun r c =>
          monomialJet (frobeniusTriangleDegree r).1 (order c) (z c) * w c ^ (frobeniusTriangleDegree r).2).det‖ ≤
      (x / 3) * Real.log H + (40 + 14 * C) * x ^ (1 / 2 : ℝ) * Real.log x := by
  let k := gaussianSqrtTriangleScale x
  let s := 2 * k / x ^ 2
  let v := x ^ (1 / 2 : ℝ)
  have hRows (r : FrobeniusTriangleRow x k) :
      ((frobeniusTriangleDegree r).1 : ℝ) + k * ((frobeniusTriangleDegree r).2 : ℝ) < x := by
    have h := Nat.lt_ceil.mp r.2.isLt
    dsimp [frobeniusTriangleDegree]
    linarith
  have hCard := (frobeniusTriangleRow_card x k).le
  have hA := sqrtHasseMinor_normalizedLog_le hx hH hHlog frobeniusTriangleDegree order z w
    hRows hj hz hw hCard hDet
  dsimp only at hA
  rw [frobeniusTriangleRow_firstDegree x k] at hA
  have hU : s * (frobeniusTriangleDivisibility x k 1 : ℝ) ≤ x / 3 + 10 * v := by
    have hR : |s * (frobeniusTriangleDivisibility x k 1 : ℝ) - x / 3| ≤ 10 * v :=
      gaussianSqrtTriangle_scaledFirstDegree_error hx
    linarith [(abs_le.mp hR).2]
  have hHeight := mul_le_mul_of_nonneg_right hU (Real.log_nonneg hH)
  have hError := mul_le_mul_of_nonneg_left hHlog (show 0 ≤ 10 * v by positivity)
  change s * Real.log ‖(Matrix.of fun r c =>
    monomialJet (frobeniusTriangleDegree r).1 (order c) (z c) * w c ^ (frobeniusTriangleDegree r).2).det‖ ≤
      (x / 3) * Real.log H + (40 + 14 * C) * v * Real.log x
  nlinarith

#print axioms gaussianSqrtJetCount_eq_triangleOrder
#print axioms frobeniusJet_orders_lt_iff
#print axioms frobeniusTriangle_retainedSupport_iff
#print axioms gaussianSqrtJet_order_lt_retainedPrime
#print axioms gaussianSqrtTriangle_no_Yp
#print axioms gaussianSqrtTriangle_scaledRowCount_le
#print axioms gaussianSqrtTriangle_nodes_lower
#print axioms gaussianSqrtTriangle_scaledFirstDegree_error
#print axioms sqrtHasseMinor_norm_le
#print axioms sqrtHasseMinor_normalizedLog_le
#print axioms frobeniusTriangleRow_card
#print axioms frobeniusTriangleRow_firstDegree
#print axioms sqrtHasseTriangle_normalizedLog_le

end
end AlpogeSuperZeta
