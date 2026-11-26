import GaussianSqrtTriangleWindow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The monotone remainder in centering the squared prime cutoff. -/

namespace AlpogeSuperZeta

open Finset Set

noncomputable section

/-- Integral of the squared ramp minus its sum over positive integers up to the cutoff. -/
def squaredRoundingResidual (y : ℝ) : ℝ :=
  y / 3 - ∑ m ∈ range ⌊y⌋₊, (1 - ((m + 1 : ℕ) : ℝ) / y) ^ 2

private theorem sum_squaredMultiples (n : ℕ) {y : ℝ} (hy : y ≠ 0) :
    (∑ m ∈ range n, (1 - ((m + 1 : ℕ) : ℝ) / y) ^ 2) =
      (n : ℝ) - (n : ℝ) * ((n : ℝ) + 1) / y +
        (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / (6 * y ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    field_simp
    ring

private def residualPiece (n : ℕ) (y : ℝ) : ℝ :=
  y / 3 - ((n : ℝ) - (n : ℝ) * ((n : ℝ) + 1) / y +
    (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / (6 * y ^ 2))

private theorem squaredRoundingResidual_eq_piece {n : ℕ} {y : ℝ}
    (hl : (n : ℝ) ≤ y) (hr : y ≤ (n : ℝ) + 1) (hy : 0 < y) :
    squaredRoundingResidual y = residualPiece n y := by
  have hsum : (∑ m ∈ range ⌊y⌋₊, (1 - ((m + 1 : ℕ) : ℝ) / y) ^ 2) =
      ∑ m ∈ range n, (1 - ((m + 1 : ℕ) : ℝ) / y) ^ 2 := by
    rcases hr.lt_or_eq with hlt | heq
    · rw [(Nat.floor_eq_iff hy.le).mpr ⟨hl, hlt⟩]
    · have hcast : y = ((n + 1 : ℕ) : ℝ) := by exact_mod_cast heq
      have hfloor : ⌊y⌋₊ = n + 1 := by rw [hcast, Nat.floor_natCast]
      rw [hfloor, sum_range_succ, ← hcast, div_self hy.ne', sub_self, zero_pow (by decide),
        add_zero]
  unfold squaredRoundingResidual residualPiece
  rw [hsum, sum_squaredMultiples n hy.ne']

private def residualPieceDeriv (n : ℕ) (y : ℝ) : ℝ :=
  let a : ℝ := n
  1 / 3 - a * (a + 1) / y ^ 2 + a * (a + 1) * (2 * a + 1) / (3 * y ^ 3)

private theorem residualPiece_hasDerivAt (n : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (residualPiece n) (residualPieceDeriv n y) y := by
  let a : ℝ := n
  have h₁ := (hasDerivAt_id y).div_const (3 : ℝ)
  have h₂ := (hasDerivAt_const y (a * (a + 1))).div (hasDerivAt_id y) hy.ne'
  have hden := ((hasDerivAt_id y).pow 2).const_mul (6 : ℝ)
  have h₃ := (hasDerivAt_const y (a * (a + 1) * (2 * a + 1))).div hden
    (by dsimp; positivity : (6 : ℝ) * y ^ 2 ≠ 0)
  convert h₁.sub (((hasDerivAt_const y a).sub h₂).add h₃) using 1
  all_goals
    first
    | rfl
    | funext z
    | simp only [residualPieceDeriv, id_eq, Pi.pow_apply, zero_mul, zero_sub, mul_one,
        Nat.reduceSub, pow_one]
      dsimp [a]
      field_simp
      ring

private theorem residualPieceDeriv_eq (n : ℕ) {y : ℝ} (hy : 0 < y) :
    let r := y - (n : ℝ)
    residualPieceDeriv n y = ((n : ℝ) * (1 - 3 * r * (1 - r)) + r ^ 3) / (3 * y ^ 3) := by
  dsimp [residualPieceDeriv]
  field_simp
  ring

private theorem residualPiece_monotoneOn (n : ℕ) (hn : 0 < n) :
    MonotoneOn (residualPiece n) (Icc (n : ℝ) ((n : ℝ) + 1)) := by
  let a : ℝ := n
  have ha : 0 < a := Nat.cast_pos.mpr hn
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := residualPieceDeriv n) (convex_Icc _ _)
  · intro y hy
    have hy₀ := ha.trans_le hy.1
    exact (residualPiece_hasDerivAt n hy₀).continuousAt.continuousWithinAt
  · intro y hy
    exact (residualPiece_hasDerivAt n (ha.trans_le (interior_subset hy).1)).hasDerivWithinAt
  · intro y hy
    have hmem : y ∈ Icc a (a + 1) := interior_subset hy
    have hy₀ : 0 < y := ha.trans_le hmem.1
    let r := y - a
    have hr₀ : 0 ≤ r := sub_nonneg.mpr hmem.1
    have hquarter : r * (1 - r) ≤ 1 / 4 := by nlinarith [sq_nonneg (r - 1 / 2)]
    have hfactor : 0 ≤ 1 - 3 * r * (1 - r) := by nlinarith
    rw [residualPieceDeriv_eq n hy₀]
    exact div_nonneg (add_nonneg (mul_nonneg ha.le hfactor) (pow_nonneg hr₀ _)) (by positivity)

private theorem squaredRoundingResidual_zero : squaredRoundingResidual 0 = 0 := by
  simp [squaredRoundingResidual]

/-- When the cutoff is at most one, only the integral contributes to the residual. -/
theorem squaredRoundingResidual_eq_div_three {y : ℝ} (h₀ : 0 ≤ y) (h₁ : y ≤ 1) :
    squaredRoundingResidual y = y / 3 := by
  rcases h₀.lt_or_eq with hy | rfl
  · rw [squaredRoundingResidual_eq_piece (n := 0) (by exact_mod_cast h₀)
      (by simpa using h₁) hy]
    simp [residualPiece]
  · rw [squaredRoundingResidual_zero, zero_div]

private theorem squaredRoundingResidual_monotoneOn_cell (n : ℕ) :
    MonotoneOn squaredRoundingResidual (Icc (n : ℝ) ((n : ℝ) + 1)) := by
  by_cases hn : 0 < n
  · intro y hy z hz hyz
    have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [squaredRoundingResidual_eq_piece hy.1 hy.2 (hpos.trans_le hy.1),
      squaredRoundingResidual_eq_piece hz.1 hz.2 (hpos.trans_le hz.1)]
    exact residualPiece_monotoneOn n hn hy hz hyz
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    intro y hy z hz hyz
    rw [squaredRoundingResidual_eq_div_three (by simpa using hy.1) (by simpa using hy.2),
      squaredRoundingResidual_eq_div_three (by simpa using hz.1) (by simpa using hz.2)]
    exact div_le_div_of_nonneg_right hyz (by norm_num)

private theorem squaredRoundingResidual_monotoneOn_toNat (N : ℕ) :
    MonotoneOn squaredRoundingResidual (Icc (0 : ℝ) (N : ℝ)) := by
  induction N with
  | zero =>
    intro y hy z hz _
    have hy₀ : y = 0 := le_antisymm (by simpa using hy.2) hy.1
    have hz₀ : z = 0 := le_antisymm (by simpa using hz.2) hz.1
    subst y
    subst z
    rfl
  | succ N ih =>
    intro y hy z hz hyz
    have hz₁ : z ≤ (N : ℝ) + 1 := by exact_mod_cast hz.2
    by_cases hzN : z ≤ (N : ℝ)
    · exact ih ⟨hy.1, hyz.trans hzN⟩ ⟨hz.1, hzN⟩ hyz
    · have hzN' := le_of_not_ge hzN
      have hcell := squaredRoundingResidual_monotoneOn_cell N
      by_cases hyN : y ≤ (N : ℝ)
      · exact (ih ⟨hy.1, hyN⟩ ⟨Nat.cast_nonneg N, le_rfl⟩ hyN).trans
          (hcell ⟨le_rfl, by linarith⟩ ⟨hzN', hz₁⟩ hzN')
      · exact hcell ⟨le_of_not_ge hyN, hyz.trans hz₁⟩ ⟨hzN', hz₁⟩ hyz

theorem squaredRoundingResidual_monotoneOn : MonotoneOn squaredRoundingResidual (Ici 0) := by
  intro y hy z hz hyz
  have hceil := Nat.le_ceil z
  exact squaredRoundingResidual_monotoneOn_toNat ⌈z⌉₊
    ⟨hy, hyz.trans hceil⟩ ⟨hz, hceil⟩ hyz

theorem squaredRoundingResidual_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ squaredRoundingResidual y := by
  simpa only [squaredRoundingResidual_zero] using
    squaredRoundingResidual_monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy

theorem squaredRoundingResidual_le_half {y : ℝ} (hy : 0 ≤ y) :
    squaredRoundingResidual y ≤ 1 / 2 := by
  let N := max 1 ⌈y⌉₊
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  have hyN : y ≤ (N : ℝ) := (Nat.le_ceil y).trans (by exact_mod_cast le_max_right 1 ⌈y⌉₊)
  refine (squaredRoundingResidual_monotoneOn hy hN.le hyN).trans ?_
  rw [squaredRoundingResidual_eq_piece (n := N) le_rfl (by linarith) hN]
  have hval : residualPiece N (N : ℝ) = 1 / 2 - 1 / (6 * (N : ℝ)) := by
    unfold residualPiece
    field_simp
    ring
  rw [hval]
  exact sub_le_self _ (by positivity)

private theorem residualPieceDeriv_le (n : ℕ) {y : ℝ} (hy : 0 < y)
    (hl : (n : ℝ) ≤ y) (hr : y ≤ (n : ℝ) + 1) :
    residualPieceDeriv n y ≤ 1 / (3 * y ^ 2) := by
  let a : ℝ := n
  let r := y - a
  have hr₀ : 0 ≤ r := sub_nonneg.mpr hl
  have hr₁ : r ≤ 1 := by dsimp [r, a]; linarith
  have hfirst : a * (1 - 3 * r * (1 - r)) ≤ a := by
    have h : 0 ≤ 3 * r * (1 - r) := mul_nonneg (by positivity) (sub_nonneg.mpr hr₁)
    exact (mul_le_mul_of_nonneg_left (sub_le_self _ h) (Nat.cast_nonneg n)).trans_eq (mul_one a)
  have hlast : r ^ 3 ≤ r := by
    have h : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr₀ hr₁ 2
    rw [pow_succ]
    simpa using mul_le_mul_of_nonneg_right h hr₀
  rw [residualPieceDeriv_eq n hy]
  calc
    _ ≤ y / (3 * y ^ 3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      change a * (1 - 3 * r * (1 - r)) + r ^ 3 ≤ y
      exact (add_le_add hfirst hlast).trans_eq (by dsimp [r]; ring)
    _ = _ := by field_simp

private def reciprocalAdjustedResidual (y : ℝ) : ℝ :=
  squaredRoundingResidual y + (1 / 3 : ℝ) * y⁻¹

private theorem reciprocalAdjustedResidual_antitoneOn_cell (n : ℕ) :
    AntitoneOn reciprocalAdjustedResidual (Icc (n : ℝ) ((n : ℝ) + 1) ∩ Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    intro y hy z hz hyz
    have hy₀ : 0 < y := hy.2
    have hz₀ : 0 < z := hz.2
    have hy₁ : y ≤ 1 := by simpa using hy.1.2
    have hz₁ : z ≤ 1 := by simpa using hz.1.2
    have hp : y * z ≤ 1 := by
      simpa using mul_le_mul hy₁ hz₁ hz₀.le zero_le_one
    unfold reciprocalAdjustedResidual
    rw [squaredRoundingResidual_eq_div_three hy₀.le hy₁,
      squaredRoundingResidual_eq_div_three hz₀.le hz₁]
    have hdiff : (y / 3 + 1 / 3 * y⁻¹) - (z / 3 + 1 / 3 * z⁻¹) =
        (z - y) * (1 - y * z) / (3 * y * z) := by
      field_simp
      ring
    apply sub_nonneg.mp
    rw [hdiff]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hyz) (sub_nonneg.mpr hp)) (by positivity)
  · let f (y : ℝ) := residualPiece n y + (1 / 3 : ℝ) * y⁻¹
    let d (y : ℝ) := residualPieceDeriv n y - 1 / (3 * y ^ 2)
    have ha : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hDer (y : ℝ) (hy : 0 < y) : HasDerivAt f (d y) y := by
      have h := (residualPiece_hasDerivAt n hy).add
        ((hasDerivAt_inv hy.ne').const_mul (1 / 3 : ℝ))
      have hd : d y = residualPieceDeriv n y + 1 / 3 * -(y ^ 2)⁻¹ := by
        dsimp [d]
        ring
      rw [hd]
      exact h
    have hF : AntitoneOn f (Icc (n : ℝ) ((n : ℝ) + 1)) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := d) (convex_Icc _ _)
      · intro y hy
        exact (hDer y (ha.trans_le hy.1)).continuousAt.continuousWithinAt
      · intro y hy
        exact (hDer y (ha.trans_le (interior_subset hy).1)).hasDerivWithinAt
      · intro y hy
        have hmem := interior_subset hy
        exact sub_nonpos.mpr (residualPieceDeriv_le n (ha.trans_le hmem.1) hmem.1 hmem.2)
    intro y hy z hz hyz
    have h := hF hy.1 hz.1 hyz
    unfold reciprocalAdjustedResidual
    rw [squaredRoundingResidual_eq_piece hy.1.1 hy.1.2 hy.2,
      squaredRoundingResidual_eq_piece hz.1.1 hz.1.2 hz.2]
    exact h

private theorem reciprocalAdjustedResidual_antitoneOn_toNat (N : ℕ) :
    AntitoneOn reciprocalAdjustedResidual (Ioc (0 : ℝ) (N : ℝ)) := by
  induction N with
  | zero =>
    intro y hy
    have hy' : y ≤ 0 := by simpa using hy.2
    exact (not_lt_of_ge hy' hy.1).elim
  | succ N ih =>
    intro y hy z hz hyz
    have hz₁ : z ≤ (N : ℝ) + 1 := by exact_mod_cast hz.2
    by_cases hzN : z ≤ (N : ℝ)
    · exact ih ⟨hy.1, hyz.trans hzN⟩ ⟨hz.1, hzN⟩ hyz
    · have hzN' := le_of_not_ge hzN
      have hcell := reciprocalAdjustedResidual_antitoneOn_cell N
      by_cases hyN : y ≤ (N : ℝ)
      · have hpos := hy.1.trans_le hyN
        exact (hcell ⟨⟨le_rfl, by linarith⟩, hpos⟩ ⟨⟨hzN', hz₁⟩, hz.1⟩ hzN').trans
          (ih ⟨hy.1, hyN⟩ ⟨hpos, le_rfl⟩ hyN)
      · exact hcell ⟨⟨le_of_not_ge hyN, hyz.trans hz₁⟩, hy.1⟩ ⟨⟨hzN', hz₁⟩, hz.1⟩ hyz

/-- The residual increment is at most the corresponding drop in the reciprocal term. -/
theorem squaredRoundingResidual_sub_le_reciprocal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    squaredRoundingResidual b - squaredRoundingResidual a ≤ (a⁻¹ - b⁻¹) / 3 := by
  have hb := ha.trans_le hab
  have hceil := Nat.le_ceil b
  have h := reciprocalAdjustedResidual_antitoneOn_toNat ⌈b⌉₊
    ⟨ha, hab.trans hceil⟩ ⟨hb, hceil⟩ hab
  dsimp [reciprocalAdjustedResidual] at h
  linarith

theorem squaredRoundingResidual_at_prime {x : ℝ} (hx : 0 < x) {p : ℕ} (hp : 0 < p) :
    squaredRoundingResidual (x / (p : ℝ)) =
      x / (3 * (p : ℝ)) - ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p) := by
  let y := x / (p : ℝ)
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hy : 0 < y := div_pos hx hp₀
  have hle : ⌊y⌋₊ ≤ ⌈x⌉₊ := Nat.floor_le_of_le (by
    exact (div_le_self hx.le hp₁).trans (Nat.le_ceil x))
  have hsum : (∑ m ∈ range ⌊y⌋₊, (1 - ((m + 1 : ℕ) : ℝ) / y) ^ 2) =
      ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p) := by
    calc
      _ = ∑ m ∈ range ⌊y⌋₊, squaredRampWeight x ((m + 1) * p) := by
        apply sum_congr rfl
        intro m hm
        have hm₁ : ((m + 1 : ℕ) : ℝ) ≤ y :=
          (Nat.cast_le.mpr (Nat.succ_le_of_lt (mem_range.mp hm))).trans (Nat.floor_le hy.le)
        have hmp : (((m + 1) * p : ℕ) : ℝ) ≤ x := by
          simpa only [Nat.cast_mul] using (le_div_iff₀ hp₀).mp hm₁
        have hratio : ((m + 1 : ℕ) : ℝ) / y = (((m + 1) * p : ℕ) : ℝ) / x := by
          dsimp [y]
          push_cast
          field_simp
        rw [hratio, squaredRampWeight]
        rcases hmp.lt_or_eq with hlt | heq
        · rw [if_pos hlt]
        · rw [heq, if_neg (lt_irrefl x), div_self hx.ne', sub_self, zero_pow (by decide)]
      _ = _ := by
        refine sum_subset (range_mono hle) (fun m _ hm => ?_)
        have hm₁ : y < ((m + 1 : ℕ) : ℝ) :=
          (Nat.lt_floor_add_one y).trans_le (by
            exact_mod_cast Nat.succ_le_succ (not_lt.mp (fun h => hm (mem_range.mpr h))))
        have hmp : x < (((m + 1) * p : ℕ) : ℝ) := by
          simpa only [Nat.cast_mul] using (div_lt_iff₀ hp₀).mp hm₁
        exact if_neg hmp.le.not_gt
  change y / 3 - _ = _
  rw [hsum]
  dsimp [y]
  ring

end

end AlpogeSuperZeta
