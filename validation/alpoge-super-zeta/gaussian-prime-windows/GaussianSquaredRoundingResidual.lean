import GaussianSqrtTriangleWindow
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

private theorem residualPiece_monotoneOn (n : ℕ) (hn : 0 < n) :
    MonotoneOn (residualPiece n) (Icc (n : ℝ) ((n : ℝ) + 1)) := by
  let a : ℝ := n
  let d (y : ℝ) := 1 / 3 - a * (a + 1) / y ^ 2 + a * (a + 1) * (2 * a + 1) / (3 * y ^ 3)
  have ha : 0 < a := Nat.cast_pos.mpr hn
  have hDer (y : ℝ) (hy : 0 < y) : HasDerivAt (residualPiece n) (d y) y := by
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
      | simp only [d, id_eq, Pi.pow_apply, zero_mul, zero_sub, mul_one, Nat.reduceSub, pow_one]
        field_simp
        ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := d) (convex_Icc _ _)
  · intro y hy
    have hy₀ := ha.trans_le hy.1
    exact (hDer y hy₀).continuousAt.continuousWithinAt
  · intro y hy
    exact (hDer y (ha.trans_le (interior_subset hy).1)).hasDerivWithinAt
  · intro y hy
    have hmem : y ∈ Icc a (a + 1) := interior_subset hy
    have hy₀ : 0 < y := ha.trans_le hmem.1
    let r := y - a
    have hr₀ : 0 ≤ r := sub_nonneg.mpr hmem.1
    have hquarter : r * (1 - r) ≤ 1 / 4 := by nlinarith [sq_nonneg (r - 1 / 2)]
    have hfactor : 0 ≤ 1 - 3 * r * (1 - r) := by nlinarith
    have hd : d y = (a * (1 - 3 * r * (1 - r)) + r ^ 3) / (3 * y ^ 3) := by
      dsimp [d, r]
      field_simp
      ring
    rw [hd]
    exact div_nonneg (add_nonneg (mul_nonneg ha.le hfactor) (pow_nonneg hr₀ _)) (by positivity)

private theorem squaredRoundingResidual_zero : squaredRoundingResidual 0 = 0 := by
  simp [squaredRoundingResidual]

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
    have hlinear (y : ℝ) (hy : y ∈ Icc (0 : ℝ) (0 + 1)) :
        squaredRoundingResidual y = y / 3 := by
      rcases hy.1.lt_or_eq with hy₀ | h
      · rw [squaredRoundingResidual_eq_piece (n := 0) (by simpa using hy.1)
          (by simpa using hy.2) hy₀]
        simp [residualPiece]
      · subst y
        rw [squaredRoundingResidual_zero, zero_div]
    intro y hy z hz hyz
    rw [hlinear y (by simpa using hy), hlinear z (by simpa using hz)]
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
