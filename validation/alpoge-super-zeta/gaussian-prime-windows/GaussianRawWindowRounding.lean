import GaussianDivisorWindow
import Mathlib.Order.Interval.Finset.Nat

/-! Address multiplicities in a raw window, and a square-root split
which absorbs small-address rounding into the allowed error. -/

namespace AlpogeSuperZeta

open Finset
open scoped Classical

noncomputable section

def divisorWindowMultiplicity (x : ℝ) (d : ℕ) : ℝ :=
  (⌈x / (d : ℝ)⌉₊ : ℝ) - (⌈x / (2 * (d : ℝ))⌉₊ : ℝ)

theorem divisorWindowMultiplicity_rounding {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    |divisorWindowMultiplicity x d - x / (2 * (d : ℝ))| < 1 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h0 : 0 ≤ x / (d : ℝ) := div_nonneg hx hd'.le
  have h1 : 0 ≤ x / (2 * (d : ℝ)) := div_nonneg hx (by positivity)
  have hsplit : x / (d : ℝ) = 2 * (x / (2 * (d : ℝ))) := by ring
  unfold divisorWindowMultiplicity
  exact abs_lt.mpr ⟨by linarith [Nat.le_ceil (x / (d : ℝ)), Nat.ceil_lt_add_one h1],
    by linarith [Nat.ceil_lt_add_one h0, Nat.le_ceil (x / (2 * (d : ℝ)))]⟩

private theorem divisorWindowMultiplicity_hasSum {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 0 < d)
    (b : ℝ) :
    HasSum (fun m : ℕ => b * IndexedCutoff.window.weight x (d * (m + 1)))
      (b * divisorWindowMultiplicity x d) := by
  let lo := ⌈x / (2 * (d : ℝ))⌉₊
  let hi := ⌈x / (d : ℝ)⌉₊
  let I := Finset.Ico (lo - 1) (hi - 1)
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlo : 1 ≤ lo := Nat.succ_le_of_lt
    (Nat.lt_ceil.mpr (by simpa using div_pos hx (show (0 : ℝ) < 2 * d by positivity)))
  have hle : lo ≤ hi := Nat.ceil_le_ceil (by
    apply div_le_div_of_nonneg_left hx.le hd'
    linarith)
  have he (m : ℕ) : m ∈ I ↔ (d * (m + 1) : ℕ) < x ∧ x ≤ 2 * ((d * (m + 1) : ℕ) : ℝ) := by
    have h0 : lo ≤ m + 1 ↔ x ≤ 2 * ((d * (m + 1) : ℕ) : ℝ) := by
      dsimp [lo]
      rw [Nat.ceil_le, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d)]
      push_cast
      ring_nf
    have h1 : m + 1 < hi ↔ ((d * (m + 1) : ℕ) : ℝ) < x := by
      dsimp [hi]
      rw [Nat.lt_ceil, lt_div_iff₀ hd']
      push_cast
      ring_nf
    rw [← h0, ← h1, mem_Ico]
    omega
  have hWeight (m : ℕ) :
      IndexedCutoff.window.weight x (d * (m + 1)) = if m ∈ I then 1 else 0 := by
    simp only [IndexedCutoff.weight, ← he m]
  have hsum : HasSum (fun m : ℕ => b * IndexedCutoff.window.weight x (d * (m + 1)))
      (∑ m ∈ I, b * IndexedCutoff.window.weight x (d * (m + 1))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro m hm
    simp only [hWeight, if_neg hm, mul_zero]
  have htotal : ∑ m ∈ I, b * IndexedCutoff.window.weight x (d * (m + 1)) =
      b * divisorWindowMultiplicity x d := by
    have hfun (m : ℕ) (hm : m ∈ I) : b * IndexedCutoff.window.weight x (d * (m + 1)) = b := by
      rw [hWeight, if_pos hm, mul_one]
    rw [Finset.sum_congr rfl hfun, Finset.sum_const, nsmul_eq_mul]
    dsimp only [I, divisorWindowMultiplicity]
    rw [Nat.card_Ico]
    change (((hi - 1 - (lo - 1) : ℕ) : ℝ) * b) = b * ((hi : ℝ) - (lo : ℝ))
    rw [show hi - 1 - (lo - 1) = hi - lo by omega, Nat.cast_sub hle, mul_comm]
  exact htotal ▸ hsum

private theorem archivedRawWindow_multiplicity_hasSum {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun i : GaussianIndexFamily =>
      gaussianIndexCoefficient i * divisorWindowMultiplicity x (gaussianIndexAddress i))
      (archivedGaussianRawWindow x) := by
  have hprod := indexedCutoffSum_summable_at .window
    (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
    (divisorWindowIndex gaussianIndexAddress) (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (a := 2) (by norm_num) hx
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress (by norm_num)
      (gaussianIndexFamily_summable (by norm_num)))
  exact hprod.hasSum.prod_fiberwise fun i =>
    divisorWindowMultiplicity_hasSum (zero_lt_one.trans_le hx) (gaussianIndexAddress_pos i)
      (gaussianIndexCoefficient i)

/-- Each address counts all its original multiples in the half-window. -/
theorem archivedGaussianRawWindow_by_multiplicity {x : ℝ} (hx : 1 ≤ x) :
    archivedGaussianRawWindow x = ∑' i : GaussianIndexFamily,
      gaussianIndexCoefficient i * divisorWindowMultiplicity x (gaussianIndexAddress i) :=
  (archivedRawWindow_multiplicity_hasSum hx).tsum_eq.symm

/-- Replace the counts of multiples by their lengths at addresses
at most `√x`, and keep the exact counts at all larger addresses. -/
def archivedGaussianLargeAddressWindow (x : ℝ) : ℝ :=
  ∑' i : GaussianIndexFamily, gaussianIndexCoefficient i *
    if (gaussianIndexAddress i : ℝ) ≤ Real.sqrt x then x / (2 * (gaussianIndexAddress i : ℝ))
    else divisorWindowMultiplicity x (gaussianIndexAddress i)

/-- Small-address rounding fits the original error scale for every
exponent strictly above one half. -/
theorem archivedGaussianLargeAddressWindow_error {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ D ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianRawWindow x - archivedGaussianLargeAddressWindow x| ≤ D * x ^ θ := by
  let a := 2 * θ
  have ha : 1 < a := by dsimp [a]; linarith
  let u (i : GaussianIndexFamily) := |gaussianIndexCoefficient i| / (gaussianIndexAddress i : ℝ) ^ a
  have hs : Summable u := gaussianIndexFamily_summable ha
  have hu (i : GaussianIndexFamily) : 0 ≤ u i := by dsimp [u]; positivity
  refine ⟨∑' i, u i, tsum_nonneg hu, fun x hx => ?_⟩
  have hx₀ := zero_le_one.trans hx
  let f (i : GaussianIndexFamily) :=
    gaussianIndexCoefficient i * divisorWindowMultiplicity x (gaussianIndexAddress i)
  let g (i : GaussianIndexFamily) := gaussianIndexCoefficient i *
    if (gaussianIndexAddress i : ℝ) ≤ Real.sqrt x then x / (2 * (gaussianIndexAddress i : ℝ))
    else divisorWindowMultiplicity x (gaussianIndexAddress i)
  have hF : HasSum f (archivedGaussianRawWindow x) := archivedRawWindow_multiplicity_hasSum hx
  have hbound (i : GaussianIndexFamily) : |f i - g i| ≤ u i * x ^ θ := by
    dsimp only [f, g]
    split_ifs with hi
    · rw [← mul_sub, abs_mul]
      have hp := gaussianIndexAddress_pos i
      have hp' : (0 : ℝ) < (gaussianIndexAddress i : ℝ) := Nat.cast_pos.mpr hp
      calc
        _ ≤ |gaussianIndexCoefficient i| * 1 := mul_le_mul_of_nonneg_left
          (divisorWindowMultiplicity_rounding hp hx₀).le (abs_nonneg _)
        _ ≤ u i * x ^ θ := by
          rw [mul_one]
          dsimp only [u]
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ (Real.rpow_pos_of_pos hp' _)).mpr
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hh := Real.rpow_le_rpow hp'.le hi (zero_lt_one.trans ha).le
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx₀, show (1 / (2 : ℝ)) * a = θ by
            dsimp [a]; ring] at hh
          exact hh
    · rw [sub_self, abs_zero]
      exact mul_nonneg (hu i) (Real.rpow_nonneg hx₀ _)
  have hAbs : Summable (fun i => |f i - g i|) :=
    (hs.mul_right (x ^ θ)).of_nonneg_of_le (fun _ => abs_nonneg _) hbound
  have hE := hAbs.of_abs
  have hG : Summable g := by
    simpa only [sub_sub_cancel] using hF.summable.sub hE
  rw [show archivedGaussianLargeAddressWindow x = ∑' i, g i from rfl, ← hF.tsum_eq,
    ← hF.summable.tsum_sub hG, ← hs.tsum_mul_right]
  calc
    _ ≤ ∑' i, |f i - g i| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => f i - g i) (by simpa only [Real.norm_eq_abs] using hAbs))
    _ ≤ _ := hAbs.tsum_le_tsum hbound (hs.mul_right (x ^ θ))

#print axioms archivedGaussianRawWindow_by_multiplicity
#print axioms archivedGaussianLargeAddressWindow_error

end
end AlpogeSuperZeta
