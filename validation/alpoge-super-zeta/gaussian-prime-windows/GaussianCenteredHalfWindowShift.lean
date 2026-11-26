import GaussianHalfWindowShift

/-! The unit shift of the prime addresses has an explicit linear term.
The residual is bounded at every exponent strictly above one half. -/

namespace AlpogeSuperZeta

open Finset
open scoped Classical

noncomputable section

private theorem divisorWindow_shift_length {x : ℝ} {p : ℕ} (hp : 0 < p) :
    x / (2 * (p : ℝ)) - x / (2 * ((p + 1 : ℕ) : ℝ)) =
      (x / 2) * (1 / (p : ℝ) / ((p : ℝ) + 1)) := by
  push_cast
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  field_simp
  ring

theorem divisorWindow_shift_centered_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (b : ℕ → ℝ) (hb₀ : b 0 = 0) (hb : ∀ n, 0 ≤ b n) {B : ℝ} (hB : 0 ≤ B)
    (hbLog : ∀ n, b n ≤ B * Real.log n)
    (hs : Summable (fun n => b n / (n : ℝ) ^ (2 * θ))) :
    Summable (fun n => b n / (n : ℝ) / ((n : ℝ) + 1)) ∧
    ∃ D ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |(∑ n ∈ range (⌊x⌋₊ + 1), b n *
          (divisorWindowMultiplicity x n - divisorWindowMultiplicity x (n + 1))) -
        (x / 2) * ∑' n, b n / (n : ℝ) / ((n : ℝ) + 1)| ≤ D * x ^ θ := by
  let L (n : ℕ) := b n / (n : ℝ) / ((n : ℝ) + 1)
  let u (n : ℕ) := b n / (n : ℝ) ^ (2 * θ)
  have hu (n : ℕ) : 0 ≤ u n := div_nonneg (hb n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hL (n : ℕ) : 0 ≤ L n := div_nonneg (div_nonneg (hb n) (Nat.cast_nonneg _)) (by positivity)
  have hLs : Summable L := by
    refine hs.of_nonneg_of_le hL (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp [L, hb₀]
    · have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow : (n : ℝ) ^ (2 * θ) ≤ (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith)
      have hdenom : (n : ℝ) ^ (2 * θ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
        rw [Real.rpow_two] at hpow
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      rw [show L n = b n / ((n : ℝ) * ((n : ℝ) + 1)) by dsimp [L]; rw [div_div]]
      exact div_le_div_of_nonneg_left (hb n) (by positivity) hdenom
  let A := ∑' n, u n
  let ε := θ - 1 / 2
  have hε : 0 < ε := sub_pos.mpr hθ
  have hA : 0 ≤ A := tsum_nonneg hu
  refine ⟨hLs, 2 * A + B / ε,
    add_nonneg (mul_nonneg (by norm_num) hA) (div_nonneg hB hε.le), ?_⟩
  intro x hx
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let R := range (⌊x⌋₊ + 1)
  let S := range (⌊Real.sqrt x⌋₊ + 1)
  let P := R \ S
  have hmemR {n : ℕ} : n ∈ R ↔ (n : ℝ) ≤ x := by
    rw [show R = range (⌊x⌋₊ + 1) from rfl, mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx₀]
  have hmemS {n : ℕ} : n ∈ S ↔ (n : ℝ) ≤ Real.sqrt x := by
    rw [show S = range (⌊Real.sqrt x⌋₊ + 1) from rfl, mem_range, Nat.lt_succ_iff,
      Nat.le_floor_iff (Real.sqrt_nonneg x)]
  have hSR : S ⊆ R := fun n hn =>
    hmemR.mpr ((hmemS.mp hn).trans (Real.sqrt_le_self_iff.mpr (Or.inr hx)))
  have hlt {n : ℕ} (hn : n ∉ S) : Real.sqrt x < (n : ℝ) :=
    lt_of_not_ge fun h => hn (hmemS.mpr h)
  let diff (n : ℕ) := b n *
    (divisorWindowMultiplicity x n - divisorWindowMultiplicity x (n + 1))
  let inside (n : ℕ) := if n ∈ S then diff n else 0
  let e (n : ℕ) := inside n - (x / 2) * L n
  have hbound (n : ℕ) : |e n| ≤ (2 * x ^ θ) * u n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [e, inside, L, u, diff, hb₀]
    have hp : 0 < n := Nat.pos_of_ne_zero hn
    have hp' : (0 : ℝ) < n := Nat.cast_pos.mpr hp
    by_cases hm : n ∈ S
    · have hl : x / (2 * (n : ℝ)) - x / (2 * ((n + 1 : ℕ) : ℝ)) =
          (x / 2) * (1 / (n : ℝ) / ((n : ℝ) + 1)) := divisorWindow_shift_length hp
      have he : e n = b n * ((divisorWindowMultiplicity x n - x / (2 * (n : ℝ))) -
          (divisorWindowMultiplicity x (n + 1) - x / (2 * ((n + 1 : ℕ) : ℝ)))) := by
        simp only [e, inside, if_pos hm, diff, L]
        rw [show divisorWindowMultiplicity x n - x / (2 * (n : ℝ)) -
            (divisorWindowMultiplicity x (n + 1) - x / (2 * ((n + 1 : ℕ) : ℝ))) =
            (divisorWindowMultiplicity x n - divisorWindowMultiplicity x (n + 1)) -
            (x / (2 * (n : ℝ)) - x / (2 * ((n + 1 : ℕ) : ℝ))) by ring, hl]
        ring
      have hr := divisorWindowMultiplicity_rounding hp hx₀
      have hs' := divisorWindowMultiplicity_rounding (Nat.succ_pos n) hx₀
      have hsmall : (n : ℝ) ^ (2 * θ) ≤ x ^ θ := by
        have hh := Real.rpow_le_rpow hp'.le (hmemS.mp hm) (show 0 ≤ 2 * θ by linarith)
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx₀,
          show (1 / (2 : ℝ)) * (2 * θ) = θ by ring] at hh
        exact hh
      rw [he, abs_mul, abs_of_nonneg (hb n)]
      calc
        _ ≤ b n * 2 := by
          apply mul_le_mul_of_nonneg_left _ (hb n)
          rw [sub_eq_add_neg]
          apply (abs_add_le _ _).trans
          rw [abs_neg]
          linarith only [hr, hs']
        _ ≤ _ := by
          dsimp [u]
          rw [← mul_div_assoc]
          apply (le_div_iff₀ (Real.rpow_pos_of_pos hp' _)).mpr
          nlinarith [mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * b n from
            mul_nonneg (by norm_num) (hb n))]
    · have hpw : x ^ (1 - θ) ≤ (n : ℝ) ^ (2 - 2 * θ) := by
        have hh := Real.rpow_le_rpow (Real.sqrt_nonneg x) (hlt hm).le (show 0 ≤ 2 - 2 * θ by linarith)
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx₀,
          show (1 / (2 : ℝ)) * (2 - 2 * θ) = 1 - θ by ring] at hh
        exact hh
      have hxp : x ≤ x ^ θ * (n : ℝ) ^ (2 - 2 * θ) := by
        calc
          x = x ^ θ * x ^ (1 - θ) := by
            rw [← Real.rpow_add hxpos, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
          _ ≤ _ := mul_le_mul_of_nonneg_left hpw (by positivity)
      have hratio : x / ((n : ℝ) * ((n : ℝ) + 1)) ≤ x ^ θ / (n : ℝ) ^ (2 * θ) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        calc
          _ ≤ (x ^ θ * (n : ℝ) ^ (2 - 2 * θ)) * (n : ℝ) ^ (2 * θ) :=
            mul_le_mul_of_nonneg_right hxp (by positivity)
          _ = x ^ θ * (n : ℝ) ^ (2 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hp', show 2 - 2 * θ + 2 * θ = 2 by ring]
          _ ≤ _ := by rw [Real.rpow_two]; gcongr; nlinarith [hp'.le]
      have hlen : 0 ≤ (x / 2) * L n := mul_nonneg (by positivity) (hL n)
      rw [show e n = -((x / 2) * L n) by simp [e, inside, hm], abs_neg, abs_of_nonneg hlen]
      calc
        _ = (b n / 2) * (x / ((n : ℝ) * ((n : ℝ) + 1))) := by
          rw [show L n = b n / ((n : ℝ) * ((n : ℝ) + 1)) by dsimp [L]; rw [div_div]]
          ring
        _ ≤ (b n / 2) * (x ^ θ / (n : ℝ) ^ (2 * θ)) :=
          mul_le_mul_of_nonneg_left hratio (div_nonneg (hb n) (by norm_num))
        _ = (x ^ θ / 2) * u n := by dsimp [u]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.rpow_nonneg hx₀ θ]) (hu n)
  have he : Summable fun n => |e n| :=
    (hs.mul_left (2 * x ^ θ)).of_nonneg_of_le (fun _ => abs_nonneg _) hbound
  have hEs : |∑' n, e n| ≤ (2 * A) * x ^ θ := by
    calc
      _ ≤ ∑' n, |e n| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := e) (by simpa only [Real.norm_eq_abs] using he)
      _ ≤ ∑' n, (2 * x ^ θ) * u n := he.tsum_le_tsum hbound (hs.mul_left (2 * x ^ θ))
      _ = _ := by rw [hs.tsum_mul_left]; dsimp [A]; ring
  have hi : HasSum inside (∑ n ∈ S, diff n) := by
    have hh : HasSum inside (∑ n ∈ S, inside n) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      simp [inside, hn]
    exact (sum_congr rfl (fun n hn => if_pos hn) : (∑ n ∈ S, inside n) = ∑ n ∈ S, diff n) ▸ hh
  have heq : (∑' n, e n) = (∑ n ∈ S, diff n) - (x / 2) * ∑' n, L n :=
    (hi.sub (hLs.hasSum.mul_left (x / 2))).tsum_eq
  have hW : 0 ≤ B * Real.log x := mul_nonneg hB (Real.log_nonneg hx)
  have hP := divisorWindow_shift_large hx P (fun n hn => hlt (mem_sdiff.mp hn).2) b hW
    (fun n hn => ⟨hb n, (hbLog n).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log ((Real.sqrt_pos.mpr hxpos).trans (hlt (mem_sdiff.mp hn).2))
        (hmemR.mp (mem_sdiff.mp hn).1)) hB)⟩)
  have hbig : (∑ n ∈ P, diff n) ≤ (B / ε) * x ^ θ := by
    calc
      _ ≤ (B * Real.log x) * Real.sqrt x := hP.2
      _ ≤ (B * (x ^ ε / ε)) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx₀ hε) hB)
          (Real.sqrt_nonneg x)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, show (B * (x ^ ε / ε)) * x ^ (1 / (2 : ℝ)) =
          (B / ε) * (x ^ ε * x ^ (1 / (2 : ℝ))) by ring, ← Real.rpow_add hxpos,
          show ε + 1 / (2 : ℝ) = θ by dsimp [ε]; ring]
  change |(∑ n ∈ R, diff n) - (x / 2) * ∑' n, L n| ≤ _
  rw [← sum_sdiff hSR (f := diff)]
  rw [show (∑ n ∈ R \ S, diff n) + (∑ n ∈ S, diff n) - (x / 2) * ∑' n, L n =
      (∑' n, e n) + ∑ n ∈ P, diff n by rw [heq]; dsimp [P]; ring]
  calc
    _ ≤ |∑' n, e n| + |∑ n ∈ P, diff n| := abs_add_le _ _
    _ ≤ (2 * A) * x ^ θ + (B / ε) * x ^ θ := add_le_add hEs (by rwa [abs_of_nonneg hP.1])
    _ = _ := by ring

#print axioms divisorWindow_shift_centered_error

end
end AlpogeSuperZeta
