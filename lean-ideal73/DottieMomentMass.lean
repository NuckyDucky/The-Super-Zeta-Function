import DottieSignedMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Bound the absolute mass of the original signed polynomial by counting
Gaussian lattice points by their largest coordinate. -/

open Complex Finset

namespace QuarticModel

open private onArchivedShell rowIndex shellRows from ArchivedQuarticLatticeCoefficients
open private abs_archived_sign_le_one from DottieSignedMoments

private theorem archivedCoeff_abs_le_rows (n : ℕ) :
    |(archivedLatticeCoeff n : ℝ)| ≤ (shellRows n).card := by
  classical
  rw [archivedLatticeCoeff, Int.cast_sum, ← Real.norm_eq_abs]
  refine (norm_sum_le _ _).trans ?_
  have hf : (∑ j ∈ range n.sqrt, ‖(archivedLatticeRow n j : ℝ)‖) =
      ∑ j ∈ shellRows n, ‖(archivedLatticeRow n j : ℝ)‖ := by
    rw [shellRows, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : onArchivedShell n j <;> simp [archivedLatticeRow, h]
  rw [hf]
  calc
    _ ≤ ∑ _j ∈ shellRows n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [archivedLatticeRow, Int.cast_ite, Int.cast_zero, Real.norm_eq_abs]
      split
      · exact abs_archived_sign_le_one _
      · norm_num
    _ = _ := by simp

/-- The unsigned mass through norm `N` is at most twice the number of square
shells. A shell of maximum coordinate `r` has `2r` slots, each of weight
at most `1/r`. -/
theorem archivedMomentMass_le_two_sqrt (N : ℕ) :
    signedMomentMass archivedLatticeCoeff N ≤ 2 * (N.sqrt : ℝ) := by
  classical
  let source := (range N).sigma (fun n => shellRows (n+1))
  let target := (range (N.sqrt+1)).sigma (fun r => range (2*r))
  let u (p : Σ _ : ℕ, ℕ) := p.2 + 1
  let v (p : Σ _ : ℕ, ℕ) := (p.1+1 - (u p)^2).sqrt
  let slot (p : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
    ⟨max (u p) (v p), if v p ≤ u p then v p else max (u p) (v p) + u p⟩
  let decode (q : Σ _ : ℕ, ℕ) : ℕ × ℕ :=
    if q.2 ≤ q.1 then (q.1, q.2) else (q.2-q.1, q.1)
  have hu (p : Σ _ : ℕ, ℕ) : 0 < u p := by simp [u]
  have hnorm (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : (u p)^2+(v p)^2=p.1+1 :=
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
  have hmax (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : max (u p) (v p) ≤ (p.1+1).sqrt := by
    have hn := hnorm p hp
    apply max_le
    · apply Nat.le_sqrt'.mpr
      omega
    · apply Nat.le_sqrt'.mpr
      omega
  have hin (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : slot p ∈ target := by
    apply Finset.mem_sigma.mpr
    constructor
    · have hN := Nat.succ_le_of_lt (mem_range.mp (Finset.mem_sigma.mp hp).1)
      exact mem_range.mpr (Nat.lt_succ_of_le ((hmax p hp).trans (Nat.sqrt_le_sqrt hN)))
    · apply mem_range.mpr
      change (if v p ≤ u p then v p else max (u p) (v p)+u p) < 2*max (u p) (v p)
      split <;> rename_i h
      · rw [max_eq_left h]
        have hup := hu p
        omega
      · rw [max_eq_right (Nat.le_of_lt (lt_of_not_ge h))]
        omega
  have hrecover (p : Σ _ : ℕ, ℕ) : decode (slot p) = (u p, v p) := by
    dsimp only [decode, slot]
    by_cases h : v p ≤ u p
    · simp [h]
    · have hv := lt_of_not_ge h
      have hu' := hu p
      have hlt : ¬ v p + u p ≤ v p := by omega
      simp only [h, if_false, max_eq_right hv.le, hlt, Nat.add_sub_cancel_left]
  have hinj : Set.InjOn slot ↑source := by
    intro p hp q hq h
    have hv := (hrecover p).symm.trans ((congrArg decode h).trans (hrecover q))
    have huu := congrArg Prod.fst hv
    have hvv := congrArg Prod.snd hv
    change u p = u q at huu
    change v p = v q at hvv
    have hn : p.1 = q.1 := by
      have hpn := hnorm p hp
      rw [huu, hvv, hnorm q hq] at hpn
      omega
    have hj : p.2 = q.2 := Nat.succ.inj huu
    exact Sigma.ext hn (heq_of_eq hj)
  let weight (q : Σ _ : ℕ, ℕ) : ℝ := 1/(q.1 : ℝ)
  have hweight (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) :
      1 / Real.sqrt (p.1+1) ≤ weight (slot p) := by
    have h : ((max (u p) (v p) : ℕ) : ℝ) ≤ Real.sqrt (p.1+1) := by
      have hp' := Nat.le_sqrt'.mp (hmax p hp)
      apply Real.le_sqrt (by positivity) (by positivity) |>.mpr
      exact_mod_cast hp'
    change 1/Real.sqrt (p.1+1) ≤ 1/((max (u p) (v p) : ℕ) : ℝ)
    exact one_div_le_one_div_of_le (by exact_mod_cast (hu p).trans_le (le_max_left _ _)) h
  have htotal : (∑ q ∈ target, weight q) = 2*(N.sqrt : ℝ) := by
    dsimp only [target]
    rw [Finset.sum_sigma, Finset.sum_range_succ']
    simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, add_zero]
    calc
      _ = ∑ _m ∈ range N.sqrt, (2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro m _
        simp only [weight, Finset.sum_const, card_range, nsmul_eq_mul]
        push_cast
        have hm : (m:ℝ)+1 ≠ 0 := by positivity
        field_simp
      _ = _ := by simp [mul_comm]
  calc
    signedMomentMass archivedLatticeCoeff N ≤
        ∑ n ∈ range N, ∑ _j ∈ shellRows (n+1), 1 / Real.sqrt (n+1) := by
      unfold signedMomentMass
      apply Finset.sum_le_sum
      intro n _
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      exact div_le_div_of_nonneg_right (archivedCoeff_abs_le_rows _) (Real.sqrt_nonneg _)
    _ = ∑ p ∈ source, 1 / Real.sqrt (p.1+1) :=
      (Finset.sum_sigma (range N) (fun n => shellRows (n+1))
        (fun p => 1 / Real.sqrt (p.1+1))).symm
    _ ≤ ∑ p ∈ source, weight (slot p) := Finset.sum_le_sum hweight
    _ = ∑ q ∈ source.image slot, weight q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ target, weight q := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr hin) (fun _ _ _ => by positivity)
    _ = _ := htotal

#print axioms archivedMomentMass_le_two_sqrt

end QuarticModel
