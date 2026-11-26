import ArchivedGaussianLogDerivative
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Reduce a single Gaussian prime-norm window bound to finitely many
checks at the endpoints and prime powers. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Complex Set
open scoped Classical

noncomputable section

/-- The points where the slope of the prime-norm ramp can change,
along with the two endpoints of the window. -/
def gaussianPrimeWindowKnots (L U : ℝ) : Finset ℝ :=
  insert L (insert U
    (((Finset.range (⌊U⌋₊ + 1)).filter
      (fun n : ℕ => IsPrimePow n ∧ L ≤ (n : ℝ))).image fun n : ℕ => (n : ℝ)))

private theorem knot_mem_Icc {L U x : ℝ} (hL : 0 ≤ L) (hLU : L ≤ U)
    (hx : x ∈ gaussianPrimeWindowKnots L U) : x ∈ Icc L U := by
  simp only [gaussianPrimeWindowKnots, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hx
  rcases hx with rfl | rfl | ⟨n, ⟨hn, _, hLn⟩, rfl⟩
  · exact ⟨le_rfl, hLU⟩
  · exact ⟨hLU, le_rfl⟩
  · exact ⟨hLn, (Nat.le_floor_iff (hL.trans hLU)).mp hn⟩

private theorem prime_power_mem_knots {L U : ℝ} {n : ℕ}
    (hn : IsPrimePow n) (hx : (n : ℝ) ∈ Icc L U) :
    (n : ℝ) ∈ gaussianPrimeWindowKnots L U := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  refine Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨?_, hn, hx.1⟩, rfl⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hx.2))

private theorem gaussianRamp_affine_between_prime_powers (a : ℕ → ℝ) {L U : ℝ}
    (hL : 0 ≤ L) (hK : ∀ n : ℕ, IsPrimePow n → (n : ℝ) ∉ Ioo L U) :
    ∃ m b : ℝ, ∀ x ∈ Icc L U, gaussianPrimeNormRamp a x = m * x + b := by
  let c := (logDeriv QuarticModel.archivedGaussianFactor 1).re
  let weight (n : ℕ) := ArithmeticFunction.vonMangoldt n * a n
  let S := Finset.range (⌊L⌋₊ + 1)
  refine ⟨(∑ n ∈ S, weight n / n) + c, -(∑ n ∈ S, weight n), fun x hx => ?_⟩
  simp only [gaussianPrimeNormRamp, Deduction.ramp, Complex.re_sum, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  change (∑ n ∈ Finset.range (⌊x⌋₊ + 1), weight n * max (x / n - 1) 0) + c * x =
    ((∑ n ∈ S, weight n / n) + c) * x + -(∑ n ∈ S, weight n)
  have hS : S ⊆ Finset.range (⌊x⌋₊ + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.floor_mono hx.1))
  have htail (n : ℕ) (_ : n ∈ Finset.range (⌊x⌋₊ + 1)) (hn : n ∉ S) :
      weight n * max (x / n - 1) 0 = 0 := by
    by_cases hp : IsPrimePow n
    · have hLn : L < (n : ℝ) := by
        apply Nat.lt_of_floor_lt
        simpa [S, Finset.mem_range, Nat.lt_succ_iff] using hn
      have hnU : U ≤ (n : ℝ) := le_of_not_gt fun h => hK n hp ⟨hLn, h⟩
      have hnpos : 0 < (n : ℝ) := hL.trans_lt hLn
      have hzero : x / (n : ℝ) - 1 ≤ 0 :=
        sub_nonpos.mpr ((div_le_one₀ hnpos).mpr (hx.2.trans hnU))
      rw [max_eq_right hzero, mul_zero]
    · simp [weight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
  rw [← Finset.sum_subset hS htail]
  have hterms (n : ℕ) (hn : n ∈ S) :
      weight n * max (x / n - 1) 0 = (weight n / n) * x - weight n := by
    by_cases hz : n = 0
    · subst n
      simp [weight]
    have hnL : (n : ℝ) ≤ L := (Nat.le_floor_iff hL).mp (by
      simpa [S, Finset.mem_range, Nat.lt_succ_iff] using hn)
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)
    have hnonneg : 0 ≤ x / (n : ℝ) - 1 :=
      sub_nonneg.mpr ((one_le_div₀ hnpos).mpr (hnL.trans hx.1))
    rw [max_eq_left hnonneg]
    ring
  rw [Finset.sum_congr rfl hterms, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Checking the endpoints and prime powers is equivalent to checking
the entire real interval for the one-sided bound. -/
theorem gaussianPrimeWindowBound_iff_knots (a : ℕ → ℝ) {L U θ C : ℝ}
    (hL : 0 ≤ L) (hLU : L ≤ U) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) (hC : 0 ≤ C) :
    (∀ x ∈ Icc L U, gaussianPrimeNormRamp a x ≤ C * x ^ θ) ↔
      (∀ x ∈ gaussianPrimeWindowKnots L U, gaussianPrimeNormRamp a x ≤ C * x ^ θ) := by
  constructor
  · exact fun h x hx => h x (knot_mem_Icc hL hLU hx)
  · intro h x hx
    let S := gaussianPrimeWindowKnots L U
    have hSL : L ∈ S := by simp [S, gaussianPrimeWindowKnots]
    have hSU : U ∈ S := by simp [S, gaussianPrimeWindowKnots]
    have hA : (S.filter (fun y => y ≤ x)).Nonempty :=
      ⟨L, Finset.mem_filter.mpr ⟨hSL, hx.1⟩⟩
    have hB : (S.filter (fun y => x ≤ y)).Nonempty :=
      ⟨U, Finset.mem_filter.mpr ⟨hSU, hx.2⟩⟩
    let l := (S.filter (fun y => y ≤ x)).max' hA
    let r := (S.filter (fun y => x ≤ y)).min' hB
    have hl : l ∈ S ∧ l ≤ x := Finset.mem_filter.mp (Finset.max'_mem _ hA)
    have hr : r ∈ S ∧ x ≤ r := Finset.mem_filter.mp (Finset.min'_mem _ hB)
    have hlr : l ≤ r := hl.2.trans hr.2
    have hIl := knot_mem_Icc hL hLU hl.1
    have hIr := knot_mem_Icc hL hLU hr.1
    obtain ⟨m, b, hab⟩ := gaussianRamp_affine_between_prime_powers a (hL.trans hIl.1)
      (show ∀ n : ℕ, IsPrimePow n → (n : ℝ) ∉ Ioo l r from by
        intro n hn hmid
        have hnS : (n : ℝ) ∈ S :=
          prime_power_mem_knots hn ⟨hIl.1.trans hmid.1.le, hmid.2.le.trans hIr.2⟩
        by_cases hnx : (n : ℝ) ≤ x
        · exact hmid.1.not_ge (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hnS, hnx⟩))
        · exact hmid.2.not_ge
            (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hnS, (lt_of_not_ge hnx).le⟩)))
    have haf : ConvexOn ℝ (Icc l r) (fun y => m * y + b) := by
      refine ⟨convex_Icc l r, ?_⟩
      intro p _ q _ u v _ _ huv
      simp only [smul_eq_mul]
      apply le_of_eq
      linear_combination -b * huv
    have hAconv := haf.congr (fun y hy => (hab y hy).symm)
    have hCconc : ConcaveOn ℝ (Icc l r) (fun y => C * y ^ θ) :=
      ((Real.concaveOn_rpow hθ₀ hθ₁).subset
        (fun _ hy => hL.trans (hIl.1.trans hy.1)) (convex_Icc l r)).smul hC
    have hmax := (hAconv.sub hCconc).le_max_of_mem_Icc
      (left_mem_Icc.mpr hlr) (right_mem_Icc.mpr hlr) ⟨hl.2, hr.2⟩
    have hltest := sub_nonpos.mpr (h l hl.1)
    have hrtest := sub_nonpos.mpr (h r hr.1)
    exact sub_nonpos.mp (hmax.trans (max_le hltest hrtest))

/-- The full cutoff condition stated using only the endpoints and prime
powers of each selected window. -/
def ArchivedGaussianPrimeKnotBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ max Y₀ 1,
      ∀ y ∈ gaussianPrimeWindowKnots Y (Y ^ (1 + δ)),
        gaussianPrimeNormRamp archivedGaussianPrimeWeight y ≤ C * y ^ θ

theorem archivedGaussianPrimeWindowBound_iff_knots :
    ArchivedGaussianPrimeWindowBound ↔ ArchivedGaussianPrimeKnotBound := by
  constructor
  · intro h θ hθ₀ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ₀ hθ₁
    refine ⟨δ, hδ, C, hC, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, hbound⟩ := hW (max Y₀ 1)
    have hY1 : 1 ≤ Y := (le_max_right _ _).trans hY
    have hYY : Y ≤ Y ^ (1 + δ) := Real.self_le_rpow_of_one_le hY1 (by linarith)
    exact ⟨Y, hY, (gaussianPrimeWindowBound_iff_knots _ (by linarith) hYY
      (by linarith) hθ₁.le hC).1 hbound⟩
  · intro h θ hθ₀ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ₀ hθ₁
    refine ⟨δ, hδ, C, hC, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, hbound⟩ := hW Y₀
    have hY1 : 1 ≤ Y := (le_max_right _ _).trans hY
    have hYY : Y ≤ Y ^ (1 + δ) := Real.self_le_rpow_of_one_le hY1 (by linarith)
    exact ⟨Y, (le_max_left _ _).trans hY,
      (gaussianPrimeWindowBound_iff_knots _ (by linarith) hYY
        (by linarith) hθ₁.le hC).2 hbound⟩

theorem quartic_rh_of_archived_gaussian_knot_bound (hD : DirichletLZerosOnLine)
    (hcut : ArchivedGaussianPrimeKnotBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_window_bound hD
    (archivedGaussianPrimeWindowBound_iff_knots.2 hcut)

#print axioms gaussianPrimeWindowBound_iff_knots
#print axioms archivedGaussianPrimeWindowBound_iff_knots
#check quartic_rh_of_archived_gaussian_knot_bound
#print axioms quartic_rh_of_archived_gaussian_knot_bound

end
end AlpogeSuperZeta
