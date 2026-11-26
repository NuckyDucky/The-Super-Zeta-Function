import GaussianSharpRationalPrefix
import GaussianDyadicFrobeniusWindow

/-! The rational Dirichlet input supplies the expected combined mass of
the two central classes in the original half-open prime window. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArithmeticFunction ArtinPrimitiveRootsConjecture Complex FieldTarget Finset QuarticModel
open scoped Classical

noncomputable section

private abbrev splitPrimes := primePart archivedGaussianSplitMangoldt

private theorem dyadic_split_prefix_difference {x : ℝ}
    (hx : 2 * ((archivedGaussianRationalLevel : ℝ) + 1) ≤ x) :
    rationalStrictPrefix splitPrimes x - rationalStrictPrefix splitPrimes (x / 2) =
      ((4 * (dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x)
        : ℝ) : ℂ) := by
  have hX : 0 ≤ x := by linarith [Nat.cast_nonneg (α := ℝ) archivedGaussianRationalLevel]
  have hco : 2 * (26509772707289 + 1 : ℝ) ≤ x := by
    have h : (26509772707289 : ℝ) ≤ (archivedGaussianRationalLevel : ℝ) := by
      norm_num [archivedGaussianRationalLevel]
    linarith
  let P := range ⌈x⌉₊
  let Q := range ⌈x / 2⌉₊
  have hsub : Q ⊆ P := range_mono (Nat.ceil_mono (by linarith))
  have he : (P \ Q).filter Nat.Prime = dyadicPrimes x := by
    apply Finset.ext
    intro p
    simp only [P, Q, dyadicPrimes, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_range, Nat.lt_ceil, not_lt]
    constructor
    · rintro ⟨⟨hu, hl⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le (Nat.le_floor hu.le), hp, hl, hu⟩
    · rintro ⟨_, hp, hl, hu⟩
      exact ⟨⟨hu, hl⟩, hp⟩
  have hs : rationalStrictPrefix splitPrimes x - rationalStrictPrefix splitPrimes (x / 2) =
      ∑ p ∈ (P \ Q).filter Nat.Prime, archivedGaussianSplitMangoldt p := by
    change (∑ p ∈ P, splitPrimes p) - (∑ p ∈ Q, splitPrimes p) = _
    rw [sum_filter]
    calc
      _ = ∑ p ∈ P \ Q, splitPrimes p := (eq_sub_of_add_eq (sum_sdiff hsub)).symm
      _ = _ := by
        apply sum_congr rfl
        intro p _
        simp only [primePart, ArithmeticFunction.coe_mk]
  rw [hs, he, dyadicFrobeniusLogMass_pair_eq_rational hco, ofReal_mul, ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hP := (mem_filter.mp hp).2
  have hbig : archivedGaussianRationalLevel < p := by
    exact_mod_cast (show (archivedGaussianRationalLevel : ℝ) < (p : ℝ) by linarith [hP.2.1])
  have h₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ archivedGaussianRationalLevel).trans_lt hbig)
  have hD : p.Coprime 26509772707289 := hP.1.coprime_iff_not_dvd.mpr fun h =>
    (not_le_of_gt ((by decide : (26509772707289 : ℕ) ≤ archivedGaussianRationalLevel).trans_lt hbig))
      (Nat.le_of_dvd (by decide) h)
  have hc : p.Coprime archivedGaussianRationalLevel := hP.1.coprime_iff_not_dvd.mpr fun h =>
    hbig.not_ge (Nat.le_of_dvd (by decide) h)
  rw [archivedGaussianSplitMangoldt_at_prime hP.1 h₂ hD hc]
  by_cases h : p % 4 = 1 ∧ rationalNormSign p = 1 <;> simp [h]

theorem dyadicFrobeniusLogMass_pair_main_term (hDir : DirichletLZerosOnLine)
    {t : ℝ} (ht : 1 / 2 < t) (ht₁ : t < 1) :
    ∃ C ≥ 0, ∀ x ≥ 2 * ((archivedGaussianRationalLevel : ℝ) + 1),
      |dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x - x / 8| ≤
        C * x ^ t := by
  obtain ⟨A, hA, hE⟩ := archivedGaussianSplitPrime_prefix_main_term hDir ht ht₁
  refine ⟨A / 2, by positivity, fun x hx => ?_⟩
  have hx₀ : 4 ≤ x := by
    have h : (1 : ℝ) ≤ (archivedGaussianRationalLevel : ℝ) := by
      norm_num [archivedGaussianRationalLevel]
    linarith
  let P := rationalStrictPrefix splitPrimes x
  let Q := rationalStrictPrefix splitPrimes (x / 2)
  have hev : ‖(P - (x : ℂ)) - (Q - ((x / 2 : ℝ) : ℂ))‖ ≤ 2 * A * x ^ t := by
    calc
      _ ≤ ‖P - (x : ℂ)‖ + ‖Q - ((x / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ A * x ^ t + A * (x / 2) ^ t :=
        add_le_add (hE _ (by linarith)) (hE _ (by linarith))
      _ ≤ _ := by
        have hT : (x / 2) ^ t ≤ x ^ t := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
        linarith [mul_le_mul_of_nonneg_left hT hA]
  have he : (P - (x : ℂ)) - (Q - ((x / 2 : ℝ) : ℂ)) =
      ((4 * (dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x - x / 8)
        : ℝ) : ℂ) := by
    have h := dyadic_split_prefix_difference hx
    change P - Q = _ at h
    rw [show (P - (x : ℂ)) - (Q - ((x / 2 : ℝ) : ℂ)) =
      (P - Q) - ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      h]
    push_cast
    ring
  rw [he, norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hev
  linarith

theorem dyadicFrobeniusLogMass_pair_lower (hDir : DirichletLZerosOnLine)
    {t : ℝ} (ht : 1 / 2 < t) (ht₁ : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), x / 8 - C * x ^ t ≤
      dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x := by
  obtain ⟨A, hA, hE⟩ := dyadicFrobeniusLogMass_pair_main_term hDir ht ht₁
  let X₀ := 2 * ((archivedGaussianRationalLevel : ℝ) + 1)
  have h₀ : 0 ≤ X₀ / 8 := by dsimp [X₀]; positivity
  refine ⟨A + X₀ / 8, by positivity, fun x hx => ?_⟩
  by_cases hX : X₀ ≤ x
  · have he := (abs_le.mp (hE x hX)).1
    linarith [mul_nonneg h₀ (Real.rpow_nonneg (zero_le_one.trans hx) t)]
  · have hPos (g : GaussianClosureGroup) : 0 ≤ dyadicFrobeniusLogMass g x := by
      unfold dyadicFrobeniusLogMass
      apply sum_nonneg
      intro p hp
      have h := ((mem_filter.mp (mem_filter.mp hp).1).2).1
      exact Real.log_nonneg (by exact_mod_cast h.pos)
    have ht₀ : 0 ≤ t := by linarith
    have hxpow := Real.one_le_rpow hx ht₀
    have hP := le_mul_of_one_le_right h₀ hxpow
    have hHalf : x / 8 ≤ X₀ / 8 := div_le_div_of_nonneg_right (le_of_not_ge hX) (by norm_num)
    have hA' := mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hx) t)
    rw [add_mul]
    exact (sub_nonpos.mpr (hHalf.trans (hP.trans (le_add_of_nonneg_left hA')))).trans
      (add_nonneg (hPos gaussianCentralElement) (hPos 1))

theorem quartic_rh_of_archived_gaussian_sharp_central_windows
    (hDir : DirichletLZerosOnLine)
    (hcut : GaussianCutoffWindowBound archivedGaussianCentralPrimeExcess) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_central_prime_windows hDir
    (fun _ ht ht₁ => dyadicFrobeniusLogMass_pair_lower hDir ht ht₁) hcut

#check quartic_rh_of_archived_gaussian_sharp_central_windows
#print axioms dyadicFrobeniusLogMass_pair_main_term
#print axioms dyadicFrobeniusLogMass_pair_lower
#print axioms quartic_rh_of_archived_gaussian_sharp_central_windows

end
end GaussianQuarticClosure
end AlpogeSuperZeta
