import GaussianClosurePrimeTrace
import GaussianDyadicPrimeWindow

/-! The dyadic cutoff in terms of actual arithmetic Frobenius in the quartic's closure. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget Finset NumberField QuarticModel Set
open scoped Classical

noncomputable section

private theorem closurePrimeLabel_exists {p : ℕ} (hp : p.Prime) :
    ∃ g : GaussianClosureGroup, ∃ (P : Ideal (𝓞 L)) (σ : ClosureAut),
      P ∈ closurePrimeFiber p ∧ IsArithFrobAt ℤ σ P ∧ g = closureGaloisEquiv σ := by
  obtain ⟨P, hP⟩ := closurePrimeFiber_nonempty hp
  obtain ⟨σ, hσ⟩ := closurePrimeFiber_exists_frobenius hp hP
  exact ⟨closureGaloisEquiv σ, P, σ, hP, hσ, rfl⟩

private def closurePrimeLabel (p : ℕ) : GaussianClosureGroup :=
  if hp : p.Prime then (closurePrimeLabel_exists hp).choose else 1

private theorem closurePrimeLabel_weight {p : ℕ} (hp : p.Prime)
    (hbig : 26509772707289 < p) :
    archivedGaussianPrimeWeight p = (closurePrimeTrace (closurePrimeLabel p) : ℝ) := by
  have h₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ 26509772707289).trans_lt hbig)
  have hD : p.Coprime 26509772707289 := hp.coprime_iff_not_dvd.mpr fun hd =>
    hbig.not_ge (Nat.le_of_dvd (by decide) hd)
  have hB : ¬p ∣ 1027708 := fun hd =>
    (lt_of_le_of_lt (by decide : (1027708 : ℕ) ≤ 26509772707289) hbig).not_ge
      (Nat.le_of_dvd (by decide) hd)
  unfold closurePrimeLabel
  rw [dif_pos hp]
  obtain ⟨P, σ, hP, hσ, hg⟩ := (closurePrimeLabel_exists hp).choose_spec
  rw [hg]
  exact archivedGaussianPrimeWeight_eq_arithmeticFrobenius hp h₂ hD hB hP hσ

private def dyadicPrimes (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x)

private theorem dyadicPrime_gt_conductor {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) {p : ℕ} (hp : p ∈ dyadicPrimes x) :
    26509772707289 < p := by
  have hl : x / 2 ≤ (p : ℝ) := (mem_filter.mp hp).2.2.1
  exact_mod_cast (show (26509772707289 : ℝ) < (p : ℝ) by linarith)

private theorem central_ne_identity : gaussianCentralElement ≠ (1 : GaussianClosureGroup) := by
  decide +kernel

/-- Log-weighted rational primes in the chosen arithmetic Frobenius class of the closure. -/
def dyadicFrobeniusLogMass (label : GaussianClosureGroup) (x : ℝ) : ℝ :=
  ∑ p ∈ (dyadicPrimes x).filter (fun p => closurePrimeLabel p = label), Real.log (p : ℝ)

private theorem dyadicFrobeniusLogMass_eq_sum (g : GaussianClosureGroup) (x : ℝ) :
    dyadicFrobeniusLogMass g x =
      ∑ p ∈ dyadicPrimes x, if closurePrimeLabel p = g then Real.log (p : ℝ) else 0 :=
  sum_filter _ _

theorem archivedGaussianDyadicPrimeWindow_eq_frobenius {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    archivedGaussianDyadicPrimeWindow x =
      2 * (dyadicFrobeniusLogMass gaussianCentralElement x - dyadicFrobeniusLogMass 1 x) := by
  have hx₀ : 0 ≤ x := by linarith
  rw [archivedGaussianDyadicPrimeWindow_eq_sum hx₀]
  change (∑ p ∈ dyadicPrimes x, -Real.log (p : ℝ) * archivedGaussianPrimeWeight p) = _
  rw [dyadicFrobeniusLogMass_eq_sum, dyadicFrobeniusLogMass_eq_sum, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2.1
  rw [closurePrimeLabel_weight hprime (dyadicPrime_gt_conductor hx hp), closurePrimeTrace]
  by_cases hz : closurePrimeLabel p = gaussianCentralElement <;>
    by_cases h₁ : closurePrimeLabel p = 1 <;>
    simp [hz, h₁, central_ne_identity, Ne.symm central_ne_identity] <;> ring

/-- The sum over the two central classes is the rational two-character count. -/
theorem dyadicFrobeniusLogMass_pair_eq_rational {x : ℝ}
    (hx : 2 * (26509772707289 + 1 : ℝ) ≤ x) :
    dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x =
      ∑ p ∈ dyadicPrimes x,
        if p % 4 = 1 ∧ rationalNormSign p = 1 then Real.log (p : ℝ) else 0 := by
  rw [dyadicFrobeniusLogMass_eq_sum, dyadicFrobeniusLogMass_eq_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hprime : p.Prime := (mem_filter.mp hp).2.1
  let : Fact p.Prime := ⟨hprime⟩
  have hbig := dyadicPrime_gt_conductor hx hp
  have hp₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ 26509772707289).trans_lt hbig)
  have hpD : p.Coprime 26509772707289 := hprime.coprime_iff_not_dvd.mpr fun hd =>
    hbig.not_ge (Nat.le_of_dvd (by decide) hd)
  have hNonzero := archivedGaussianPrimeWeight_ne_zero_iff hp₂ hpD
  rw [closurePrimeLabel_weight hprime hbig, Int.cast_ne_zero] at hNonzero
  have hTrace : ∀ g : GaussianClosureGroup,
      closurePrimeTrace g ≠ 0 ↔ g = gaussianCentralElement ∨ g = 1 := by decide +kernel
  simp only [← hNonzero, hTrace]
  by_cases hz : closurePrimeLabel p = gaussianCentralElement <;>
    by_cases h₁ : closurePrimeLabel p = 1 <;>
    simp [hz, h₁, central_ne_identity, Ne.symm central_ne_identity]

/-- The central class has density 1/8 in an interval of length x/2. -/
def archivedGaussianCentralPrimeExcess (x : ℝ) : ℝ :=
  dyadicFrobeniusLogMass gaussianCentralElement x - x / 16

/-- Once the combined mass of the two central classes has its expected main term
with the displayed error, the arithmetic upper bound is needed only for the central class. -/
theorem quartic_rh_of_archived_gaussian_central_prime_windows (hD : DirichletLZerosOnLine)
    (hMass : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      x / 8 - C * x ^ θ ≤
        dyadicFrobeniusLogMass gaussianCentralElement x + dyadicFrobeniusLogMass 1 x)
    (hCentral : GaussianCutoffWindowBound archivedGaussianCentralPrimeExcess) :
    DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_archived_gaussian_dyadic_prime_windows hD
  intro θ hθ hθ₁
  obtain ⟨C, hC, hE⟩ := hMass θ hθ hθ₁
  obtain ⟨δ, hδ, A, hA, hW⟩ := hCentral θ hθ hθ₁
  let X₀ : ℝ := 2 * (26509772707289 + 1)
  refine ⟨δ, hδ, 4 * A + 2 * C, by positivity, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hbound⟩ := hW (max X₀ Y₀)
  refine ⟨Y, (le_max_right X₀ Y₀).trans hY, fun x hx => ?_⟩
  have hX : X₀ ≤ x := (le_max_left X₀ Y₀).trans (hY.trans hx.1)
  have hX₁ : 1 ≤ X₀ := by norm_num [X₀]
  have hN := hE x (hX₁.trans hX)
  have hLoc := hbound x hx
  rw [archivedGaussianDyadicPrimeWindow_eq_frobenius hX]
  unfold archivedGaussianCentralPrimeExcess at hLoc
  linarith

#print axioms archivedGaussianDyadicPrimeWindow_eq_frobenius
#print axioms dyadicFrobeniusLogMass_pair_eq_rational
#check quartic_rh_of_archived_gaussian_central_prime_windows
#print axioms quartic_rh_of_archived_gaussian_central_prime_windows

end

end GaussianQuarticClosure
end AlpogeSuperZeta
