import GaussianClosurePrimeTrace

/-! Supply the eventual prime data in the signed retained-norm criterion
for the archived quartic. The late-window bound remains an explicit input. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget Finset NumberField UniqueFactorizationMonoid

noncomputable section

/-- One cutoff works for every finite exceptional set used by the
unramified ideal count and the signed coefficient comparison. -/
theorem eventually_retainedPrimeData :
    ∃ X₀ : ℝ, ∀ x ≥ X₀, ∃ frob, RetainedPrimeData x frob := by
  classical
  let M : ℕ := max (discr L).natAbs 26509772707289
  have hM : (2 : ℕ) ≤ M := (by decide : (2 : ℕ) ≤ 26509772707289).trans (le_max_right _ _)
  refine ⟨((M : ℝ) + 1) ^ 2, fun x hx => ?_⟩
  have hx₂ : 2 ≤ x := by
    have hM' : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    nlinarith
  have hPrime (p : ℕ) (hp : p ∈ retainedPrimes x) :
      gaussianSqrtTriangleScale x ≤ (p : ℝ) ∧ p.Prime :=
    (mem_filter.mp (show p ∈ (range (⌊x⌋₊ + 1)).filter
      (fun q : ℕ => gaussianSqrtTriangleScale x ≤ (q : ℝ) ∧ q.Prime) from hp)).2
  have hDisc (p : ℕ) (hp : p ∈ retainedPrimes x) : ¬ (p : ℤ) ∣ discr L := by
    intro h
    have hdiv : p ∣ (discr L).natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr h
    exact (not_le_of_gt (retained_prime_gt_of_cutoff hx hp))
      ((Nat.le_of_dvd (Int.natAbs_pos.mpr (discr_ne_zero L)) hdiv).trans (le_max_left _ _))
  have hPlaces (p : ℕ) (hp : p ∈ retainedPrimes x) :
      ∃ (P : Ideal (𝓞 L)) (σ : ClosureAut), P ∈ closurePrimeFiber p ∧ IsArithFrobAt ℤ σ P := by
    have hp' := (hPrime p hp).2
    obtain ⟨P, hP⟩ := closurePrimeFiber_nonempty hp'
    obtain ⟨σ, hσ⟩ := closurePrimeFiber_exists_frobenius hp' hP
    exact ⟨P, σ, hP, hσ⟩
  choose P σ hP hσ using hPlaces
  let g (p : ℕ) : GaussianClosureGroup :=
    if hp : p ∈ retainedPrimes x then closureGaloisEquiv (σ p hp) else 1
  refine ⟨g, ⟨?_, ?_, ?_⟩⟩
  · exact fun p hp Q hQ => closurePrimeFiber_unramified (hPrime p hp).2 (hDisc p hp) hQ
  · intro p hp Q hQ label hLabel
    have h := hPrime p hp
    change (normalizedFactors (sqrtFrobeniusMinorIdeal x (integerAction label).toRingHom)).count Q =
      if g p = label then frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p else 0
    simpa only [g, dif_pos hp] using retainedMinor_exponents_of_arithmeticFrobenius h.2
      (hDisc p hp) (hP p hp) (hσ p hp) hx₂ h.1 hQ label hLabel
  · intro p hp
    have h := hPrime p hp
    have hBig : 26509772707289 < p := (le_max_right _ _).trans_lt (retained_prime_gt_of_cutoff hx hp)
    have hp₂ : p ≠ 2 := ne_of_gt (hM.trans_lt (retained_prime_gt_of_cutoff hx hp))
    have hpD : p.Coprime 26509772707289 := h.2.coprime_iff_not_dvd.mpr fun hd =>
      (not_le_of_gt hBig) (Nat.le_of_dvd (by decide) hd)
    have hpB : ¬ p ∣ 1027708 := fun hd =>
      (not_le_of_gt ((by decide : (1027708 : ℕ) ≤ 26509772707289).trans_lt hBig))
        (Nat.le_of_dvd (by decide) hd)
    simpa only [g, dif_pos hp] using
      archivedGaussianPrimeWeight_eq_arithmeticFrobenius h.2 hp₂ hpD hpB (hP p hp) (hσ p hp)

theorem archivedGaussianRetainedNormWindow_bound_iff_triangle :
    GaussianCutoffWindowBound archivedGaussianRetainedNormWindow ↔
      GaussianCutoffWindowBound archivedGaussianSqrtTriangleWindow := by
  obtain ⟨_, hData⟩ := eventually_retainedPrimeData
  exact archivedGaussianRetainedNormWindow_bound_iff hData

/-- The norm-window form of the quartic deduction with its prime-data
input discharged in the actual degree-eight closure. -/
theorem quartic_rh_of_archived_gaussian_actual_norm_windows
    (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianRetainedNormWindow) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨_, hData⟩ := eventually_retainedPrimeData
  exact quartic_rh_of_archived_gaussian_retained_norm_windows hD hpos hData hcut

#check quartic_rh_of_archived_gaussian_actual_norm_windows
#print axioms eventually_retainedPrimeData
#print axioms archivedGaussianRetainedNormWindow_bound_iff_triangle
#print axioms quartic_rh_of_archived_gaussian_actual_norm_windows

end
end GaussianQuarticClosure
end AlpogeSuperZeta
