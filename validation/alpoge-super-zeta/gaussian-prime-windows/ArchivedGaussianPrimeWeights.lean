import GaussianPrimeRamp
import GaussianBaseEuler
import Mathlib.Data.Nat.Factorization.PrimePow

/-! The logarithmic-derivative weights from the original Gaussian Euler factors. -/

namespace AlpogeSuperZeta

open QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

def archivedGaussianPrimePowerWeight (p j : ℕ) : ℝ :=
  ∑ I ∈ gaussianPrimesAbove p,
    if I.inertiaDeg ℤ ∣ j then
      (I.inertiaDeg ℤ : ℝ) * (archivedIdealCharacter I : ℝ) ^ (j / I.inertiaDeg ℤ)
    else 0

def archivedGaussianPrimeWeight (n : ℕ) : ℝ :=
  if IsPrimePow n then archivedGaussianPrimePowerWeight n.minFac (n.factorization n.minFac)
  else 0

theorem archivedGaussianPrimeWeight_prime_power {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    archivedGaussianPrimeWeight (p ^ j) = archivedGaussianPrimePowerWeight p j := by
  have h : IsPrimePow (p ^ j) := ⟨p, j, hp.prime, Nat.pos_of_ne_zero hj, rfl⟩
  rw [archivedGaussianPrimeWeight, if_pos h, hp.pow_minFac hj, Nat.factorization_pow_self hp]

private theorem archivedIdealCharacter_abs_le_one (I : Ideal GaussianInt) :
    |(archivedIdealCharacter I : ℝ)| ≤ 1 := by
  obtain ⟨z, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  rw [archivedIdealCharacter_span]
  have hJacobi (a : ℤ) (n : ℕ) : |jacobiSym a n| ≤ 1 := by
    rcases jacobiSym.trichotomy a n with h | h | h <;> rw [h] <;> norm_num
  have h : |archivedGaussianSign z| ≤ 1 := by
    unfold archivedGaussianSign
    simp only [abs_mul]
    exact (mul_le_mul (mul_le_mul (hJacobi _ _) (hJacobi _ _) (abs_nonneg _) (by decide))
      (hJacobi _ _) (abs_nonneg _) (by decide)).trans_eq (by norm_num)
  exact_mod_cast h

private theorem gaussian_inertia_sum_le_two (p : ℕ) [Fact p.Prime] :
    ∑ I ∈ gaussianPrimesAbove p, I.inertiaDeg ℤ ≤ 2 := by
  by_cases hp : p = 2
  · subst p
    rw [dyadic_gaussian_prime, Finset.sum_singleton, dyadic_gaussian_prime_degree]
    decide
  have hodd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hcases with h₁ | h₃
  · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
    have hpos : r ^ 2 = -1 := by rw [pow_two, ← hr]
    have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
    have hs := split_gaussian_primes hp r hpos hneg
    have ha : gaussianPrimeAt r hpos ∈ gaussianPrimesAbove p := by simp [hs]
    have hb : gaussianPrimeAt (-r) hneg ∈ gaussianPrimesAbove p := by simp [hs]
    have hne := gaussianPrimeAt_distinct hp r hpos
    rw [hs, Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.sum_singleton, primeAt_degree r hpos ha, primeAt_degree (-r) hneg hb]
  · rw [inert_gaussian_primes h₃, Finset.sum_singleton, inert_gaussian_prime_degree h₃]

theorem archivedGaussianPrimeWeight_abs_le_two (n : ℕ) :
    |archivedGaussianPrimeWeight n| ≤ 2 := by
  rw [archivedGaussianPrimeWeight]
  split_ifs with hn
  · let p := n.minFac
    let j := n.factorization p
    have : Fact p.Prime := ⟨Nat.minFac_prime hn.ne_one⟩
    change |archivedGaussianPrimePowerWeight p j| ≤ 2
    unfold archivedGaussianPrimePowerWeight
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ I ∈ gaussianPrimesAbove p, (I.inertiaDeg ℤ : ℝ) := by
        apply Finset.sum_le_sum
        intro I _
        split_ifs
        · rw [abs_mul, Nat.abs_cast, abs_pow]
          exact mul_le_of_le_one_right (Nat.cast_nonneg _)
            (pow_le_one₀ (abs_nonneg _) (archivedIdealCharacter_abs_le_one I))
        · simp
      _ ≤ 2 := by exact_mod_cast gaussian_inertia_sum_le_two p
  · norm_num

local instance : Fact (Nat.Prime 73) := ⟨by norm_num⟩

theorem archivedGaussianPrimeWeights_at_73 :
    archivedGaussianPrimeWeight 73 = 0 ∧ archivedGaussianPrimeWeight (73 ^ 2) = 2 := by
  have hp : Nat.Prime 73 := Fact.out
  let r : ZMod 73 := 27
  have hpos : r ^ 2 = -1 := by
    change (27 : ZMod 73) ^ 2 = -1
    decide +kernel
  have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
  have htwo : 73 ≠ 2 := by decide
  have hs := split_gaussian_primes htwo r hpos hneg
  have ha : gaussianPrimeAt r hpos ∈ gaussianPrimesAbove 73 := by simp [hs]
  have hb : gaussianPrimeAt (-r) hneg ∈ gaussianPrimesAbove 73 := by simp [hs]
  have hne := gaussianPrimeAt_distinct htwo r hpos
  have hda := primeAt_degree r hpos ha
  have hdb := primeAt_degree (-r) hneg hb
  have hrA : gaussianResidue r hpos ⟨3, 8⟩ = 0 := by
    change (3 : ZMod 73) + 8 * 27 = 0
    decide +kernel
  have hrB : gaussianResidue (-r) hneg ⟨3, -8⟩ = 0 := by
    change (3 : ZMod 73) + (-8) * (-27) = 0
    decide +kernel
  have hA := gaussianPrimeAt_eq_span r hpos ⟨3, 8⟩ (by decide +kernel) hrA
  have hB := gaussianPrimeAt_eq_span (-r) hneg ⟨3, -8⟩ (by decide +kernel) hrB
  have hsa : archivedIdealCharacter (gaussianPrimeAt r hpos) = -1 := by
    rw [hA, archivedIdealCharacter_span]
    norm_num [archivedGaussianSign]
  have hsb : archivedIdealCharacter (gaussianPrimeAt (-r) hneg) = 1 := by
    rw [hB, archivedIdealCharacter_span]
    norm_num [archivedGaussianSign]
  have h (j : ℕ) : archivedGaussianPrimePowerWeight 73 j = (-1 : ℝ) ^ j + 1 := by
    rw [archivedGaussianPrimePowerWeight, hs,
      Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.sum_singleton, hda, hdb, hsa, hsb]
    simp
  constructor
  · rw [← pow_one (73 : ℕ), archivedGaussianPrimeWeight_prime_power hp (by decide), h]
    norm_num
  · rw [archivedGaussianPrimeWeight_prime_power hp (by decide), h]
    norm_num

theorem quartic_rh_of_archived_gaussian_prime_windows (hD : DirichletLZerosOnLine)
    (hcoeff : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => (archivedGaussianPrimeWeight n : ℂ) *
        (ArithmeticFunction.vonMangoldt n : ℂ)) w = -logDeriv archivedGaussianFactor w)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
        ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
          gaussianPrimeNormRamp archivedGaussianPrimeWeight y ≤ C * y ^ θ) :
    DedekindZetaRH K :=
  quartic_rh_of_pointwise_gaussian_prime_norm_windows hD archivedGaussianPrimeWeight
    archivedGaussianPrimeWeight_abs_le_two hcoeff hcut

#check quartic_rh_of_archived_gaussian_prime_windows
#print axioms archivedGaussianPrimeWeight_prime_power
#print axioms archivedGaussianPrimeWeight_abs_le_two
#print axioms archivedGaussianPrimeWeights_at_73
#print axioms quartic_rh_of_archived_gaussian_prime_windows

end
end AlpogeSuperZeta
