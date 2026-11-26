import ArchivedGaussianPrimeWeights
import GaussianPrimePowerCoefficients
import Mathlib.RingTheory.PowerSeries.Derivative

/-! The logarithmic derivative of each archived Gaussian Euler factor
as a formal power series, with its prime-power weights. -/

namespace AlpogeSuperZeta

open PowerSeries QuarticModel
open scoped Classical

noncomputable section

local notation "Xₚ" => (PowerSeries.X : PowerSeries ℂ)
local notation "Dₓ" => PowerSeries.derivative ℂ

private theorem weightedGeometric_derivative (a : ℂ) {d : ℕ} (hd : d ≠ 0) :
    Xₚ * Dₓ (weightedGeometricAtDegree a d) =
      weightedGeometricAtDegree a d *
        ((d : PowerSeries ℂ) * (weightedGeometricAtDegree a d - 1)) := by
  let f := weightedGeometricAtDegree a d
  let q := 1 - PowerSeries.C a * Xₚ ^ d
  have hf : f * q = 1 := weightedGeometricAtDegree_mul_denominator a hd
  have hpow : Xₚ * Xₚ ^ (d - 1) = Xₚ ^ d := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]
  have hq : Xₚ * Dₓ q = -((d : PowerSeries ℂ) * (1 - q)) := by
    dsimp only [q]
    rw [map_sub, derivative_one, Derivation.leibniz, derivative_C, derivative_pow, derivative_X]
    simp only [smul_eq_mul, mul_zero, add_zero, zero_sub, mul_one, sub_sub_cancel]
    calc
      _ = -((d : PowerSeries ℂ) * (PowerSeries.C a * (Xₚ * Xₚ ^ (d - 1)))) := by ring
      _ = _ := by rw [hpow]
  have hprod := congrArg (fun F : PowerSeries ℂ => Xₚ * Dₓ F) hf
  change Xₚ * Dₓ (f * q) = Xₚ * Dₓ 1 at hprod
  rw [Derivation.leibniz, derivative_one, mul_zero] at hprod
  simp only [smul_eq_mul] at hprod
  have hrel : Xₚ * Dₓ f * q = f * ((d : PowerSeries ℂ) * (1 - q)) := by
    have hsum : Xₚ * Dₓ f * q + f * (Xₚ * Dₓ q) = 0 := by
      linear_combination hprod
    rw [hq] at hsum
    linear_combination hsum
  change Xₚ * Dₓ f = f * ((d : PowerSeries ℂ) * (f - 1))
  calc
    _ = (Xₚ * Dₓ f * q) * f := by rw [mul_assoc, mul_comm q f, hf, mul_one]
    _ = (f * ((d : PowerSeries ℂ) * (1 - q))) * f := by rw [hrel]
    _ = f * ((d : PowerSeries ℂ) * (f - q * f)) := by ring
    _ = _ := by rw [mul_comm q f, hf]

private theorem derivative_product {ι : Type*} (s : Finset ι) (f b : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, Xₚ * Dₓ (f i) = f i * b i) :
    Xₚ * Dₓ (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hhead := h i (Finset.mem_insert_self i s)
    have htail := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz]
    simp only [smul_eq_mul]
    calc
      _ = f i * (Xₚ * Dₓ (∏ j ∈ s, f j)) + (∏ j ∈ s, f j) * (Xₚ * Dₓ (f i)) := by ring
      _ = _ := by rw [hhead, htail]; ring

/-- For a rational prime, the formal series of logarithmic-derivative
coefficients before the common factor log p is inserted. -/
def archivedGaussianEulerLogSeries (p : ℕ) : PowerSeries ℂ :=
  ∑ I : ↥(gaussianPrimesAbove p),
    (I.val.inertiaDeg ℤ : PowerSeries ℂ) *
      (weightedGeometricAtDegree (archivedIdealCharacter I.val : ℂ) (I.val.inertiaDeg ℤ) - 1)

theorem signedLocalEulerSeries_derivative (p : ℕ) :
    Xₚ * Dₓ (signedLocalEulerSeries p) = signedLocalEulerSeries p * archivedGaussianEulerLogSeries p := by
  unfold signedLocalEulerSeries archivedGaussianEulerLogSeries
  apply derivative_product
  intro I _
  exact weightedGeometric_derivative _ (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt I).ne'

private theorem coeff_natCast_mul (n d : ℕ) (F : PowerSeries ℂ) :
    coeff n ((d : PowerSeries ℂ) * F) = (d : ℂ) * coeff n F := by
  rw [← map_natCast (PowerSeries.C (R := ℂ)) d, coeff_C_mul]

@[simp] theorem archivedGaussianEulerLogSeries_coeff_zero (p : ℕ) :
    coeff 0 (archivedGaussianEulerLogSeries p) = 0 := by
  unfold archivedGaussianEulerLogSeries
  rw [map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  rw [coeff_natCast_mul, map_sub, coeff_weightedGeometricAtDegree _
    (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt I).ne']
  simp

theorem archivedGaussianEulerLogSeries_coeff (p j : ℕ) (hj : j ≠ 0) :
    coeff j (archivedGaussianEulerLogSeries p) = (archivedGaussianPrimePowerWeight p j : ℂ) := by
  unfold archivedGaussianEulerLogSeries archivedGaussianPrimePowerWeight
  rw [map_sum, Complex.ofReal_sum]
  let weight (I : Ideal GaussianInt) : ℝ :=
    if I.inertiaDeg ℤ ∣ j then
      (I.inertiaDeg ℤ : ℝ) * (archivedIdealCharacter I : ℝ) ^ (j / I.inertiaDeg ℤ)
    else 0
  change _ = ∑ I ∈ gaussianPrimesAbove p, (weight I : ℂ)
  rw [← Finset.sum_coe_sort (gaussianPrimesAbove p) (fun I => (weight I : ℂ))]
  apply Finset.sum_congr rfl
  intro I _
  rw [coeff_natCast_mul, map_sub, coeff_weightedGeometricAtDegree _
    (IdealPrimePower.primeAbove_inertiaDeg_pos GaussianInt I).ne', coeff_one, if_neg hj, sub_zero]
  dsimp only [weight]
  split_ifs <;> simp

#print axioms signedLocalEulerSeries_derivative
#print axioms archivedGaussianEulerLogSeries_coeff_zero
#print axioms archivedGaussianEulerLogSeries_coeff

end
end AlpogeSuperZeta
