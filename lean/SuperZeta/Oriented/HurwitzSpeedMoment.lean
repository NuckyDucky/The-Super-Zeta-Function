import SuperZeta.Oriented.LiuEndpointTransfer
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring

namespace HurwitzSpeedMoment

open Complex HurwitzZeta
open scoped ComplexConjugate BigOperators
noncomputable section

/-- The modulus of this complex quantity is the normalized speed at a simple zero. -/
def scaledQuotient (χ : DirichletCharacter ℂ 3) (z : ℂ) : ℂ :=
  (3 / (Real.pi : ℂ)) * (χ.LFunction (1+z) / (1-(3 : ℂ)^(-z)))

def mirror (z : ℂ) : ℂ := 1 - conj z

theorem mirror_fixed_iff (z : ℂ) : mirror z = z ↔ z.re = 1/2 := by
  rw [Complex.ext_iff]
  simp [mirror]
  constructor <;> intro h <;> linarith

theorem pair_difference (u v : ℂ) :
    normSq u + normSq v = 2 * (u * conj v).re + normSq (u-v) := by
  rw [normSq_sub]
  ring

theorem pair_agreement_iff (u v : ℂ) :
    normSq u + normSq v = 2 * (u * conj v).re ↔ u = v := by
  rw [pair_difference]
  simp [sub_eq_zero]

/-- Repeated indices allow multiplicity. A permutation represents reflection
of the finite list of zeros in a height window. -/
theorem reflected_window {ι : Type*} [Fintype ι] (χ : DirichletCharacter ℂ 3)
    (z : ι → ℂ) (p : ι ≃ ι) (hp : ∀ j, z (p j) = mirror (z j)) :
    2 * (∑ j, normSq (scaledQuotient χ (z j))) =
    2 * (∑ j, (scaledQuotient χ (z j) * conj (scaledQuotient χ (mirror (z j)))).re) +
      ∑ j, normSq (scaledQuotient χ (z j) - scaledQuotient χ (mirror (z j))) := by
  have hsum := p.sum_comp (fun j => normSq (scaledQuotient χ (z j)))
  simp only [hp] at hsum
  have pairs := Finset.sum_congr (rfl : (Finset.univ : Finset ι) = Finset.univ) (fun j _ =>
    pair_difference (scaledQuotient χ (z j)) (scaledQuotient χ (mirror (z j))))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at pairs
  linarith

theorem reflected_window_lower {ι : Type*} [Fintype ι] (χ : DirichletCharacter ℂ 3)
    (z : ι → ℂ) (p : ι ≃ ι) (hp : ∀ j, z (p j) = mirror (z j)) :
    (∑ j, (scaledQuotient χ (z j) * conj (scaledQuotient χ (mirror (z j)))).re) ≤
      ∑ j, normSq (scaledQuotient χ (z j)) := by
  have h := reflected_window χ z p hp
  have hn : 0 ≤ ∑ j, normSq (scaledQuotient χ (z j) - scaledQuotient χ (mirror (z j))) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  linarith

/-- The geometric sum at the prime three and the two Hurwitz residue classes
in the diagonal are the actual convergent constants at exponent three. -/
theorem normalized_diagonal :
    (3 / Real.pi)^2 * (∑' k : ℕ, (1/3 : ℝ)^k) *
      ((hurwitzZeta (1/3 : ℝ) (3 : ℂ) + hurwitzZeta (2/3 : ℝ) (3 : ℂ)).re / 27) =
      13 * (riemannZeta (3 : ℂ)).re / Real.pi^2 := by
  have hg := tsum_geometric_of_lt_one (r := (1/3 : ℝ)) (by norm_num) (by norm_num)
  have h := DottieOriented.LiuConnection.hurwitz_pair (w := (3 : ℂ)) (by norm_num)
  rw [h, hg]
  norm_num [Complex.mul_re]
  ring

end
end HurwitzSpeedMoment
