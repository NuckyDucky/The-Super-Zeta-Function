import SuperZeta.CapRecovery.CapJets
import SuperZeta.CapRecovery.DyadicWeights

noncomputable section
namespace SuperZeta.DyadicCap

open SignWords CapJets DyadicWeights

/-- Prefix polynomial in chronological order. -/
def polynomial (w : List Sign) (t : ℂ) : ℂ :=
  ∑ j ∈ Finset.range w.length, (signProduct (w.take (j+1)) : ℂ) * t^j

private theorem polynomial_snoc (w : List Sign) (s : Sign) (t : ℂ) :
    polynomial (w ++ [s]) t = polynomial w t +
      (signProduct (w ++ [s]) : ℂ) * t^w.length := by
  unfold polynomial
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [List.take_append_of_le_length (show j + 1 ≤ w.length by
      exact Finset.mem_range.mp hj)]
  · rw [List.take_of_length_le (by simp)]

private theorem rate_letter (s : Sign) :
    s.rate lift = (letter s : ℂ) * lift := by
  cases s <;> simp [Sign.rate, letter]

private theorem product_snoc (w : List Sign) (s : Sign) :
    signProduct (w ++ [s]) = signProduct w * letter s := by
  simp [signProduct]

/-- The initial derivative and logarithmic curvature are the final sign product
and prefix polynomial, respectively. -/
theorem jet_prefixes (w : List Sign) :
    (jet w).1 = (-lift)^w.length * (signProduct w : ℂ) ∧
    (jet w).2 = lift * polynomial w (-lift) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [jet, signProduct, polynomial]
  | append_singleton w s ih =>
    have h : jet (w ++ [s]) = stepJet (jet w) s := by
      simp [jet]
    rw [h, polynomial_snoc, product_snoc, Complex.ofReal_mul]
    simp only [stepJet, List.length_append, List.length_singleton, pow_succ]
    rw [ih.1, ih.2, rate_letter]
    constructor <;> ring

/-- The cap's actual second-to-first derivative ratio reads the same residues
as the normalized dyadic logarithmic Euler coefficients in the order selected
by the word. No zero-location assumptions enter. -/
theorem cap_ratio_dyadic (w : List Sign) :
    deriv (deriv (eval lift w)) 1 / deriv (eval lift w) 1 =
    lift * ∑ j ∈ Finset.range w.length,
      ((7 * (FieldWeights.primePowerWeight (1/7) (legendreSym 3 2 : ℝ)
        (exponent (w.take (j+1))) - 1) : ℝ) : ℂ) * (-lift)^j := by
  rw [jet_ratio, (jet_prefixes w).2]
  unfold polynomial
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [recover_character_prefix]

end SuperZeta.DyadicCap
