import DottieOmittedSharpVariation
import DottieDyadicCoefficient

/-! Reuse the even norms of a new block by evaluating their coefficients at
half the norm. Completion and smoothing weights stay at the original norm. -/

namespace QuarticModel

open Complex Finset
open private signedTerm from DottieSignedMoments

theorem dottie_norm_block_eq_prefix_sub (h len : ℕ) (w : ℂ) :
    dottieNormBlock h len w =
      signedDirichletPolynomial archivedLatticeCoeff (h+len) w -
      signedDirichletPolynomial archivedLatticeCoeff h w := by
  rw [signedDirichletPolynomial, signedDirichletPolynomial, Finset.sum_range_add,
    dottieNormBlock, add_sub_cancel_left]

private theorem dottie_even_norms_image (h k : ℕ) :
    (Ioc h k).filter (fun n => n % 2 = 0) =
      (Ioc (h / 2) (k / 2)).image (fun n => 2*n) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨hn, heven⟩
    exact ⟨n/2, by omega, by omega⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨by omega, by omega⟩

theorem dottie_even_norm_weighted (h k : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ (Ioc h k).filter (fun n => n % 2 = 0), (archivedLatticeCoeff n : ℂ) * f n =
      ∑ n ∈ Ioc (h/2) (k/2), (archivedLatticeCoeff n : ℂ) * f (2*n) := by
  rw [dottie_even_norms_image, sum_image (fun x _ y _ hxy => by omega)]
  simp only [archivedLatticeCoeff_two_mul]

theorem dottie_norm_block_dyadic (h k : ℕ) (w : ℂ) :
    ∑ n ∈ Ioc h k, (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w) =
      (2 : ℂ)^(-w) * (∑ n ∈ Ioc (h/2) (k/2), (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w)) +
      ∑ n ∈ (Ioc h k).filter (fun n => n % 2 ≠ 0), (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w) := by
  rw [← sum_filter_add_sum_filter_not (Ioc h k) (fun n : ℕ => n % 2 = 0),
    dottie_even_norm_weighted h k, Finset.mul_sum]
  congr 1
  refine sum_congr rfl (fun n _ => ?_)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show ((2 : ℂ) * n)^(-w) = (2 : ℂ)^(-w) * (n : ℂ)^(-w) from
    Complex.natCast_mul_natCast_cpow 2 n (-w)]
  ring

theorem dottie_first_omitted_dyadic (w : ℂ) :
    dottieNormBlock dottiePrefixEnd dottiePrefixEnd w =
      (2 : ℂ)^(-w) * dottieNormBlock (dottiePrefixEnd/2) (dottiePrefixEnd/2) w +
      ∑ n ∈ (Ioc dottiePrefixEnd (2*dottiePrefixEnd)).filter (fun n => n % 2 ≠ 0),
        (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w) := by
  have heven : dottiePrefixEnd/2 + dottiePrefixEnd/2 = dottiePrefixEnd := by decide +kernel
  have hdiv : (2*dottiePrefixEnd)/2 = dottiePrefixEnd := by decide +kernel
  rw [dottie_norm_block_eq_Ioc, dottie_norm_block_eq_Ioc, heven, ← Nat.two_mul]
  simpa only [hdiv] using dottie_norm_block_dyadic dottiePrefixEnd (2*dottiePrefixEnd) w

#print axioms dottie_norm_block_eq_prefix_sub
#print axioms dottie_even_norm_weighted
#print axioms dottie_norm_block_dyadic
#print axioms dottie_first_omitted_dyadic

end QuarticModel
