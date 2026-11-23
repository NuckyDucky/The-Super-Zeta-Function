import FieldCoefficientTransfer
import IdealNormCoprime

namespace FieldCoefficientTransfer
open NumberField ArtinPrimitiveRootsConjecture ArithmeticFunction
noncomputable section

private abbrev fiber (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  IdealNormCoprime.fiber (𝓞 K) n

theorem idealCounts_mul (K : Type*) [Field K] [NumberField K] :
    (idealCounts K).IsMultiplicative := by
  classical
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · let : Unique (fiber K 1) :=
      { default := ⟨⊤, by simp⟩
        uniq := fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property) }
    simp [idealCounts, toArithmeticFunction]
  · intro m n hm hn h
    have hc := (Nat.card_congr (IdealNormCoprime.splitEquiv (R := 𝓞 K) h)).symm
    rw [Nat.card_prod] at hc
    simpa [idealCounts, toArithmeticFunction, hm, hn, fiber] using congrArg (Nat.cast : ℕ → ℂ) hc

#print axioms idealCounts_mul

theorem quarticRH_iff_gaussian_of_local_data {G : ℂ → ℂ} {g : ArithmeticFunction ℂ}
    (hhol : DifferentiableOn ℂ (fun s => riemannZeta s * chi4.LFunction s * G s) {1}ᶜ)
    (hg : g.IsMultiplicative)
    (hlocal : ∀ p j : ℕ, p.Prime →
      idealCounts QuarticModel.K (p^j) = (zetaCoeff * betaCoeff * g) (p^j))
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum g s (G s))
    (hZ : FieldTarget.StripZerosOnLine riemannZeta)
    (hβ : FieldTarget.StripZerosOnLine chi4.LFunction) :
    DedekindZetaRH QuarticModel.K ↔ FieldTarget.StripZerosOnLine G :=
  quarticRH_iff_gaussian hhol (idealCounts_mul QuarticModel.K) hg hlocal hseries hZ hβ

#print axioms quarticRH_iff_gaussian_of_local_data
end
end FieldCoefficientTransfer
