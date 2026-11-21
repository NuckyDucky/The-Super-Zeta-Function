import FieldTarget
import QuarticModel
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! Reduce the series agreement in the field RH interface to local arithmetic.
The first two factors are mathlib's actual Riemann zeta and Dirichlet beta.
The Gaussian series, the ideal-count multiplicativity and the identities at
all prime powers are explicit inputs. -/

namespace FieldCoefficientTransfer

open NumberField ArtinPrimitiveRootsConjecture ArithmeticFunction
noncomputable section

def idealCounts (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n => (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℂ))

/-- Mathlib's L-series ignores n=0. Its ideal count there is one, whereas an
arithmetic function takes value zero there. All positive terms agree. -/
theorem idealCounts_series (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    LSeries (idealCounts K) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr
  intro n hn
  simp [idealCounts, toArithmeticFunction, hn]

def zetaCoeff : ArithmeticFunction ℂ := toArithmeticFunction (1 : ℕ → ℂ)
def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
def betaCoeff : ArithmeticFunction ℂ := toArithmeticFunction (chi4 ·)

theorem zetaCoeff_mul : zetaCoeff.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · simp [zetaCoeff, toArithmeticFunction]
  · intro m n hm hn _
    simp [zetaCoeff, toArithmeticFunction, hm, hn]

theorem zetaCoeff_sum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum zetaCoeff s (riemannZeta s) := by
  apply (LSeriesHasSum_congr _ _ (f := (1 : ℕ → ℂ)) (g := (zetaCoeff : ℕ → ℂ))
    (fun hn => by simp [zetaCoeff, toArithmeticFunction, hn])).mp
  exact LSeriesHasSum_one hs

theorem betaCoeff_sum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum betaCoeff s (chi4.LFunction s) := by
  apply (LSeriesHasSum_congr _ _ chi4.apply_eq_toArithmeticFunction_apply).mp
  rw [chi4.LFunction_eq_LSeries hs]
  exact (chi4.LSeriesSummable_of_one_lt_re hs).LSeriesHasSum

theorem isDedekind_of_primePowerCounts {K : Type*} [Field K] [NumberField K]
    {H : ℂ → ℂ} {g : ArithmeticFunction ℂ}
    (hhol : DifferentiableOn ℂ (fun s => riemannZeta s * chi4.LFunction s * H s) {1}ᶜ)
    (hfield : (idealCounts K).IsMultiplicative) (hg : g.IsMultiplicative)
    (hlocal : ∀ p j : ℕ, p.Prime →
      idealCounts K (p^j) = (zetaCoeff * betaCoeff * g) (p^j))
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum g s (H s)) :
    IsDedekindZeta K (fun s => riemannZeta s * chi4.LFunction s * H s) := by
  refine ⟨hhol, ?_⟩
  intro s hs
  have hb : betaCoeff.IsMultiplicative := chi4.isMultiplicative_toArithmeticFunction
  have hc := (IsMultiplicative.eq_iff_eq_on_prime_powers (idealCounts K) hfield
    (zetaCoeff * betaCoeff * g) ((zetaCoeff_mul.mul hb).mul hg)).mpr hlocal
  have hprod := LSeriesHasSum_mul (LSeriesHasSum_mul (zetaCoeff_sum hs) (betaCoeff_sum hs))
    (hseries s hs)
  rw [← idealCounts_series K s, hc]
  exact hprod.LSeries_eq.symm

#print axioms idealCounts_series
#print axioms isDedekind_of_primePowerCounts

/-- For the quartic constructed from the original polynomial, the two known
factor statements leave precisely the strip-zero question for the Gaussian
candidate. Matching the ideal series at every prime power is an input. -/
theorem quarticRH_iff_gaussian {G : ℂ → ℂ} {g : ArithmeticFunction ℂ}
    (hhol : DifferentiableOn ℂ (fun s => riemannZeta s * chi4.LFunction s * G s) {1}ᶜ)
    (hfield : (idealCounts QuarticModel.K).IsMultiplicative) (hg : g.IsMultiplicative)
    (hlocal : ∀ p j : ℕ, p.Prime →
      idealCounts QuarticModel.K (p^j) = (zetaCoeff * betaCoeff * g) (p^j))
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum g s (G s))
    (hZ : FieldTarget.StripZerosOnLine riemannZeta)
    (hβ : FieldTarget.StripZerosOnLine chi4.LFunction) :
    DedekindZetaRH QuarticModel.K ↔ FieldTarget.StripZerosOnLine G := by
  have hp := isDedekind_of_primePowerCounts hhol hfield hg hlocal hseries
  exact FieldTarget.dedekindZetaRH_iff_third_factor hp.1 hp.2 hZ hβ

#print axioms quarticRH_iff_gaussian

end
end FieldCoefficientTransfer
