import FieldCoefficientTransfer
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The two Gaussian zeros give a single field value. Any observation that
separates these inputs cannot be recovered from that value alone. -/

namespace GaussianZeroFiber

open ArtinPrimitiveRootsConjecture Complex FieldCoefficientTransfer

noncomputable section

/-- Scale in the completed primitive Gaussian Hecke factor of the quartic. -/
def gaussianScale : ℝ := Real.sqrt 106039090829156 / (2 * Real.pi)

def completion (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  (gaussianScale : ℂ) ^ s * Complex.Gamma s * G s

/-- Above real part zero the scale and Gamma factor cannot create a zero. -/
theorem completion_zero_iff {G : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re) :
    completion G s = 0 ↔ G s = 0 := by
  have hB : 0 < gaussianScale := by unfold gaussianScale; positivity
  have hpow : (gaussianScale : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hB.ne'))
  simp [completion, hpow, Complex.Gamma_ne_zero_of_re_pos hs]

/-- Height parameter on the critical line, with sign retained. -/
def linePoint (t : ℝ) : ℂ := ⟨1 / 2, t⟩

/-- At a critical-line zero of the completed Gaussian factor, every field
continuation agrees with the vanishing product. The value at the pole is
outside the identity theorem, and the real coordinate here excludes it. -/
theorem field_zero_of_completion_zero {K : Type*} [Field K] [NumberField K]
    {G Z : ℂ → ℂ} {t : ℝ}
    (hproduct : IsDedekindZeta K (fun s => riemannZeta s * chi4.LFunction s * G s))
    (hZ : IsDedekindZeta K Z) (hz : completion G (linePoint t) = 0) :
    Z (linePoint t) = 0 := by
  have hG := (completion_zero_iff (G := G) (s := linePoint t)
    (by norm_num [linePoint])).mp hz
  have hne : linePoint t ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [linePoint] at hr
  exact (FieldTarget.continuation_eq_off_one hZ hproduct hne).trans (by simp [hG])

/-- Specialization to the quartic defined by the original polynomial. The
coefficient hypotheses identify the product with its ideal-counting series.
The two completed zeros and their distinguished spectral values are explicit
inputs from the central Gaussian and super-zeta calculations. -/
theorem quartic_continuation_no_decoder {G Φ : ℂ → ℂ} {g : ArithmeticFunction ℂ} {t : ℝ}
    (hhol : DifferentiableOn ℂ (fun s => riemannZeta s * chi4.LFunction s * G s) {1}ᶜ)
    (hfield : (idealCounts QuarticModel.K).IsMultiplicative) (hg : g.IsMultiplicative)
    (hlocal : ∀ p j : ℕ, p.Prime →
      idealCounts QuarticModel.K (p^j) = (zetaCoeff * betaCoeff * g) (p^j))
    (hseries : ∀ s : ℂ, 1 < s.re → LSeriesHasSum g s (G s))
    (hupper : completion G (linePoint t) = 0)
    (hlower : completion G (linePoint (-t)) = 0)
    (hdistinct : Φ (linePoint t) ≠ Φ (linePoint (-t))) :
    ∀ Z : ℂ → ℂ, IsDedekindZeta QuarticModel.K Z →
      Z (linePoint t) = 0 ∧ Z (linePoint (-t)) = 0 ∧
      ¬ ∃ H : ℂ → ℂ, H (Z (linePoint t)) = Φ (linePoint t) ∧
        H (Z (linePoint (-t))) = Φ (linePoint (-t)) := by
  intro Z hZ
  have hproduct := isDedekind_of_primePowerCounts hhol hfield hg hlocal hseries
  have hu := field_zero_of_completion_zero hproduct hZ hupper
  have hl := field_zero_of_completion_zero hproduct hZ hlower
  refine ⟨hu, hl, ?_⟩
  rintro ⟨H, he₁, he₂⟩
  rw [hu] at he₁
  rw [hl] at he₂
  exact hdistinct (he₁.symm.trans he₂)

end

end GaussianZeroFiber
