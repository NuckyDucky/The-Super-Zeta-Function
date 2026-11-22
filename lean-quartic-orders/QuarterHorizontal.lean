import QuarterLineTest
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
namespace SuperZeta.QuarterHorizontal
open Complex Set UnitSpectrum

def atHeight (t x : ℝ) : ℂ := (x:ℂ) + (t:ℂ)*I

private theorem horizontal_derivative (f : ℂ → ℂ) {t x : ℝ}
    (h : DifferentiableAt ℂ f (atHeight t x)) :
    HasDerivAt (fun u : ℝ => f (atHeight t u)) (deriv f (atHeight t x)) x := by
  have hp : HasDerivAt (fun z : ℂ => z + (t:ℂ)*I) 1 (x:ℂ) :=
    (hasDerivAt_id _).add_const _
  simpa [atHeight,Function.comp_def] using (h.hasDerivAt.comp (x:ℂ) hp).comp_ofReal

/-- Logarithmic slope with respect to the real input, with the height fixed. -/
theorem norm_strictAnti {f : ℂ → ℂ} {t a b : ℝ}
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℂ f (atHeight t x))
    (hs : ∀ x ∈ Icc a b, (deriv f (atHeight t x) / f (atHeight t x)).re < 0) :
    StrictAntiOn (fun x => ‖f (atHeight t x)‖) (Icc a b) := by
  have hsq : StrictAntiOn (fun x => ‖f (atHeight t x)‖^2) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    · intro x hx
      exact ((horizontal_derivative f (hd x hx)).norm_sq.continuousAt).continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      let z := atHeight t x
      have hh := hs x hx'
      have hn : f z ≠ 0 := by intro he; change (deriv f z / f z).re < 0 at hh; simp [he] at hh
      have hp := Complex.normSq_pos.mpr hn
      change (deriv f z / f z).re < 0 at hh
      rw [Complex.div_re,← add_div] at hh
      have hnum := (div_lt_iff₀ hp).mp hh
      rw [((horizontal_derivative f (hd x hx')).norm_sq).deriv, real_inner_eq_re_inner ℂ,
        RCLike.inner_apply]
      change 2 * ((deriv f z) * (starRingEnd ℂ) (f z)).re < 0
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      linarith
  intro x hx y hy hxy
  have h := hsq hx hy hxy
  exact lt_of_not_ge (fun hn => (not_le_of_gt h)
    (pow_le_pow_left₀ (norm_nonneg _) hn 2))

end SuperZeta.QuarterHorizontal
