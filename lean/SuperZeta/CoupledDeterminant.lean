import SuperZeta.QuartetLevels
import SuperZeta.Spectrum
import Mathlib.Analysis.Analytic.OfScalars

/-! The entire unit-coupling determinant in the squared spectral variable.
The coefficients, growth bound, simple zeros, and enumeration are independent
of a product formula. -/
namespace SuperZeta.Spectrum
open Complex Set
noncomputable section

private def series := FormalMultilinearSeries.ofScalars ℂ (fun n => (determinantCoeff 1 n : ℂ))

/-- The entire squared determinant, normalized by E(0)=1. -/
def coupledDet : ℂ → ℂ := series.sum

theorem coupledDet_sq (z : ℂ) : coupledDet (z^2) = Complex.cos z ^ 2-z^2 := by
  change FormalMultilinearSeries.ofScalarsSum _ _ = _
  simpa [FormalMultilinearSeries.ofScalars_sum_eq, smul_eq_mul] using (determinant_hasSum 1 z).tsum_eq

theorem coupledDet_zero : coupledDet 0 = 1 := by simpa using coupledDet_sq 0

theorem coupledDet_analytic (z : ℂ) : AnalyticAt ℂ coupledDet z := by
  have rad : series.radius = ⊤ := by
    apply series.radius_eq_top_of_summable_norm
    intro r
    let v := (↑(Real.sqrt r):ℂ)
    have hv : v^2=((r:ℝ):ℂ) := by
      change (↑(Real.sqrt r):ℂ)^2=_
      rw [← Complex.ofReal_pow, Real.sq_sqrt r.coe_nonneg]
    have h := (determinant_hasSum 1 v).summable.norm
    simp only [hv, norm_mul, norm_pow, Complex.norm_of_nonneg r.coe_nonneg] at h
    simpa only [series, FormalMultilinearSeries.ofScalars_norm] using h
  exact (series.hasFPowerSeriesOnBall (by simp [rad])).analyticAt_of_mem (by simp [rad])

private theorem square_preimage (w : ℂ) : ∃ z : ℂ, z^2=w :=
  ⟨_,Complex.cpow_nat_inv_pow w (n:=2) (by decide)⟩

/-- Explicit growth of order at most one half, throughout the whole plane. -/
theorem coupledDet_growth (w : ℂ) :
    ‖coupledDet w‖ ≤ Real.exp (2*Real.sqrt ‖w‖) + ‖w‖ := by
  obtain ⟨z,rfl⟩ := square_preimage w
  have ec (y : ℂ) : ‖Complex.exp (y*I)‖ ≤ Real.exp ‖y‖ := by
    simpa [norm_mul] using Complex.norm_exp_le_exp_norm (y*I)
  have hcos : ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
    rw [Complex.cos, norm_div]
    have hp := (norm_add_le (Complex.exp (z*I)) (Complex.exp (-z*I))).trans
      (add_le_add (ec z) (ec (-z)))
    simp only [norm_neg,Complex.norm_ofNat] at *
    linarith
  rw [coupledDet_sq]
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  rw [norm_pow, norm_pow, Real.sqrt_sq (norm_nonneg _), two_mul, Real.exp_add, ← sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hcos 2

theorem coupledDet_on_ray {r : ℝ} (hr : 0≤r) :
    coupledDet (-(r:ℂ)) = ((Real.cosh (Real.sqrt r)^2 + r : ℝ):ℂ) := by
  let z : ℂ := (Real.sqrt r : ℂ)*I
  have hz : z^2 = -(r:ℂ) := by simp [z, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hr]
  rw [← hz, coupledDet_sq, hz, show Complex.cos z = Complex.cosh (Real.sqrt r) from Complex.cos_mul_I _]
  push_cast
  ring

/-- The determinant in the squared plane has exactly the indexed spectrum,
with a unique index for every zero. -/
theorem coupledDet_zero_iff_unique_index {d : ℝ}
    (hd : d ∈ Ioo 0 (Real.pi/2) ∧ d = Real.cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ QuartetRadius.level (t n)=2*Real.pi*(n+1)) (w : ℂ) :
    coupledDet w=0 ↔ ∃! j, w=RootBounds.family d t j := by
  obtain ⟨z,rfl⟩ := square_preimage w
  rw [coupledDet_sq, RootBounds.determinant_root_iff_indexed_square hd roots]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨j,hj,fun k hk => RootBounds.family_injective d roots (hk.symm.trans hj)⟩
  · exact ExistsUnique.exists

theorem coupledDet_simple {w : ℂ} (h : coupledDet w=0) : deriv coupledDet w ≠ 0 := by
  obtain ⟨z,rfl⟩ := square_preimage w
  rw [coupledDet_sq] at h
  intro hd
  have he := (coupledDet_analytic (z^2)).differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  rw [hd, zero_mul] at he
  have hg : HasDerivAt (fun w : ℂ => cos w ^ 2 - w^2) 0 z := by
    simpa only [Function.comp_def, id_eq, coupledDet_sq] using he
  exact Quartet.determinant_root_simple h hg.deriv

end
end SuperZeta.Spectrum
