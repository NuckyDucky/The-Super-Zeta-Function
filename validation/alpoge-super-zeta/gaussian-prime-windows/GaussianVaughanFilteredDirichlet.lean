import GaussianVaughanPrimePowers
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The dyadic scale removes the principal Dirichlet pole after doubling.
This module proves the holomorphic continuation supplied by the rational
zero-free input, including the value at the removed pole. -/

namespace AlpogeSuperZeta

open Complex DirichletCharacter Filter Set
open scoped Classical Topology

noncomputable section

private def principalResidue (N : ℕ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹)

private def principalRegular (N : ℕ) [NeZero N] : ℂ → ℂ :=
  Function.update (fun w => (w - 1) * LFunctionTrivChar N w) 1 (principalResidue N)

private theorem principalResidue_ne_zero (N : ℕ) : principalResidue N ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp'.pos
  have hlt : ‖(p : ℂ)⁻¹‖ < 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact (inv_lt_one₀ hpos).mpr (by exact_mod_cast hp'.one_lt)
  intro he
  exact (ne_of_lt hlt) (by rw [← sub_eq_zero.mp he, norm_one])

private theorem principalRegular_eventuallyEq (N : ℕ) [NeZero N] {w : ℂ} (hw : w ≠ 1) :
    principalRegular N =ᶠ[𝓝 w] (fun z => (z - 1) * LFunctionTrivChar N z) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds (show w ∈ ({1} : Set ℂ)ᶜ from hw)] with z hz
  rw [principalRegular, Function.update_of_ne hz]

private theorem principalRegular_differentiable (N : ℕ) [NeZero N] :
    Differentiable ℂ (principalRegular N) := by
  intro w
  by_cases hw : w = 1
  · subst w
    let f (w : ℂ) := (w - 1) * LFunctionTrivChar N w
    have ht : Tendsto f (𝓝[≠] (1 : ℂ)) (𝓝 (principalResidue N)) :=
      LFunctionTrivChar_residue_one (N := N)
    let C := ‖principalResidue N‖ + 1
    have hBound : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ‖f z‖ < C :=
      ht.norm.eventually (Iio_mem_nhds (lt_add_one _))
    let S : Set ℂ := {z | z ≠ 1 → ‖f z‖ < C}
    have hS : S ∈ 𝓝 (1 : ℂ) := by
      change ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 1 → ‖f z‖ < C
      simpa only [mem_compl_iff, mem_singleton_iff] using eventually_nhdsWithin_iff.mp hBound
    have hd : DifferentiableOn ℂ f (S \ {1}) := by
      intro z hz
      exact ((differentiableAt_id.sub_const _).mul
        (differentiableAt_LFunction _ _ (Or.inl hz.2))).differentiableWithinAt
    have hb : BddAbove ((norm ∘ f) '' (S \ {1})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.1 hz.2).le
    have he := differentiableOn_update_limUnder_of_bddAbove hS hd hb
    rw [ht.limUnder_eq] at he
    exact he.differentiableAt hS
  · exact ((differentiableAt_id.sub_const _).mul
      (differentiableAt_LFunction _ _ (Or.inl hw))).congr_of_eventuallyEq
        (principalRegular_eventuallyEq N hw)

private theorem dirichletL_ne_zero_of_right (hDir : DirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {w : ℂ}
    (hw : 1 / 2 < w.re) (hχw : χ ≠ 1 ∨ w ≠ 1) : LFunction χ w ≠ 0 := by
  by_cases hw₁ : w.re < 1
  · intro hzero
    have he := hDir N χ w (by linarith) hw₁ hzero
    linarith
  · exact LFunction_ne_zero_of_one_le_re χ hχw (le_of_not_gt hw₁)

private theorem principalRegular_ne_zero (hDir : DirichletLZerosOnLine)
    (N : ℕ) [NeZero N] {w : ℂ} (hw : 1 / 2 < w.re) : principalRegular N w ≠ 0 := by
  by_cases h₁ : w = 1
  · subst w
    simpa only [principalRegular, Function.update_self] using principalResidue_ne_zero N
  rw [principalRegular, Function.update_of_ne h₁]
  exact mul_ne_zero (sub_ne_zero.mpr h₁) (dirichletL_ne_zero_of_right hDir _ hw (Or.inr h₁))

private abbrev scaleDifference := gaussianScaleDifference (1 / 2)

private theorem scaleDifference_differentiable : Differentiable ℂ scaleDifference := by
  unfold scaleDifference gaussianScaleDifference
  fun_prop

private theorem scaleDifference_half : scaleDifference ((1 / 2 : ℝ) : ℂ) = 0 :=
  (gaussianHalfScale_zero_ne_zero (z := 1) (by norm_num)).1

private theorem scaleDifference_dslope_differentiable :
    Differentiable ℂ (dslope scaleDifference ((1 / 2 : ℝ) : ℂ)) := by
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (s := univ) univ_mem).mpr
    scaleDifference_differentiable.differentiableOn

/-- The pole of the principal logarithmic derivative is divided out of the
scale difference by an entire divided difference. -/
def archivedGaussianFilteredDirichletLog {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  if χ = 1 then
    scaleDifference z * (-logDeriv (principalRegular N) (2 * z)) +
      dslope scaleDifference ((1 / 2 : ℝ) : ℂ) z / 2
  else scaleDifference z * (-logDeriv (LFunction χ) (2 * z))

theorem archivedGaussianFilteredDirichletLog_analyticAt (hDir : DirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 / 4 < z.re) :
    AnalyticAt ℂ (archivedGaussianFilteredDirichletLog χ) z := by
  have hw : 1 / 2 < (2 * z).re := by simp [mul_re]; linarith
  have hlin : AnalyticAt ℂ (fun w : ℂ => 2 * w) z := analyticAt_const.mul analyticAt_id
  have hs := scaleDifference_differentiable.analyticAt z
  by_cases hχ : χ = 1
  · have hd := (principalRegular_differentiable N).analyticAt (2 * z)
    have hn := principalRegular_ne_zero hDir N hw
    have he := (hd.deriv.div hd hn).neg.comp hlin
    unfold archivedGaussianFilteredDirichletLog
    simp only [if_pos hχ]
    exact (hs.mul he).add ((scaleDifference_dslope_differentiable.analyticAt z).div_const (c := 2))
  have hd := (differentiable_LFunction hχ).analyticAt (2 * z)
  have hn := dirichletL_ne_zero_of_right hDir χ hw (Or.inl hχ)
  have he := (hd.deriv.div hd hn).neg.comp hlin
  unfold archivedGaussianFilteredDirichletLog
  simp only [if_neg hχ]
  exact hs.mul he

theorem archivedGaussianFilteredDirichletLog_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 / 2 < z.re) :
    archivedGaussianFilteredDirichletLog χ z =
      scaleDifference z * (-logDeriv (LFunction χ) (2 * z)) := by
  by_cases hχ : χ = 1
  · subst χ
    let w := (2 : ℂ) * z
    have hw : 1 < w.re := by dsimp only [w]; simp [mul_re]; linarith
    have hw₀ : w ≠ 1 := by
      intro he
      rw [he, one_re] at hw
      exact (lt_irrefl _) hw
    have hlog : logDeriv (principalRegular N) w =
        (w - 1)⁻¹ + logDeriv (LFunctionTrivChar N) w := by
      have he := principalRegular_eventuallyEq N hw₀
      have hχw := LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ N) (Or.inr hw₀) hw.le
      have hlin : HasDerivAt (fun t : ℂ => t - 1) 1 w := (hasDerivAt_id w).sub_const 1
      have hsub : logDeriv (fun x : ℂ => x - 1) w = (w - 1)⁻¹ := by
        rw [logDeriv_apply, hlin.deriv, one_div]
      rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds, ← logDeriv_apply,
        logDeriv_mul (f := fun t : ℂ => t - 1) (g := LFunctionTrivChar N)
          w (sub_ne_zero.mpr hw₀) hχw hlin.differentiableAt
          (differentiableAt_LFunction _ _ (Or.inl hw₀)),
        hsub]
    have hds : dslope scaleDifference ((1 / 2 : ℝ) : ℂ) z / 2 = scaleDifference z / (w - 1) := by
      apply (eq_div_iff (sub_ne_zero.mpr hw₀)).2
      calc
        _ = (z - ((1 / 2 : ℝ) : ℂ)) * dslope scaleDifference ((1 / 2 : ℝ) : ℂ) z := by
            dsimp only [w]
            push_cast
            ring
        _ = _ := by simpa only [smul_eq_mul] using sub_smul_dslope_of_zero scaleDifference_half z
    change (if (1 : DirichletCharacter ℂ N) = 1 then
      scaleDifference z * (-logDeriv (principalRegular N) w) +
        dslope scaleDifference ((1 / 2 : ℝ) : ℂ) z / 2
      else _) = _
    rw [if_pos rfl, hlog, hds]
    change _ = scaleDifference z * (-logDeriv (LFunctionTrivChar N) w)
    ring
  · simp only [archivedGaussianFilteredDirichletLog, if_neg hχ]

/-- The principal branch uses Mathlib's pole-removed Dirichlet function. -/
theorem archivedGaussianFilteredDirichletLog_principal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) (hχ : χ = 1) :
    archivedGaussianFilteredDirichletLog χ z =
      scaleDifference z * (-logDeriv (LFunctionTrivChar₁ N) (2 * z)) +
        dslope scaleDifference ((1 / 2 : ℝ) : ℂ) z / 2 := by
  have he : principalRegular N = LFunctionTrivChar₁ N := by
    funext w
    by_cases hw : w = 1
    · subst w
      simp only [principalRegular, LFunctionTrivChar₁, Function.update_self, principalResidue]
    · simp only [principalRegular, LFunctionTrivChar₁, Function.update_of_ne hw]
  rw [archivedGaussianFilteredDirichletLog, if_pos hχ, he]

#print axioms archivedGaussianFilteredDirichletLog_principal
#print axioms archivedGaussianFilteredDirichletLog_analyticAt
#print axioms archivedGaussianFilteredDirichletLog_eq

end
end AlpogeSuperZeta
