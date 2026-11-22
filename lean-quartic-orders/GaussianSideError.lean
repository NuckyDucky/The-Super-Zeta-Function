import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The signed horizontal slope differs from its central value by an integral
over two disjoint regions. The input bounds on the signed theta kernel belong
to the quartic certificate. -/

open MeasureTheory Set

namespace GaussianSideError

noncomputable section

def averageCosh (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..1, Real.cosh (u*y)

theorem averageCosh_eq (y : ℝ) :
    averageCosh y = if y = 0 then 1 else Real.sinh y / y := by
  by_cases hy : y = 0
  · simp [averageCosh, hy]
  rw [if_neg hy, eq_div_iff hy, mul_comm]
  unfold averageCosh
  rw [intervalIntegral.mul_integral_comp_mul_right]
  simp only [zero_mul, one_mul]
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => Real.hasDerivAt_sinh x) (Real.continuous_cosh.intervalIntegrable 0 y))

theorem averageCosh_abs_mono {x y : ℝ} (h : |x| ≤ |y|) :
    averageCosh x ≤ averageCosh y := by
  apply intervalIntegral.integral_mono_on zero_le_one
    ((Real.continuous_cosh.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1)
    ((Real.continuous_cosh.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1)
  intro u _
  apply Real.cosh_le_cosh.mpr
  simpa only [abs_mul] using mul_le_mul_of_nonneg_left h (abs_nonneg u)

theorem one_le_averageCosh (y : ℝ) : 1 ≤ averageCosh y := by
  simpa [averageCosh_eq] using
    (averageCosh_abs_mono (x := 0) (y := y) (by simp))

theorem averageCosh_le_exp_abs (y : ℝ) : averageCosh y ≤ Real.exp |y| := by
  have local_bound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      Real.cosh (u*y) ≤ Real.exp |y| := by
    have h : |u*y| ≤ |y| := by
      rw [abs_mul, abs_of_nonneg hu.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hu.2
    have h₁ := Real.exp_le_exp.mpr ((le_abs_self _).trans h)
    have h₂ := Real.exp_le_exp.mpr ((neg_le_abs _).trans h)
    rw [Real.cosh_eq]
    linarith
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((Real.continuous_cosh.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1)
    (intervalIntegrable_const (c := Real.exp |y|)) local_bound
  simpa [averageCosh] using h

/-- Add the mass-weighted core error and the independently bounded integral tail. -/
theorem slope_lower {mass v : ℝ → ℝ} {a : ℝ} (ha : |a| ≤ 1/20)
    (hm : ∀ x ∈ Ici (0:ℝ), 0 ≤ mass x) (hv : ∀ x : ℝ, |v x| ≤ 1)
    (hmI : IntegrableOn mass (Ici 0))
    (hbase : IntegrableOn (fun x => mass x * v x) (Ici 0))
    (hside : IntegrableOn (fun x => mass x * v x * averageCosh (a*x)) (Ici 0))
    (htailI : IntegrableOn (fun x => mass x * Real.exp (x/20)) (Ioi 18))
    (hline : 519994 < ∫ x in Ici 0, mass x * v x)
    (hcurv : ∫ x in Ici 0, mass x ≤ 3565602)
    (htail : ∫ x in Ioi 18, mass x * Real.exp (x/20) ≤ (1:ℝ)/10^10)
    (hend : averageCosh (9/10) ≤ 11407/10000) :
    18000 < ∫ x in Ici 0, mass x * v x * averageCosh (a*x) := by
  let diff := fun x => mass x * v x - mass x * v x * averageCosh (a*x)
  have hd : IntegrableOn diff (Ici 0) := hbase.sub hside
  have hc : Icc (0 : ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1
  have ht : Ioi (18 : ℝ) ⊆ Ici 0 := fun _ hx => (by norm_num : (0 : ℝ) ≤ 18).trans hx.le
  have hdc := hd.mono_set hc
  have hdt := hd.mono_set ht
  have hdis : Disjoint (Icc (0:ℝ) 18) (Ioi 18) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  have hcov : Icc (0:ℝ) 18 ∪ Ioi 18 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro h
      by_cases hx : x ≤ 18
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  have hdebt (x) (hx : x ∈ Ici (0:ℝ)) :
      diff x ≤ mass x * (averageCosh (a*x) - 1) := by
    have h := mul_le_mul_of_nonneg_right ((abs_le.mp (hv x)).1)
      (sub_nonneg.mpr (one_le_averageCosh (a*x)))
    dsimp [diff]
    calc
      _ = mass x * (-(v x * (averageCosh (a*x) - 1))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (hm x hx)
  have hcore : ∫ x in Icc 0 18, diff x ≤
      (1407/10000 : ℝ) * ∫ x in Icc 0 18, mass x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hdc ((hmI.mono_set hc).const_mul _) measurableSet_Icc
    intro x hx
    have hax : |a*x| ≤ |(9:ℝ)/10| := by
      rw [abs_mul, abs_of_nonneg hx.1, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 9/10)]
      have h := mul_le_mul_of_nonneg_right ha hx.1
      linarith [hx.2]
    have hlim := (averageCosh_abs_mono hax).trans hend
    have hh := mul_le_mul_of_nonneg_left
      (show averageCosh (a*x)-1 ≤ (1407:ℝ)/10000 by linarith) (hm x (hc hx))
    exact (hdebt x (hc hx)).trans (by simpa only [mul_comm] using hh)
  have hfar : ∫ x in Ioi 18, diff x ≤ ∫ x in Ioi 18, mass x * Real.exp (x/20) := by
    apply setIntegral_mono_on hdt htailI measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := ht hx
    have hax := mul_le_mul_of_nonneg_right ha hx0
    have hh : |a*x| ≤ x/20 := by rw [abs_mul, abs_of_nonneg hx0]; linarith
    have hb := (averageCosh_le_exp_abs (a*x)).trans (Real.exp_le_exp.mpr hh)
    exact (hdebt x hx0).trans (mul_le_mul_of_nonneg_left (by linarith) (hm x hx0))
  have hmass : ∫ x in Icc 0 18, mass x ≤ ∫ x in Ici 0, mass x :=
    setIntegral_mono_set hmI ((ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall hm)) hc.eventuallyLE
  have hsplit := setIntegral_union hdis measurableSet_Ioi hdc hdt
  rw [hcov] at hsplit
  have hdiff : ∫ x in Ici 0, diff x =
      (∫ x in Ici 0, mass x * v x) - ∫ x in Ici 0, mass x * v x * averageCosh (a*x) :=
    integral_sub hbase hside
  linarith

#print axioms slope_lower

/-- A linear exponential majorant for the weighted tail of the theta kernel. -/
private def tailBound (x : ℝ) : ℝ :=
  (1944 * Real.exp 672) * Real.exp ((-39) * x)

private theorem weighted_le_tailBound {K : ℝ → ℝ} {x : ℝ} (hx : 18 ≤ x)
    (hK : K x ≤ 3 * Real.exp (x/2) * Real.exp (-40 * Real.exp (x-18))) :
    (2*K x*x^2) * Real.exp (x/20) ≤ tailBound x := by
  have hs : x ≤ 18 * Real.exp ((x-18)/18) := by
    linarith [Real.add_one_le_exp ((x-18)/18)]
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ x) hs 2
  have he : x/2 + -40 * Real.exp (x-18) + 2*((x-18)/18) + x/20 ≤
      672+(-39)*x := by linarith [Real.add_one_le_exp (x-18)]
  calc
    _ ≤ 2*(3*Real.exp (x/2)*Real.exp (-40 * Real.exp (x-18))) *
        (18*Real.exp ((x-18)/18))^2 * Real.exp (x/20) := by
      gcongr
    _ = 1944 * Real.exp (x/2 + -40 * Real.exp (x-18) + 2*((x-18)/18) + x/20) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, two_mul ((x-18)/18), Real.exp_add]
      ring
    _ ≤ 1944 * Real.exp (672+(-39)*x) := by gcongr
    _ = tailBound x := by rw [Real.exp_add]; unfold tailBound; ring

private theorem tailBound_integrable : IntegrableOn tailBound (Ioi 18) :=
  (integrableOn_exp_mul_Ioi (a := -39) (by norm_num) 18).const_mul _

private theorem integral_tailBound_lt :
    (∫ x in Ioi 18, tailBound x) < (1:ℝ)/10^10 := by
  have hv : Real.exp (30:ℝ) = (Real.exp 1)^30 := by
    norm_num [← Real.exp_nat_mul]
  have h₁ : (5/2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/2) h₁ 30
  rw [← hv] at hp
  unfold tailBound
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-39:ℝ) < 0)]
  have he : Real.exp 672 * Real.exp ((-39:ℝ)*18) = (Real.exp 30)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    norm_num
  calc
    _ = (1944/39) * (Real.exp 672 * Real.exp ((-39:ℝ)*18)) := by ring
    _ = (1944/39) / Real.exp 30 := by rw [he]; simp only [div_eq_mul_inv]
    _ < _ := by
      apply (div_lt_iff₀ (Real.exp_pos _)).mpr
      norm_num at hp ⊢
      linarith

/-- From the published pointwise theta envelope, the weighted tail is
integrable and smaller than the allowance used in the slope comparison. -/
theorem tail_of_kernel_majorant {K : ℝ → ℝ}
    (hK0 : ∀ x ∈ Ioi (18:ℝ), 0 ≤ K x)
    (hK : ∀ x ∈ Ioi (18:ℝ), K x ≤
      3 * Real.exp (x/2) * Real.exp (-40 * Real.exp (x-18)))
    (hm : AEStronglyMeasurable (fun x => (2*K x*x^2) * Real.exp (x/20))
      (volume.restrict (Ioi 18))) :
    IntegrableOn (fun x => (2*K x*x^2) * Real.exp (x/20)) (Ioi 18) ∧
      (∫ x in Ioi 18, (2*K x*x^2) * Real.exp (x/20)) < (1:ℝ)/10^10 := by
  have hmj (x : ℝ) (hx : x ∈ Ioi (18:ℝ)) :=
    weighted_le_tailBound hx.le (hK x hx)
  have hi : IntegrableOn (fun x => (2*K x*x^2) * Real.exp (x/20)) (Ioi 18) := by
    apply tailBound_integrable.mono' hm
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro x hx
    have h0 := hK0 x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmj x hx
  exact ⟨hi, (setIntegral_mono_on hi tailBound_integrable measurableSet_Ioi hmj).trans_lt
    integral_tailBound_lt⟩

#print axioms tail_of_kernel_majorant

end
end GaussianSideError
