import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The second logarithmic derivative of a locally uniform Hadamard product.
Zeros are indexed with multiplicity. A finite genus-one product can absorb
its constant factors and linear exponentials into the affine exponential.
Both coefficients may therefore depend on the finite subset. -/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace SuperZeta.ZeroMoment

variable {ι : Type*}

/-- Finite product with its affine exponential normalization. -/
def partialProduct (ρ : ι → ℂ) (s : Finset ι) (a b : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (a + b*z) * ∏ j ∈ s, (z - ρ j)

private theorem diff_partial (ρ : ι → ℂ) (s : Finset ι) (a b : ℂ) :
    Differentiable ℂ (partialProduct ρ s a b) := by
  unfold partialProduct
  fun_prop

private theorem logDeriv_partial (ρ : ι → ℂ) (s : Finset ι) (a b x : ℂ)
    (h : ∀ j ∈ s, x ≠ ρ j) :
    logDeriv (partialProduct ρ s a b) x = b + ∑ j ∈ s, (x - ρ j)⁻¹ := by
  classical
  unfold partialProduct
  have ha : HasDerivAt (fun z : ℂ => a + b*z) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add a
  rw [logDeriv_mul (f := fun z : ℂ => Complex.exp (a + b*z))
    (g := fun z : ℂ => ∏ j ∈ s, (z - ρ j)) x (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr
    (fun j hj => sub_ne_zero.mpr (h j hj))) (by fun_prop) (by fun_prop)]
  simp only [logDeriv_prod s (fun j z => z - ρ j) x
    (fun j hj => sub_ne_zero.mpr (h j hj)) (fun _ _ => by fun_prop)]
  congr 1
  · rw [logDeriv_apply, ha.cexp.deriv]
    field_simp
  · apply Finset.sum_congr rfl
    intro j _
    have hd : HasDerivAt (fun z : ℂ => z - ρ j) 1 x := (hasDerivAt_id x).sub_const _
    rw [logDeriv_apply, hd.deriv, one_div]

/-- Differentiating the finite product's logarithmic derivative removes both
normalization coefficients. Repeated roots contribute once per index. -/
theorem finite_zero_moment (ρ : ι → ℂ) (s : Finset ι) (a b x : ℂ)
    (h : ∀ j ∈ s, x ≠ ρ j) :
    deriv (logDeriv (partialProduct ρ s a b)) x = ∑ j ∈ s, -(1 / (x - ρ j)^2) := by
  have he : ∀ᶠ y in 𝓝 x, ∀ j ∈ s, y ≠ ρ j :=
    s.eventually_all.mpr fun j hj => isOpen_ne.mem_nhds (h j hj)
  have hd : ∀ j ∈ s, HasDerivAt (fun z : ℂ => (z-ρ j)⁻¹) (-(1/(x-ρ j)^2)) x := by
    intro j hj
    simpa only [neg_div, one_div, id_eq] using
      (((hasDerivAt_id x).sub_const (ρ j)).inv (sub_ne_zero.mpr (h j hj)))
  exact ((HasDerivAt.sum hd).const_add b |>.congr_of_eventuallyEq
    (he.mono fun y hy => logDeriv_partial ρ s a b y hy)).deriv

private theorem deriv_logDeriv_eq {f : ℂ → ℂ} {x : ℂ}
    (hf : DifferentiableAt ℂ f x) (hf' : DifferentiableAt ℂ (deriv f) x)
    (hx : f x ≠ 0) :
    deriv (logDeriv f) x =
      ((deriv (deriv f) x) * f x - deriv f x * deriv f x) / (f x)^2 := by
  exact (hf'.hasDerivAt.div hf.hasDerivAt hx).deriv

/-- A locally uniform product representation on an open neighborhood suffices
to obtain the unordered sum over its zeros, including multiplicities.
The hypotheses concern the functions themselves, with no derivative or
zero-sum identity assumed. -/
theorem hasSum_zero_moment (ρ : ι → ℂ) (a b : Finset ι → ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (x : ℂ) (hx : x ∈ U)
    (hprod : TendstoLocallyUniformlyOn (fun s => partialProduct ρ s (a s) (b s)) f atTop U)
    (hfx : f x ≠ 0) (hρ : ∀ j, x ≠ ρ j) :
    HasSum (fun j => -(1/(x-ρ j)^2)) (deriv (logDeriv f) x) := by
  classical
  let P := fun s : Finset ι => partialProduct ρ s (a s) (b s)
  have hP (s : Finset ι) : DifferentiableOn ℂ (P s) U :=
    (diff_partial ρ s (a s) (b s)).differentiableOn
  have he : ∀ᶠ s in (atTop : Filter (Finset ι)), DifferentiableOn ℂ (P s) U :=
    Eventually.of_forall hP
  have he' : ∀ᶠ s in (atTop : Filter (Finset ι)), DifferentiableOn ℂ (deriv (P s)) U :=
    Eventually.of_forall fun s => (hP s).deriv hU
  have hf := hprod.differentiableOn he hU
  have h1 := hprod.deriv he hU
  have h0x : Tendsto (fun s => P s x) atTop (𝓝 (f x)) := hprod.tendsto_at hx
  have h1x : Tendsto (fun s => deriv (P s) x) atTop (𝓝 (deriv f x)) := h1.tendsto_at hx
  have h2x : Tendsto (fun s => deriv (deriv (P s)) x) atTop (𝓝 (deriv (deriv f) x)) :=
    (h1.deriv he' hU).tendsto_at hx
  have ht := ((h2x.mul h0x).sub (h1x.mul h1x)).div (h0x.pow 2) (pow_ne_zero 2 hfx)
  rw [deriv_logDeriv_eq (hf.differentiableAt (hU.mem_nhds hx))
    ((hf.deriv hU).differentiableAt (hU.mem_nhds hx)) hfx]
  apply ht.congr'
  apply Eventually.of_forall
  intro s
  change (deriv (deriv (P s)) x * P s x - deriv (P s) x * deriv (P s) x) /
    (P s x)^2 = ∑ j ∈ s, -(1/(x-ρ j)^2)
  rw [← finite_zero_moment ρ s (a s) (b s) x (fun j _ => hρ j)]
  symm
  apply deriv_logDeriv_eq ((hP s).differentiableAt (hU.mem_nhds hx))
    (((hP s).deriv hU).differentiableAt (hU.mem_nhds hx))
  exact mul_ne_zero (Complex.exp_ne_zero _) (Finset.prod_ne_zero_iff.mpr
    (fun j _ => sub_ne_zero.mpr (hρ j)))

/-- The signed zero statistic, with the orientation of the imaginary axis fixed. -/
def signedMoment (ρ : ι → ℂ) (x : ℝ) : ℝ :=
  -(∑' j, 1/((x : ℂ)-ρ j)^2).im

theorem signedMoment_conj (ρ : ι → ℂ) (x : ℝ) :
    signedMoment (fun j => star (ρ j)) x = -signedMoment ρ x := by
  have h : (∑' j, 1 / ((x : ℂ) - star (ρ j))^2) =
      star (∑' j, 1/((x : ℂ)-ρ j)^2) := by
    rw [show (star (∑' j, 1/((x : ℂ)-ρ j)^2)) =
      (starRingEnd ℂ) (∑' j, 1/((x : ℂ)-ρ j)^2) from rfl, Complex.conj_tsum]
    simp
  unfold signedMoment
  rw [h]
  simp

theorem im_deriv_logDeriv_eq_signedMoment (ρ : ι → ℂ) (a b : Finset ι → ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (x : ℝ) (hx : (x : ℂ) ∈ U)
    (hprod : TendstoLocallyUniformlyOn (fun s => partialProduct ρ s (a s) (b s)) f atTop U)
    (hfx : f x ≠ 0) (hρ : ∀ j, (x : ℂ) ≠ ρ j) :
    (deriv (logDeriv f) (x : ℂ)).im = signedMoment ρ x := by
  rw [← (hasSum_zero_moment ρ a b f U hU x hx hprod hfx hρ).tsum_eq, tsum_neg]
  rfl

/-- Reindexing, including repeated indices representing multiplicities,
does not change the measurement. -/
theorem signedMoment_reindex {κ : Type*} (ρ : κ → ℂ) (e : ι ≃ κ) (x : ℝ) :
    signedMoment (ρ ∘ e) x = signedMoment ρ x := by
  exact congrArg (fun z : ℂ => -z.im) (e.tsum_eq (fun j => 1/((x : ℂ)-ρ j)^2))

/-- A nonzero value certifies that no multiplicity-preserving relabeling can
identify an indexed complex zero family with its conjugate. -/
theorem no_conjugate_reindex (ρ : ι → ℂ) (x : ℝ) (h : signedMoment ρ x ≠ 0) :
    ¬ ∃ e : ι ≃ ι, ∀ j, ρ (e j) = star (ρ j) := by
  rintro ⟨e, he⟩
  have eqf : ρ ∘ e = fun j => star (ρ j) := funext he
  have eqv := signedMoment_reindex ρ e x
  rw [eqf, signedMoment_conj] at eqv
  exact h (by linarith)

end SuperZeta.ZeroMoment
