import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Removing the zeros in a disk while controlling the boundary modulus. -/
namespace SuperZeta.Factorization
open Complex Metric Set
open scoped Topology BigOperators
noncomputable section

private theorem peel_finite {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ)
    (hE : Differentiable ℂ E) (hinj : Function.Injective l)
    (hne : ∀ j, l j ≠ 0) (hroot : ∀ j, E (l j)=0) (S : Finset ι) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ∀ z, E z = f z * ∏ j ∈ S, (1-z/l j) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨E,hE,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨f, hf, heq⟩ := ih
    have hp : (∏ j ∈ S, (1-l i/l j)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj h => ?_
      have eq : l i = l j := by
        have h' := (div_eq_iff (hne j)).mp (sub_eq_zero.mp h).symm
        simpa using h'
      exact hi (hinj eq ▸ hj)
    have hfi : f (l i)=0 := by
      exact (mul_eq_zero.mp ((heq (l i)).symm.trans (hroot i))).resolve_right hp
    have hd : Differentiable ℂ (dslope f (l i)) :=
      differentiableOn_univ.mp ((Complex.differentiableOn_dslope (Filter.univ_mem)).mpr hf.differentiableOn)
    refine ⟨fun z => -(l i) * dslope f (l i) z, hd.const_mul _, fun z => ?_⟩
    rw [Finset.prod_insert hi, heq z]
    have hdz := sub_smul_dslope f (l i) z
    rw [smul_eq_mul,hfi,sub_zero] at hdz
    rw [← hdz]
    field_simp [hne i]
    ring

private theorem boundary_factor {a z : ℂ} {R : ℝ} (ha : a ≠ 0)
    (haR : ‖a‖<R) (hz : ‖z‖=R) :
    ‖1-star a*z/(R:ℂ)^2‖ ≤ ‖1-z/a‖ := by
  have hR := (norm_nonneg a).trans_lt haR
  have hRc : (R:ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hzz : star z * z=(R:ℂ)^2 := by
    change (starRingEnd ℂ) z * z = _
    simpa [hz] using Complex.conj_mul' z
  have hrat : 1-star a*z/(R:ℂ)^2 = star (z-a)*z/(R:ℂ)^2 := by
    rw [star_sub,sub_mul,hzz]
    field_simp
  rw [hrat,show 1-z/a=(a-z)/a by field_simp]
  simp only [norm_div,norm_mul,norm_star,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hR,hz,norm_sub_rev z a]
  calc
    ‖a-z‖*R/R^2 = ‖a-z‖/R := by field_simp
    _ ≤ ‖a-z‖/‖a‖ := div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.mpr ha) haR.le

/-- After removing all simple roots in a disk, the normalized quotient is
entire, has no zeros in the open disk, and inherits the boundary norm bound. -/
theorem disk_removal {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ) (S : Finset ι)
    {R M : ℝ} (hR : 0<R) (hE : Differentiable ℂ E) (h0 : E 0=1)
    (hinj : Function.Injective l) (hroot : ∀ j, E (l j)=0)
    (hsimple : ∀ j, deriv E (l j) ≠ 0) (hinside : ∀ j∈S, ‖l j‖ < R)
    (hexhaust : ∀ z, ‖z‖ < R → E z=0 → ∃ j∈S, z=l j)
    (hbound : ∀ z, ‖z‖=R → ‖E z‖≤M) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ q 0=1 ∧ (∀ z, ‖z‖<R → q z ≠ 0) ∧
      (∀ z, ‖z‖<R → ‖q z‖≤M) ∧
      ∀ z, q z * (∏ j∈S, (1-z/l j)) = E z * (∏ j∈S, (1-star (l j)*z/(R:ℂ)^2)) := by
  classical
  have hne (j : ι) : l j ≠ 0 := by
    intro hj
    simpa [hj,h0] using hroot j
  obtain ⟨f,hf,hfprod⟩ := peel_finite E l hE hinj hne hroot S
  let A (z : ℂ) := ∏ j∈S, (1-z/l j)
  let B (z : ℂ) := ∏ j∈S, (1-star (l j)*z/(R:ℂ)^2)
  have hA : Differentiable ℂ A := by
    refine Differentiable.fun_finsetProd (u := S) (f := fun j z => (1:ℂ)-z/l j) ?_
    intro j _
    exact (differentiable_const (1:ℂ)).sub (differentiable_id.div_const (l j))
  have hB : Differentiable ℂ B := by
    refine Differentiable.fun_finsetProd (u := S)
      (f := fun j z => (1:ℂ)-star (l j)*z/(R:ℂ)^2) ?_
    intro j _
    exact (differentiable_const (1:ℂ)).sub ((differentiable_id.const_mul _).div_const _)
  have heq : E = fun z => f z * A z := funext hfprod
  let q (z : ℂ) := f z * B z
  have hq : Differentiable ℂ q := hf.mul hB
  have hfac (z : ℂ) : q z*A z=E z*B z := by rw [heq]; dsimp [q]; ring
  refine ⟨q,hq,?_,?_,?_,hfac⟩
  · have hf0 := hfprod 0
    simpa [q,B] using (by simpa [h0] using hf0.symm : f 0 = 1)
  · intro z hz
    have hfz : f z ≠ 0 := by
      intro hz0
      have hez : E z=0 := by simp [heq,hz0]
      obtain ⟨j,hj,rfl⟩ := hexhaust z hz hez
      have haz : A (l j)=0 := Finset.prod_eq_zero hj (by simp [hne j])
      apply hsimple j
      rw [heq,deriv_fun_mul (hf _) (hA _), hz0, haz]
      simp
    refine mul_ne_zero hfz (Finset.prod_ne_zero_iff.mpr fun j hj h => ?_)
    have hu : ‖star (l j)*z/(R:ℂ)^2‖ < 1 := by
      rw [norm_div,norm_mul,norm_star,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hR,div_lt_one (sq_pos_of_pos hR),sq]
      exact (mul_le_mul_of_nonneg_right (hinside j hj).le (norm_nonneg z)).trans_lt
        (mul_lt_mul_of_pos_left hz hR)
    rw [← sub_eq_zero.mp h, norm_one] at hu
    exact lt_irrefl _ hu
  · intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U:=ball (0:ℂ) R) isBounded_ball
      hq.differentiableOn.diffContOnCl
    · rw [frontier_ball _ hR.ne']
      intro w hw
      have hw' : ‖w‖=R := by simpa [mem_sphere,dist_zero_right] using hw
      calc
        ‖q w‖ = ‖f w‖ * ‖B w‖ := norm_mul _ _
        _ ≤ ‖f w‖ * ‖A w‖ := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simp only [A,B,norm_prod]
          exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi =>
            boundary_factor (hne i) (hinside i hi) hw'
        _ = ‖E w‖ := by rw [heq,norm_mul]
        _ ≤ M := hbound w hw'
    · apply subset_closure
      simpa [mem_ball] using hz

end
end SuperZeta.Factorization
