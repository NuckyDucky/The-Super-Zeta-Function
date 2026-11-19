import SuperZeta.DiskRemoval
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A finite Blaschke-product estimate gives square-root growth of the counting
function and absolute summability of the reciprocal zeros. The division by a
finite list of simple linear factors follows the repository's DiskRemoval. -/
noncomputable section
namespace DottieOriented.RootCount
open Complex Metric Set Filter
open scoped Topology BigOperators

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

private theorem boundary_eq {a z : ℂ} {R : ℝ} (ha : a ≠ 0)
    (hR : 0<R) (hz : ‖z‖=R) :
    ‖1-star a*z/(R:ℂ)^2‖ = (‖a‖/R)*‖1-z/a‖ := by
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
  field_simp [norm_ne_zero_iff.mpr ha]
  ring

/-- For any finite selection in the inner half disk, every selected zero
costs a factor of two in the maximum modulus on the outer circle. -/
theorem finite_zero_count {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ)
    (hE : Differentiable ℂ E) (h0 : E 0=1) (inj : Function.Injective l)
    (root : ∀ j, E (l j)=0) (S : Finset ι) {R M : ℝ} (hR : 0<R)
    (half : ∀ j∈S, ‖l j‖ ≤ R/2) (bound : ∀ z, ‖z‖=R → ‖E z‖≤M) :
    (2:ℝ)^S.card ≤ M := by
  classical
  have hn (j) : l j ≠ 0 := by
    intro he; simpa [he,h0] using root j
  obtain ⟨f,hf,ef⟩ := peel_finite E l hE inj hn root S
  let A (z : ℂ) := ∏ j ∈ S, (1-z/l j)
  let B (z : ℂ) := ∏ j ∈ S, (1-star (l j)*z/(R:ℂ)^2)
  have hd : Differentiable ℂ B := Differentiable.finset_prod
    (fun j _ => (differentiable_const (1:ℂ)).sub ((differentiable_id.const_mul _).div_const _))
  have bnd (z : ℂ) (hz : ‖z‖=R) : ‖B z‖ ≤ (1/2:ℝ)^S.card * ‖A z‖ := by
    simp only [B,A,norm_prod]
    calc
      _ ≤ ∏ j ∈ S, ((1/2:ℝ)* ‖1-z/l j‖) := by
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro j hj
        rw [boundary_eq (hn j) hR hz]
        exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hR).mpr (by linarith [half j hj])) (norm_nonneg _)
      _ = _ := by simp [Finset.prod_mul_distrib]
  have max0 : ‖f 0 * B 0‖ ≤ (1/2:ℝ)^S.card*M := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U:=ball (0:ℂ) R) isBounded_ball
      (hf.mul hd).differentiableOn.diffContOnCl
    · rw [frontier_ball _ hR.ne']
      intro z hz
      have hz' : ‖z‖=R := by simpa [mem_sphere,dist_zero_right] using hz
      rw [norm_mul]
      calc
        _ ≤ ‖f z‖*((1/2:ℝ)^S.card * ‖A z‖) :=
          mul_le_mul_of_nonneg_left (bnd z hz') (norm_nonneg _)
        _ = (1/2:ℝ)^S.card * ‖E z‖ := by rw [ef z, norm_mul]; dsimp [A]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (bound z hz') (by positivity)
    · exact subset_closure (mem_ball_self hR)
  have hf0 : f 0 = 1 := by simpa [h0] using (ef 0).symm
  simp [B,hf0] at max0
  rwa [← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul] at max0

/-- Dyadic annuli in the square-root variable turn the finite zero count
into an absolutely convergent geometric majorant over all reciprocal roots. -/
theorem summable_reciprocal {ι : Type*} (E : ℂ → ℂ) (l : ι → ℂ)
    (hE : Differentiable ℂ E) (h0 : E 0=1) (inj : Function.Injective l)
    (root : ∀ j, E (l j)=0) {K : ℝ} (hK : 0<K)
    (growth : ∀ w : ℂ, 1 ≤ ‖w‖ → ‖E w‖ ≤ Real.exp (K*(Real.sqrt ‖w‖+1))) :
    Summable fun j => ‖l j‖⁻¹ := by
  classical
  have away : ∀ᶠ z in 𝓝 (0:ℂ), E z ≠ 0 :=
    hE.continuous.continuousAt.tendsto.eventually (eventually_ne_nhds (h0.trans_ne one_ne_zero))
  obtain ⟨d,hd,hdisk⟩ := Metric.mem_nhds_iff.mp away
  have outside (j) : d ≤ ‖l j‖ := by
    by_contra! h
    exact hdisk (mem_ball_zero_iff.mpr h) (root j)
  have locate (j : ι) : ∃ n : ℕ, ‖l j‖ ≤ (4:ℝ)^n :=
    (pow_unbounded_of_one_lt ‖l j‖ (by norm_num : (1:ℝ)<4)).imp fun _ h => h.le
  let idx (j : ι) := Nat.find (locate j)
  let B := max d⁻¹ 4
  have hB : 0 ≤ B := le_trans (by norm_num : (0:ℝ) ≤ 4) (le_max_right _ _)
  have weight (j : ι) (k : ℕ) (hh : idx j = k) : ‖l j‖⁻¹ ≤ B / (4:ℝ)^k := by
    cases k with
    | zero =>
      simp only [pow_zero,div_one]
      exact (inv_anti₀ hd (outside j)).trans (le_max_left _ _)
    | succ k =>
      have small : (4:ℝ)^k < ‖l j‖ := by
        apply lt_of_not_ge
        exact Nat.find_min (locate j) (show k < idx j by omega)
      have hnum : ‖l j‖⁻¹ * (4:ℝ)^k ≤ 1 := by
        rw [← div_eq_inv_mul, div_le_one (hd.trans_le (outside j))]
        exact small.le
      rw [le_div_iff₀ (by positivity), pow_succ, ← mul_assoc]
      exact le_trans (by linarith : ‖l j‖⁻¹ * 4^k * 4 ≤ 4) (le_max_right _ _)
  let C := 3*K / Real.log 2
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have count (S : Finset ι) (k : ℕ) (inside : ∀ j ∈ S, ‖l j‖ ≤ (4:ℝ)^k) :
      (S.card:ℝ) ≤ C*(2:ℝ)^k := by
    let R : ℝ := (2*2^k)^2
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    have hR : 1 ≤ R := by dsimp [R]; nlinarith [sq_nonneg ((2:ℝ)^k-1)]
    have ident : (4:ℝ)^k = (2^k)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    have hcount := finite_zero_count E l hE h0 inj root S (R:=R)
      (lt_of_lt_of_le zero_lt_one hR)
      (fun j hj => (inside j hj).trans (by rw [ident]; dsimp [R]; nlinarith [sq_nonneg ((2:ℝ)^k)]))
      (fun z hz => (growth z (hz ▸ hR)).trans_eq (by rw [hz]))
    have logs := Real.log_le_log (show 0 < (2:ℝ)^S.card by positivity) hcount
    rw [Real.log_pow,Real.log_exp] at logs
    have hsqrt : Real.sqrt R = 2*2^k := Real.sqrt_sq (by positivity)
    rw [hsqrt] at logs
    dsimp [C]
    rw [div_mul_eq_mul_div, le_div_iff₀ logpos]
    nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hp)]
  let major (k : ℕ) := (C*B)*(1/2:ℝ)^k
  have hm : Summable major := (summable_geometric_of_lt_one (by norm_num : 0≤(1/2:ℝ))
      (by norm_num)).mul_left (C*B)
  apply summable_of_sum_le (fun j => inv_nonneg.mpr (norm_nonneg _)) (c:=∑' k, major k)
  intro S
  let T := S.image idx
  rw [← Finset.sum_fiberwise_of_maps_to (t:=T) (g:=idx) (fun _ hj => Finset.mem_image_of_mem _ hj)]
  apply le_trans (Finset.sum_le_sum (g:=fun k => major k) ?_)
  · exact hm.sum_le_tsum T (by intros; dsimp [major]; positivity)
  intro k _
  let F := S.filter fun j => idx j = k
  have card := count F k (fun j hj => by
    have e := (Finset.mem_filter.mp hj).2
    exact e ▸ Nat.find_spec (locate j))
  change ∑ j ∈ F, ‖l j‖⁻¹ ≤ _
  calc
    _ ≤ ∑ _j ∈ F, B / (4:ℝ)^k :=
      Finset.sum_le_sum fun j hj => weight j k (Finset.mem_filter.mp hj).2
    _ = (F.card:ℝ) * (B / (4:ℝ)^k) := by simp
    _ ≤ (C*(2:ℝ)^k)*(B/(4:ℝ)^k) :=
      mul_le_mul_of_nonneg_right card (by positivity)
    _ = major k := by
      dsimp [major]
      rw [div_pow]
      have hfour : (4:ℝ)^k = (2:ℝ)^k * 2^k := by rw [← mul_pow]; norm_num
      rw [hfour, one_pow]
      field_simp
      ring

end DottieOriented.RootCount
