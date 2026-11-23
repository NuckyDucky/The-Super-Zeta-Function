import QuarticQuadrants
import QuarticKernel

open MeasureTheory

namespace QuarticKernel

private def onShell (n : ℕ) (j : Fin (n+1)) : Prop :=
  (j.val+1)^2 + (n-(j.val+1)^2).sqrt^2 = n

private instance (n : ℕ) (j : Fin (n+1)) : Decidable (onShell n j) := by
  unfold onShell
  infer_instance

private abbrev ShellIndex := Σ n : ℕ, {j : Fin (n+1) // onShell n j}

private def shellNorm (p : ℕ × ℕ) : ℕ := (p.1+1)^2+p.2^2

private def shellIndex (p : ℕ×ℕ) : ShellIndex :=
  ⟨shellNorm p, ⟨⟨p.1, by
      have h : p.1 ≤ (p.1+1)^2 := by nlinarith
      exact h.trans_lt (Nat.lt_succ_of_le (Nat.le_add_right _ _))⟩,
    by simp [onShell, shellNorm, Nat.sqrt_eq']⟩⟩

private def quarterIndex (p : ShellIndex) : ℕ×ℕ :=
  (p.2.val.val, (p.1-(p.2.val.val+1)^2).sqrt)

private theorem shell_ext {p q : ShellIndex} (hn : p.1 = q.1)
    (hj : p.2.val.val = q.2.val.val) : p = q := by
  rcases p with ⟨n,i⟩
  rcases q with ⟨m,j⟩
  dsimp only at hn hj
  subst m
  exact congrArg (Sigma.mk n) (Subtype.ext (Fin.ext hj))

private theorem quarterIndex_shellIndex (p : ℕ × ℕ) : quarterIndex (shellIndex p) = p := by
  simp [shellIndex, quarterIndex, shellNorm, Nat.sqrt_eq']

private theorem shellIndex_norm (p : ℕ × ℕ) : (shellIndex p).1 = shellNorm p := rfl

private theorem shellIndex_addr (p : ℕ × ℕ) : (shellIndex p).2.val.val = p.1 := rfl

private theorem quarterIndex_norm (p : ShellIndex) : shellNorm (quarterIndex p) = p.1 :=
  p.2.property

set_option maxRecDepth 8000 in
private theorem shellIndex_quarterIndex (p : ShellIndex) : shellIndex (quarterIndex p) = p := by
  exact @shell_ext (shellIndex (quarterIndex p)) p
    ((shellIndex_norm (quarterIndex p)).trans (quarterIndex_norm p))
    (shellIndex_addr (quarterIndex p))

private def shellEquiv : (ℕ × ℕ) ≃ ShellIndex where
  toFun := shellIndex
  invFun := quarterIndex
  left_inv := quarterIndex_shellIndex
  right_inv := shellIndex_quarterIndex

private theorem row_zero_off_shell (n : ℕ) (j : Fin (n+1)) (h : ¬ onShell n j) :
    row n j.val = 0 := by
  have hz : ¬ ((j.val+1)*(j.val+1) +
      (n-(j.val+1)*(j.val+1)).sqrt*(n-(j.val+1)*(j.val+1)).sqrt=n) := by
    simpa only [onShell, pow_two] using h
  simp only [row, if_neg hz]

private theorem coeff_sum_wider (n : ℕ) :
    coeff n = ∑ j ∈ Finset.range (n+1), row n j := by
  unfold coeff
  refine Finset.sum_subset (Finset.range_mono (le_trans (Nat.sqrt_le_self n) (by omega))) ?_
  intro j _ hj
  have hj' : n.sqrt < j+1 := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  have hs := Nat.sqrt_lt'.mp hj'
  have hz : ¬ ((j+1)*(j+1)+(n-(j+1)*(j+1)).sqrt*(n-(j+1)*(j+1)).sqrt=n) := by
    rw [pow_two] at hs
    omega
  simp only [row, if_neg hz]

private theorem shell_sum (n : ℕ) (r : ℝ) :
    (∑ j : {j : Fin (n+1) // onShell n j}, (row n j.val.val : ℝ)*r^n) =
      (coeff n : ℝ)*r^n := by
  rw [coeff_sum_wider, Int.cast_sum, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
  rw [← Finset.subtype_univ (onShell n),
    Finset.sum_subtype_eq_sum_filter (fun j : Fin (n+1) => (row n j.val : ℝ)*r^n),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : onShell n j
  · rw [if_pos hj]
  · simp [hj, row_zero_off_shell n j hj]

private theorem shell_abs_summable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable fun p : ShellIndex => ‖(row p.1 p.2.val.val : ℝ)*r^p.1‖ := by
  have hR : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr] using hr1
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  have hG : Summable (fun (n : ℕ) => ((n:ℝ)+1)*r^n) := by
    convert ((hasSum_coe_mul_geometric_of_norm_lt_one hR).summable.add
      (hasSum_geometric_of_norm_lt_one hR).summable) using 1
    ext n
    ring
  refine Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _)) ?_ hG
  intro n
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _j : {j : Fin (n+1) // onShell n j}, r^n := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr.le _)]
      have h : |(row n j.val.val : ℝ)| ≤ 1 := by exact_mod_cast row_abs_le_one n j.val.val
      simpa using mul_le_mul_of_nonneg_right h (pow_nonneg hr.le n)
    _ ≤ ((n:ℝ)+1)*r^n := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
      have hc := (Fintype.card_subtype_le (onShell n)).trans (Fintype.card_fin _).le
      exact_mod_cast hc

theorem theta_quarter_lattice {u : ℝ} (hu : 0 < u) :
    theta u = ∑' p : ℕ×ℕ,
      (SuperZeta.FieldWeights.conductorReading (p.1+1) p.2 : ℝ) *
        Real.exp (-u*((p.1+1:ℝ)^2+(p.2:ℝ)^2)) := by
  let r := Real.exp (-u)
  have hr := Real.exp_pos (-u)
  have hr' : r<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  let f (p : ShellIndex) : ℝ := (row p.1 p.2.val.val : ℝ)*r^p.1
  have hf : Summable f := (shell_abs_summable hr hr').of_norm
  calc
    _ = ∑' p : ShellIndex, f p := by
      rw [hf.tsum_sigma' (fun _ => Summable.of_finite)]
      simp only [tsum_fintype, f, shell_sum]
      rfl
    _ = ∑' p : ℕ×ℕ, f (shellEquiv p) := (shellEquiv.tsum_eq f).symm
    _ = _ := by
      apply tsum_congr
      intro p
      dsimp [f, shellEquiv, shellIndex, shellNorm]
      rw [row]
      simp only [← pow_two, Nat.add_sub_cancel_left, Nat.sqrt_eq', if_pos rfl]
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf

#print axioms theta_quarter_lattice

open QuarticFiniteFourier

private theorem shell_row_value (p : ℕ × ℕ) :
    row (shellNorm p) p.1 =
      SuperZeta.FieldWeights.conductorReading ((p.1:ℤ)+1) p.2 := by
  simp only [row, shellNorm, ← pow_two, Nat.add_sub_cancel_left, Nat.sqrt_eq', if_pos rfl,
    Nat.cast_add, Nat.cast_one, if_true]

private theorem shell_exp (A : ℝ) (p : ℕ × ℕ) :
    Complex.exp (-Real.pi*(A:ℂ)*((((p.1:ℤ)+1:ℤ):ℂ)^2+(((p.2:ℤ):ℂ))^2)) =
      (Real.exp (-(Real.pi*A))^shellNorm p : ℝ) := by
  rw [← Real.exp_nat_mul, Complex.ofReal_exp]
  congr 1
  simp only [shellNorm, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast]
  push_cast
  ring

set_option maxHeartbeats 500000 in
set_option maxRecDepth 8000 in
private theorem quarterTerm_shell (A : ℝ) (p : ℕ × ℕ) :
    quarterTerm A p =
      ((row (shellNorm p) p.1 : ℝ) * Real.exp (-(Real.pi*A))^shellNorm p : ℝ) := by
  change (SuperZeta.FieldWeights.conductorReading ((p.1:ℤ)+1) p.2 : ℂ) *
      Complex.exp (-Real.pi*(A:ℂ)*((((p.1:ℤ)+1:ℤ):ℂ)^2+(((p.2:ℤ):ℂ))^2)) = _
  rw [shell_exp, Complex.ofReal_mul, Complex.ofReal_intCast, shell_row_value]

theorem gaussianLattice_theta {A : ℝ} (hA : 0 < A) :
    gaussianLattice A = 4 * (theta (Real.pi*A) : ℂ) := by
  let u := Real.pi*A
  have hu : 0 < u := mul_pos Real.pi_pos hA
  let f (p : ShellIndex) := (row p.1 p.2.val.val : ℝ)*Real.exp (-u)^p.1
  have hf : Summable fun p => ‖f p‖ :=
    shell_abs_summable (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  have hf' : Summable fun p : ℕ×ℕ => ‖f (shellEquiv p)‖ :=
    hf.comp_injective shellEquiv.injective
  have hf'' : Summable fun p : ℕ×ℕ => ‖quarterTerm A p‖ := by
    refine hf'.congr fun p => ?_
    rw [quarterTerm_shell, Complex.norm_real]
    rfl
  have htheta : theta u = ∑' p : ShellIndex, f p := by
    rw [hf.of_norm.tsum_sigma' (fun _ => Summable.of_finite)]
    simp only [tsum_fintype, f, shell_sum]
    rfl
  rw [gaussianLattice_four_quarters A hf'', ← show u = Real.pi*A from rfl, htheta,
    ← shellEquiv.tsum_eq f, Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro p
  exact quarterTerm_shell A p

private theorem rootD_pos : 0 < Real.sqrt (D:ℝ) := by positivity

private theorem rootD_sq : Real.sqrt (D:ℝ)^2 = (D:ℝ) := Real.sq_sqrt (by positivity)

private theorem inverse_dual_coordinate {t : ℝ} (ht : 0 < t) :
    1/((D:ℝ)*(t/Real.sqrt D)) = t⁻¹/Real.sqrt D := by
  field_simp [ht.ne', rootD_pos.ne']
  change Real.sqrt (D:ℝ) * (t * Real.sqrt (D:ℝ)) = (D:ℝ) * t
  rw [mul_left_comm, ← pow_two, rootD_sq, mul_comm]

private theorem scale_coordinate (t : ℝ) : Real.pi*(t/Real.sqrt D) = t/scale := by
  change Real.pi*(t/Real.sqrt (D:ℝ)) = t/(Real.sqrt (D:ℝ)/Real.pi)
  rw [div_div_eq_mul_div]
  ring

theorem gaussAmplitude_of_center_nonzero (hc : theta (1/scale) ≠ 0) :
    gaussAmplitude = (Real.sqrt D : ℂ) := by
  have hA : (0:ℝ) < 1/Real.sqrt D := div_pos one_pos rootD_pos
  have ht := gaussian_lattice_transform hA
  rw [inverse_dual_coordinate (by norm_num : (0:ℝ)<1), inv_one] at ht
  have h0 : gaussianLattice (1/Real.sqrt D) ≠ 0 := by
    rw [gaussianLattice_theta hA, scale_coordinate]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast hc)
  apply mul_right_cancel₀ h0
  rw [ht, ← Complex.ofReal_inv, inv_div, div_one]

/-- A nonzero value at the self-dual scale fixes the positive Gauss sign and
therefore the exact reflection of the original signed norm series. -/
theorem theta_reflection_of_center_nonzero (hc : theta (1/scale) ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    theta (t/scale) = t⁻¹ * theta (t⁻¹/scale) := by
  have ha := gaussian_lattice_transform (div_pos ht rootD_pos)
  rw [gaussAmplitude_of_center_nonzero hc, inverse_dual_coordinate ht,
    gaussianLattice_theta (div_pos ht rootD_pos),
    gaussianLattice_theta (div_pos (inv_pos.mpr ht) rootD_pos),
    scale_coordinate, scale_coordinate] at ha
  have h' : Real.sqrt (D:ℝ) * (4 * theta (t/scale)) =
      (t/Real.sqrt D)⁻¹ * (4 * theta (t⁻¹/scale)) := by
    exact_mod_cast ha
  rw [inv_div, div_eq_mul_inv (Real.sqrt (D:ℝ)) t] at h'
  apply mul_left_cancel₀ (show ((4:ℝ)*Real.sqrt D) ≠ 0 by positivity)
  linear_combination h'

#print axioms gaussianLattice_theta
#print axioms gaussAmplitude_of_center_nonzero
#print axioms theta_reflection_of_center_nonzero

end QuarticKernel
