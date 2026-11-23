import QuarticDualIndex
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Filter Asymptotics
open QuarticDualArithmetic

namespace QuarticFiniteFourier

private noncomputable def twistedTerm (A y : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (-Real.pi*(A:ℂ)*(n:ℂ)^2+2*Real.pi*Complex.I*(y:ℂ)*(n:ℂ))

private noncomputable def shiftedTerm (A y : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (-Real.pi/(A:ℂ)*((n:ℂ)-(y:ℂ))^2)

private noncomputable def residueShift (h : ZMod D) : ℝ := (h.val : ℝ) / D

private theorem summable_quadratic_norm {a b : ℂ} (ha : a.re < 0) :
    Summable fun n : ℤ => ‖Complex.exp (a*(n:ℂ)^2+b*(n:ℂ))‖ := by
  have h := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ha b (-2)).isBigO.comp_tendsto
    Int.tendsto_coe_cofinite
  have h' := summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ) < 2)) h.norm_left
  simpa only [Function.comp_def, Complex.ofReal_intCast] using h'

private theorem twisted_summable {A : ℝ} (hA : 0 < A) (y : ℝ) :
    Summable fun n : ℤ => ‖twistedTerm A y n‖ := by
  apply summable_quadratic_norm
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hA

private theorem shifted_summable {A : ℝ} (hA : 0 < A) (y : ℝ) :
    Summable fun n : ℤ => ‖shiftedTerm A y n‖ := by
  let z : ℂ := -Real.pi/(A:ℂ)
  have hz : z.re < 0 := by
    dsimp [z]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hA
  have h := (summable_quadratic_norm (b := -2*z*(y:ℂ)) hz).mul_right
    ‖Complex.exp (z*(y:ℂ)^2)‖
  refine h.congr fun n => ?_
  rw [← norm_mul, ← Complex.exp_add, shiftedTerm]
  congr 2
  dsimp only [z]
  ring

noncomputable def gaussianLattice (A : ℝ) : ℂ :=
  ∑' p : ℤ × ℤ, (SuperZeta.FieldWeights.conductorReading p.1 p.2 : ℂ) *
    Complex.exp (-Real.pi*(A:ℂ)*((p.1:ℂ)^2+(p.2:ℂ)^2))

private theorem phase_product (A : ℝ) (h : ZMod D) (m n : ℤ) :
    ZMod.stdAddChar (h*((m:ZMod D)+(R:ZMod D)*(n:ZMod D))) *
      Complex.exp (-Real.pi*(A:ℂ)*((m:ℂ)^2+(n:ℂ)^2)) =
    twistedTerm A (residueShift h) m * twistedTerm A ((r:ℝ)*residueShift h) n := by
  have hh : h*((m:ZMod D)+(R:ZMod D)*(n:ZMod D)) =
      ((((h.val:ℤ)*(m+r*n)):ℤ):ZMod D) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
  rw [hh, ZMod.stdAddChar_coe, twistedTerm, twistedTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [residueShift, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_intCast, Int.cast_mul, Int.cast_add, Int.cast_natCast]
  ring

private theorem twisted_expansion {A : ℝ} (hA : 0 < A) :
    gaussAmplitude * gaussianLattice A =
      ∑ h : ZMod D, quarticCharacter h *
        ((∑' m : ℤ, twistedTerm A (residueShift h) m) *
          ∑' n : ℤ, twistedTerm A ((r:ℝ)*residueShift h) n) := by
  let f (h : ZMod D) (p : ℤ×ℤ) := quarticCharacter h *
    (twistedTerm A (residueShift h) p.1 * twistedTerm A ((r:ℝ)*residueShift h) p.2)
  have hs (h : ZMod D) : Summable (f h) :=
    (summable_mul_of_summable_norm (twisted_summable hA _) (twisted_summable hA _)).mul_left _
  unfold gaussianLattice
  rw [← tsum_mul_left]
  calc
    _ = ∑' p : ℤ × ℤ, ∑ h : ZMod D, f h p := by
      apply tsum_congr
      intro p
      rw [← mul_assoc, character_expansion p.1 p.2, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      dsimp only [f]
      rw [← phase_product, ← mul_assoc]
      rfl
    _ = ∑ h : ZMod D, ∑' p : ℤ × ℤ, f h p :=
      Summable.tsum_finsetSum (fun h _ => hs h)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [tsum_mul_tsum_of_summable_norm (twisted_summable hA _) (twisted_summable hA _)]
      simpa only [f] using (tsum_mul_left (a := quarticCharacter h))

private theorem poisson_prefactor {A : ℝ} (hA : 0 < A) :
    (1/(A:ℂ)^(1/2:ℂ))*(1/(A:ℂ)^(1/2:ℂ)) = (A:ℂ)⁻¹ := by
  have hs : ((A:ℂ)^(1/2:ℂ)) = (Real.sqrt A : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hA.le]
    norm_num
  rw [hs, div_mul_div_comm, one_mul, one_div, ← Complex.ofReal_mul, ← pow_two,
    Real.sq_sqrt hA.le]

private theorem shifted_product {A : ℝ} (hA : 0 < A) (h : ZMod D) :
    (∑' m : ℤ, twistedTerm A (residueShift h) m) *
      (∑' n : ℤ, twistedTerm A ((r:ℝ)*residueShift h) n) =
    (A:ℂ)⁻¹ * ∑' p : ℤ × ℤ,
      shiftedTerm A (residueShift h) p.1 * shiftedTerm A ((r:ℝ)*residueShift h) p.2 := by
  have h₁ := twisted_gaussian A (residueShift h) hA
  have h₂ := twisted_gaussian A ((r:ℝ)*residueShift h) hA
  change (∑' m, twistedTerm A (residueShift h) m) =
    (1/(A:ℂ)^(1/2:ℂ))*(∑' m, shiftedTerm A (residueShift h) m) at h₁
  change (∑' n, twistedTerm A ((r:ℝ)*residueShift h) n) =
    (1/(A:ℂ)^(1/2:ℂ))*(∑' n, shiftedTerm A ((r:ℝ)*residueShift h) n) at h₂
  rw [h₁,h₂,mul_mul_mul_comm,poisson_prefactor hA,
    tsum_mul_tsum_of_summable_norm (shifted_summable hA _) (shifted_summable hA _)]

private theorem shifted_weight {A : ℝ} (hA : 0 < A)
    (p : ZMod D × ℤ × ℤ) (u v : ℤ) (h : shiftedDualEquiv p = gaussianDualEquiv (u,v)) :
    quarticCharacter p.1 *
      (shiftedTerm A (residueShift p.1) p.2.1 *
        shiftedTerm A ((r:ℝ)*residueShift p.1) p.2.2) =
    (SuperZeta.FieldWeights.conductorReading u (-v) : ℂ) *
      Complex.exp (-Real.pi*((1/((D:ℝ)*A):ℝ):ℂ)*((u:ℂ)^2+(((-v:ℤ):ℂ))^2)) := by
  rw [shifted_frequency_character p u v h, shiftedTerm, shiftedTerm, ← Complex.exp_add]
  congr 2
  have hn := congrArg (fun x : ℤ => (x : ℂ)) (shifted_frequency_norm p u v h)
  push_cast only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast] at hn
  simp only [residueShift, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_intCast, Complex.ofReal_one, Int.cast_neg, Int.cast_pow]
  have hD : (D:ℂ) ≠ 0 := by norm_num [D]
  have hAc : (A:ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  let d : ℂ := (D : ℂ)
  let q : ℂ := (p.1.val : ℂ)
  let rr : ℂ := (r : ℂ)
  let m : ℂ := (p.2.1 : ℂ)
  let n : ℂ := (p.2.2 : ℂ)
  have hd : d ≠ 0 := hD
  have hs : (m-q/d)^2+(n-rr*(q/d))^2 = ((u:ℂ)^2+(v:ℂ)^2)/d := by
    change (d*m-q)^2+(d*n-rr*q)^2 = d*((u:ℂ)^2+(v:ℂ)^2) at hn
    rw [show m-q/d=(d*m-q)/d by field_simp [hd]; ring,
      show n-rr*(q/d)=(d*n-rr*q)/d by field_simp [hd]; ring,
      div_pow, div_pow, ← add_div, hn]
    field_simp [hd]
    ring
  change -Real.pi/(A:ℂ)*(m-q/d)^2 + -Real.pi/(A:ℂ)*(n-rr*(q/d))^2 =
    -Real.pi*(1/(d*(A:ℂ)))*((u:ℂ)^2+(-(v:ℂ))^2)
  rw [← mul_add, hs, neg_sq]
  field_simp [hd,hAc]
  exact Or.inl (mul_comm _ _)

private noncomputable def reflectedIndex : (ℤ × ℤ) ≃ (ZMod D × ℤ × ℤ) :=
  (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).trans
    (gaussianDualEquiv.trans shiftedDualEquiv.symm)

private theorem reflectedIndex_eq (p : ℤ × ℤ) :
    shiftedDualEquiv (reflectedIndex p) = gaussianDualEquiv (p.1,-p.2) := by
  cases p
  simp [reflectedIndex]

private theorem lattice_abs_summable {A : ℝ} (hA : 0 < A) :
    Summable (fun p : ℤ × ℤ => (SuperZeta.FieldWeights.conductorReading p.1 p.2 : ℂ) *
      Complex.exp (-Real.pi*(A:ℂ)*((p.1:ℂ)^2+(p.2:ℂ)^2))) := by
  refine Summable.of_norm_bounded
    (fun p : ℤ × ℤ => ‖twistedTerm A 0 p.1‖*‖twistedTerm A 0 p.2‖)
    ((twisted_summable hA 0).mul_of_nonneg (twisted_summable hA 0)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) ?_
  intro p
  have hc : ‖(SuperZeta.FieldWeights.conductorReading p.1 p.2 : ℂ)‖ ≤ 1 := by
    rw [← combined_character]
    rcases jacobiSym.trichotomy (p.1+r*p.2) D with h | h | h <;> simp only [h] <;> norm_num
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq ?_
  change 1 * _ = ‖twistedTerm A 0 p.1‖ * ‖twistedTerm A 0 p.2‖
  rw [one_mul, ← norm_mul, twistedTerm, twistedTerm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

set_option maxHeartbeats 1500000 in
/-- Scalar Fourier transformation of the signed Gaussian lattice for this
quartic. This keeps the Gauss amplitude explicit. -/
theorem gaussian_lattice_transform {A : ℝ} (hA : 0 < A) :
    gaussAmplitude * gaussianLattice A = (A:ℂ)⁻¹ * gaussianLattice (1/((D:ℝ)*A)) := by
  let f (p : ZMod D × ℤ × ℤ) := quarticCharacter p.1 *
    (shiftedTerm A (residueShift p.1) p.2.1 * shiftedTerm A ((r:ℝ)*residueShift p.1) p.2.2)
  have hq : 0 < (1/((D:ℝ)*A)) := by positivity
  have hEq (p : ℤ×ℤ) : f (reflectedIndex p) =
      (SuperZeta.FieldWeights.conductorReading p.1 p.2 : ℂ) *
        Complex.exp (-Real.pi*((1/((D:ℝ)*A):ℝ):ℂ)*((p.1:ℂ)^2+(p.2:ℂ)^2)) := by
    have h := shifted_weight hA (reflectedIndex p) p.1 (-p.2) (reflectedIndex_eq p)
    simpa only [neg_neg] using h
  have hf : Summable f :=
    reflectedIndex.summable_iff.mp ((lattice_abs_summable hq).congr (fun p => (hEq p).symm))
  have hfiber (h : ZMod D) : Summable fun p : ℤ×ℤ => f (h,p) := by
    have hh := (summable_mul_of_summable_norm (shifted_summable hA (residueShift h))
      (shifted_summable hA ((r:ℝ)*residueShift h))).mul_left (quarticCharacter h)
    exact hh
  have hsum :
      (∑ h : ZMod D, ∑' p : ℤ × ℤ, f (h,p)) = gaussianLattice (1/((D:ℝ)*A)) := by
    calc
      _ = ∑' p : ZMod D × ℤ × ℤ, f p := by rw [hf.tsum_prod' hfiber, tsum_fintype]
      _ = _ := by
        rw [← reflectedIndex.tsum_eq f]
        exact tsum_congr hEq
  calc
    _ = ∑ h : ZMod D, quarticCharacter h *
        ((∑' m : ℤ, twistedTerm A (residueShift h) m) *
          ∑' n : ℤ, twistedTerm A ((r:ℝ)*residueShift h) n) := twisted_expansion hA
    _ = (A:ℂ)⁻¹ * ∑ h : ZMod D, ∑' p : ℤ × ℤ, f (h,p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [shifted_product hA h, mul_left_comm]
      simp only [f, tsum_mul_left]
    _ = _ := by rw [hsum]

#print axioms gaussian_lattice_transform

end QuarticFiniteFourier
