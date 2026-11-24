import ArchivedQuarticLatticeCoefficients
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

/-! Absolute convergence and grouping by the original Gaussian norm.
The estimates reuse the quarter-lattice majorant from RingStageTwo. -/

namespace QuarticModel

open ArithmeticFunction FieldCoefficientTransfer
open scoped Classical

def archivedQuarterNorm (p : ℕ × ℕ) : ℕ := (p.1+1)^2+p.2^2

noncomputable def archivedQuarterWeight (p : ℕ × ℕ) : ℂ :=
  (archivedGaussianSign ⟨(p.1 : ℤ)+1,p.2⟩ : ℂ)

theorem archivedQuarterNorm_pos (p : ℕ × ℕ) : 0 < archivedQuarterNorm p := by
  unfold archivedQuarterNorm
  positivity

private theorem jacobi_abs_le_one (a : ℤ) (d : ℕ) : |jacobiSym a d| ≤ 1 := by
  rcases jacobiSym.trichotomy a d with h | h | h <;> rw [h] <;> norm_num

theorem archivedQuarterWeight_norm_le (p : ℕ × ℕ) : ‖archivedQuarterWeight p‖ ≤ 1 := by
  unfold archivedQuarterWeight
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have h : |archivedGaussianSign ⟨(p.1 : ℤ)+1,p.2⟩| ≤ 1 := by
    unfold archivedGaussianSign
    simp_rw [abs_mul]
    refine (mul_le_mul (mul_le_mul (jacobi_abs_le_one _ _) (jacobi_abs_le_one _ _) (abs_nonneg _) (by decide))
      (jacobi_abs_le_one _ _) (abs_nonneg _) (by decide)).trans ?_
    decide
  exact_mod_cast h

private noncomputable def quarterNormFiberEquiv (n : ℕ) (hn : n ≠ 0) :
    {p : ℕ × ℕ // archivedQuarterNorm p = n} ≃ GaussianNormFiber n := by
  let f (p : {p : ℕ × ℕ // archivedQuarterNorm p = n}) : GaussianNormFiber n :=
    ⟨gaussianQuarterIdeal p.val, (gaussianQuarterIdeal_norm p.val).trans p.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro p q h
    have he : gaussianQuarterIdeal p.val = gaussianQuarterIdeal q.val :=
      congrArg (fun I : GaussianNormFiber n => I.val) h
    exact Subtype.ext (gaussianQuarterIdealEquiv.injective (Subtype.ext he))
  · intro I
    have hne : I.val ≠ ⊥ := by
      intro h
      exact hn (I.property.symm.trans (h ▸ Ideal.absNorm_bot))
    obtain ⟨p,hp⟩ := gaussianQuarterIdealEquiv.surjective ⟨I.val,hne⟩
    have he : gaussianQuarterIdeal p = I.val := congrArg Subtype.val hp
    have hnorm : archivedQuarterNorm p = n :=
      (gaussianQuarterIdeal_norm p).symm.trans ((congrArg Ideal.absNorm he).trans I.property)
    exact ⟨⟨p,hnorm⟩,Subtype.ext he⟩

/-- Group any summable weighted function of the norm by the exact signed
coefficient from the archived square-root rows. -/
theorem hasSum_group_by_archivedNorm {F : ℕ → ℂ} {S : ℂ}
    (h : HasSum (fun p => archivedQuarterWeight p * F (archivedQuarterNorm p)) S) :
    HasSum (fun n => signedIdealCoefficients n * F n) S := by
  refine (h.tsum_fiberwise archivedQuarterNorm).congr_fun ?_
  intro n
  symm
  change (∑' p : {p : ℕ × ℕ // archivedQuarterNorm p = n},
    archivedQuarterWeight p.val * F (archivedQuarterNorm p.val)) = _
  by_cases hn : n = 0
  · let : IsEmpty {p : ℕ × ℕ // archivedQuarterNorm p = n} :=
      ⟨fun p => (archivedQuarterNorm_pos p.val).ne' (p.property.trans hn)⟩
    simp [hn]
  · have hr (p : {p : ℕ × ℕ // archivedQuarterNorm p = n}) :
        archivedQuarterWeight p.val = (archivedIdealCharacter ((quarterNormFiberEquiv n hn p).val) : ℂ) :=
      congrArg (Int.cast : ℤ → ℂ) (gaussianQuarterIdeal_signed_weight p.val).symm
    simp_rw [fun p : {p : ℕ × ℕ // archivedQuarterNorm p = n} => p.property, hr]
    rw [tsum_mul_right, (quarterNormFiberEquiv n hn).tsum_eq
      (fun I : GaussianNormFiber n => (archivedIdealCharacter I.val : ℂ))]
    simp [signedIdealCoefficients, toArithmeticFunction, signedIdealNormSum, hn]

private theorem summable_nonnegative_product {f : ℕ → ℝ} (hn : ∀ n, 0 ≤ f n)
    (hf : Summable f) : Summable (fun p : ℕ × ℕ => f p.1 * f p.2) := by
  apply (summable_prod_of_nonneg (fun p => mul_nonneg (hn p.1) (hn p.2))).mpr
  refine ⟨fun i => hf.mul_left (f i), ?_⟩
  simpa only [tsum_mul_left] using hf.mul_right (∑' n : ℕ, f n)

theorem archivedQuarter_dirichlet_abs_summable {σ scale : ℝ} (hσ : 1 < σ) (hs : 0 < scale) :
    Summable (fun p => ‖archivedQuarterWeight p‖ / ((archivedQuarterNorm p : ℝ) / scale) ^ σ) := by
  let f (n : ℕ) := ((n : ℝ) + 1) ^ (-σ)
  have hf : Summable f := by
    have h : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    simpa only [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have hprod := summable_nonnegative_product (f := f) (fun _ => by positivity) hf
  have hnorm (p : ℕ × ℕ) : 0 ≤ (archivedQuarterNorm p : ℝ) / scale := by positivity
  refine Summable.of_nonneg_of_le (fun p => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (hnorm p) _)) ?_
    (hprod.mul_left ((2*scale)^σ))
  intro p
  let a : ℝ := (p.1 : ℝ)+1
  let b : ℝ := p.2
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) p.1]
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hN : a*(b+1) ≤ 2*(archivedQuarterNorm p : ℝ) := by
    push_cast [archivedQuarterNorm]
    change a*(b+1) ≤ 2*(a^2+b^2)
    nlinarith [sq_nonneg (a-b), mul_nonneg ha0.le (sub_nonneg.mpr ha)]
  have hbase : 0 < a*(b+1)/(2*scale) := by positivity
  have hle : a*(b+1)/(2*scale) ≤ (archivedQuarterNorm p : ℝ)/scale := by
    have he : a*(b+1)/(2*scale) = (a*(b+1)/2)/scale := by ring
    rw [he]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ (by norm_num : 0 < (2 : ℝ))).2
      (by simpa only [mul_comm] using hN)) hs.le
  calc
    _ ≤ 1 / ((archivedQuarterNorm p : ℝ)/scale)^σ :=
      div_le_div_of_nonneg_right (archivedQuarterWeight_norm_le p) (Real.rpow_nonneg (hnorm p) _)
    _ ≤ (a*(b+1)/(2*scale))^(-σ) := by
      rw [one_div, ← Real.rpow_neg (hnorm p)]
      exact Real.rpow_le_rpow_of_nonpos hbase hle (by linarith)
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_neg (by positivity : 0 ≤ 2*scale), div_inv_eq_mul]
      change a^(-σ)*(b+1)^(-σ)*(2*scale)^σ = (2*scale)^σ*(a^(-σ)*(b+1)^(-σ))
      ring

noncomputable def archivedGaussianDirichlet (w : ℂ) : ℂ :=
  ∑' p, archivedQuarterWeight p / (archivedQuarterNorm p : ℂ)^w

theorem archivedGaussianDirichlet_hasSum_lattice {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun p => archivedQuarterWeight p / (archivedQuarterNorm p : ℂ)^w) (archivedGaussianDirichlet w) := by
  apply Summable.hasSum
  apply Summable.of_norm
  have h := archivedQuarter_dirichlet_abs_summable (scale := 1) hw zero_lt_one
  convert h using 1
  funext p
  rw [norm_div, div_one, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (archivedQuarterNorm_pos p))]

theorem archivedGaussianDirichlet_hasSum {w : ℂ} (hw : 1 < w.re) :
    LSeriesHasSum signedIdealCoefficients w (archivedGaussianDirichlet w) := by
  have h := hasSum_group_by_archivedNorm (F := fun n => ((n : ℂ)^w)⁻¹)
    (by simpa only [div_eq_mul_inv] using archivedGaussianDirichlet_hasSum_lattice hw)
  unfold LSeriesHasSum
  refine h.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv]

theorem dedekindZeta_eq_archivedGaussianDirichlet {w : ℂ} (hw : 1 < w.re) :
    NumberField.dedekindZeta K w = riemannZeta w * chi4.LFunction w * archivedGaussianDirichlet w := by
  rw [← idealCounts_series K w, idealCounts_eq_archived_convolution]
  exact (LSeriesHasSum_mul (LSeriesHasSum_mul (zetaCoeff_sum hw) (betaCoeff_sum hw))
    (archivedGaussianDirichlet_hasSum hw)).LSeries_eq

#print axioms hasSum_group_by_archivedNorm
#print axioms archivedGaussianDirichlet_hasSum
#print axioms dedekindZeta_eq_archivedGaussianDirichlet

end QuarticModel
