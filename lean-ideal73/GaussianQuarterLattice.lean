import GaussianPrimePowerCoefficients
import Batteries.Tactic.OpenPrivate

/-! The quarter-lattice representatives used in the archived coefficient
are the unique representatives of nonzero Gaussian ideals. -/

namespace QuarticModel

open Module
open scoped Classical
open private gaussian_unit_coordinates from ArchivedGaussianIdealCharacter

private theorem gaussianBasis_zero : gaussianIntegralBasis 0 = (⟨1,0⟩ : GaussianInt) := by
  rw [gaussianIntegralBasis, Basis.map_apply, Basis.finTwoProd_zero]
  rfl

private theorem gaussianBasis_one : gaussianIntegralBasis 1 = (⟨0,1⟩ : GaussianInt) := by
  rw [gaussianIntegralBasis, Basis.map_apply, Basis.finTwoProd_one]
  rfl

private theorem gaussianBasis_repr (z : GaussianInt) : ⇑(gaussianIntegralBasis.repr z) = ![z.re,z.im] := by
  rw [gaussianIntegralBasis, Basis.map_repr]
  exact Basis.coe_finTwoProd_repr (z.re,z.im)

theorem gaussian_algebraNorm (z : GaussianInt) : Algebra.norm ℤ z = z.norm := by
  have hm : Algebra.leftMulMatrix gaussianIntegralBasis z = !![z.re,-z.im;z.im,z.re] := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    change (⇑(gaussianIntegralBasis.repr (z * gaussianIntegralBasis j))) i = _
    rw [gaussianBasis_repr]
    fin_cases i <;> fin_cases j <;> simp [gaussianBasis_zero, gaussianBasis_one, Zsqrtd.re_mul, Zsqrtd.im_mul]
  rw [Algebra.norm_eq_matrix_det gaussianIntegralBasis, hm, Matrix.det_fin_two_of, Zsqrtd.norm_def]
  ring

private def quarterGenerator (p : ℕ × ℕ) : GaussianInt := ⟨(p.1 : ℤ)+1,p.2⟩

def gaussianQuarterIdeal (p : ℕ × ℕ) : Ideal GaussianInt := Ideal.span {quarterGenerator p}

private theorem quarterGenerator_ne_zero (p : ℕ × ℕ) : quarterGenerator p ≠ 0 := by
  intro h
  have hr := congrArg Zsqrtd.re h
  change (p.1 : ℤ)+1 = 0 at hr
  omega

private theorem gaussianQuarterIdeal_injective : Function.Injective gaussianQuarterIdeal := by
  intro p q h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have hr := congrArg Zsqrtd.re hu
  have hi := congrArg Zsqrtd.im hu
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hr hi
  rcases gaussian_unit_coordinates (u : GaussianInt) u.isUnit with
    ⟨hur, hui⟩ | ⟨hur, hui⟩ | ⟨hur, hui⟩ | ⟨hur, hui⟩
  all_goals
    simp only [hur, hui, quarterGenerator, mul_zero, mul_one, mul_neg, add_zero, zero_add] at hr hi
  · exact Prod.ext (by omega) (by omega)
  all_goals omega

private def rotation (k : Fin 4) : GaussianInt :=
  if k.val = 0 then ⟨1,0⟩ else if k.val = 1 then ⟨0,1⟩ else if k.val = 2 then ⟨-1,0⟩ else ⟨0,-1⟩

private theorem rotation_isUnit (k : Fin 4) : IsUnit (rotation k) := by
  apply (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) _).mp
  fin_cases k <;> decide

private theorem exists_quarterGenerator (z : GaussianInt) (hz : z ≠ 0) :
    ∃ p k, quarterGenerator p * rotation k = z := by
  have hc : (0 < z.re ∧ 0 ≤ z.im) ∨ (z.re ≤ 0 ∧ 0 < z.im) ∨
      (z.re < 0 ∧ z.im ≤ 0) ∨ (0 ≤ z.re ∧ z.im < 0) := by
    have h : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hz (Zsqrtd.ext hc.1 hc.2)
    omega
  rcases hc with ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩ | ⟨hr,hi⟩
  · refine ⟨((z.re-1).toNat,z.im.toNat), (0 : Fin 4), Zsqrtd.ext ?_ ?_⟩
    all_goals (simp [quarterGenerator, rotation, Zsqrtd.re_mul, Zsqrtd.im_mul]; omega)
  · refine ⟨((z.im-1).toNat,(-z.re).toNat), (1 : Fin 4), Zsqrtd.ext ?_ ?_⟩
    all_goals (simp [quarterGenerator, rotation, Zsqrtd.re_mul, Zsqrtd.im_mul]; omega)
  · refine ⟨((-z.re-1).toNat,(-z.im).toNat), (2 : Fin 4), Zsqrtd.ext ?_ ?_⟩
    all_goals (norm_num [quarterGenerator, rotation, Zsqrtd.re_mul, Zsqrtd.im_mul]; omega)
  · refine ⟨((-z.im-1).toNat,z.re.toNat), (3 : Fin 4), Zsqrtd.ext ?_ ?_⟩
    all_goals (norm_num [quarterGenerator, rotation, Zsqrtd.re_mul, Zsqrtd.im_mul]; omega)

private theorem exists_gaussianQuarterIdeal (I : Ideal GaussianInt) (hI : I ≠ ⊥) :
    ∃ p, gaussianQuarterIdeal p = I := by
  obtain ⟨z, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  have hz : z ≠ 0 := fun hz => hI (Ideal.span_singleton_eq_bot.mpr hz)
  obtain ⟨p,k,h⟩ := exists_quarterGenerator z hz
  refine ⟨p, Ideal.span_singleton_eq_span_singleton.mpr ⟨(rotation_isUnit k).unit, ?_⟩⟩
  rw [IsUnit.unit_spec, h]

noncomputable def gaussianQuarterIdealEquiv : (ℕ × ℕ) ≃ {I : Ideal GaussianInt // I ≠ ⊥} :=
  Equiv.ofBijective (fun p => ⟨gaussianQuarterIdeal p,
    fun h => quarterGenerator_ne_zero p (Ideal.span_singleton_eq_bot.mp h)⟩) <|
    ⟨fun _ _ h => gaussianQuarterIdeal_injective (congrArg Subtype.val h),
      fun I => let ⟨p, hp⟩ := exists_gaussianQuarterIdeal I.val I.property
        ⟨p, Subtype.ext hp⟩⟩

@[simp] theorem gaussianQuarterIdealEquiv_val (p : ℕ × ℕ) :
    (gaussianQuarterIdealEquiv p).val = gaussianQuarterIdeal p := rfl

theorem gaussianQuarterIdeal_norm (p : ℕ × ℕ) :
    (gaussianQuarterIdeal p).absNorm = (p.1+1)^2 + p.2^2 := by
  rw [gaussianQuarterIdeal, Ideal.absNorm_span_singleton, gaussian_algebraNorm, GaussianInt.natAbs_norm_eq]
  have hf : ((p.1 : ℤ) + 1).natAbs = p.1+1 := by
    simpa only [Nat.cast_succ] using Int.natAbs_natCast (p.1+1)
  change ((p.1 : ℤ)+1).natAbs * ((p.1 : ℤ)+1).natAbs + (p.2 : ℤ).natAbs * (p.2 : ℤ).natAbs = _
  simp only [hf, Int.natAbs_natCast, pow_two]

theorem gaussianQuarterIdeal_signed_weight (p : ℕ × ℕ) :
    archivedIdealCharacter (gaussianQuarterIdeal p) = archivedGaussianSign ⟨(p.1 : ℤ)+1,p.2⟩ :=
  archivedIdealCharacter_span (quarterGenerator p)

#print axioms gaussianQuarterIdealEquiv
#print axioms gaussianQuarterIdeal_norm
#print axioms gaussianQuarterIdeal_signed_weight

end QuarticModel
