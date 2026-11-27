import DedekindFiniteStripCounts
import DedekindDiscriminant23DirichletReduction

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex MeasureTheory NumberField Set
open scoped ComplexConjugate NumberField

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "L23" => Discriminant23GaloisField

/-- The class-character fold, as a nonzero entire counting function. -/
def discriminant23CharacterCountingFunction : NonzeroEntireFunction := by
  refine ⟨discriminant23CharacterFold, discriminant23CharacterFold_differentiable, ⟨0, ?_⟩⟩
  have h := (discriminant23_fold_bounds_to_seven_sixths (w := 0)
    (by norm_num) (by norm_num) (by norm_num)).2
  intro hz
  rw [hz, Complex.zero_re] at h
  norm_num at h

theorem discriminant23_entireReading_eq_base_mul_character_sq :
    mixedThetaEntireReading L23 = mixedThetaEntireReading F23 * discriminant23CharacterFold ^ 2 := by
  funext w
  simp only [mixedThetaEntireReading, Pi.mul_apply, Pi.pow_apply]
  rw [discriminant23_continued_completed_class_product, discriminant23_continued_completed_base]

/-- The local orders are those of the genuine Dedekind continuations. -/
theorem discriminant23_dedekind_orderNat_eq_base_add_character {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    analyticOrderNatAt (mixedThetaContinuation L23) w =
      analyticOrderNatAt (mixedThetaContinuation F23) w + 2 * analyticOrderNatAt discriminant23CharacterFold w := by
  rw [← mixedThetaEntireReading_orderNat_eq_continuation L23 hlo hhi,
    ← mixedThetaEntireReading_orderNat_eq_continuation F23 hlo hhi]
  exact (mixedThetaCountingFunction L23).orderNat_eq_factor_square
    (mixedThetaCountingFunction F23) discriminant23CharacterCountingFunction
    discriminant23_entireReading_eq_base_mul_character_sq w

/-- The same additive rule holds for any selection of zeros through `T`. -/
theorem discriminant23_stripZeroCount_eq_base_add_character (T : ℝ) (P : ℂ → Prop) :
    (mixedThetaCountingFunction L23).stripZeroCount T P =
      (mixedThetaCountingFunction F23).stripZeroCount T P +
        2 * discriminant23CharacterCountingFunction.stripZeroCount T P :=
  (mixedThetaCountingFunction L23).stripZeroCount_factor_square
    (mixedThetaCountingFunction F23) discriminant23CharacterCountingFunction
    discriminant23_entireReading_eq_base_mul_character_sq T P

private theorem discriminant23_baseRH_of_dirichlet_mod23
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) : DedekindZetaRH F23 :=
  dedekindZetaRH_of_cyclotomic_embedding 23 F23 discriminant23_cyclotomicEmbedding hD

theorem discriminant23_offLine_stripZeroCount_eq_twice_character
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) (T : ℝ) :
    (mixedThetaCountingFunction L23).stripZeroCount T (fun w ↦ w.re ≠ 1 / 2) =
      2 * discriminant23CharacterCountingFunction.stripZeroCount T (fun w ↦ w.re ≠ 1 / 2) := by
  have hF := (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind F23)).mp
    (discriminant23_baseRH_of_dirichlet_mod23 hD)
  have hbase : (mixedThetaCountingFunction F23).stripZeroCount T (fun w ↦ w.re ≠ 1 / 2) = 0 := by
    apply NonzeroEntireFunction.stripZeroCount_eq_zero_of_no_selection
    intro w hm hp
    obtain ⟨hlo, hhi, _, hz⟩ := ((mixedThetaCountingFunction F23).mem_stripZeros T w).mp hm
    exact hp (hF w hlo hhi ((mixedThetaEntireReading_zero_iff F23 w hlo hhi).mp hz))
  rw [discriminant23_stripZeroCount_eq_base_add_character, hbase, zero_add]

/-- The wider zero-free band gives the first complete count for the
field and the character fold. -/
theorem discriminant23_counts_zero_through_low_band (T : ℝ) (hT : T ≤ 7 / 6) (P : ℂ → Prop) :
    (mixedThetaCountingFunction L23).stripZeroCount T P = 0 ∧
      discriminant23CharacterCountingFunction.stripZeroCount T P = 0 := by
  have hL (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1) (him : |w.im| ≤ T) :
      mixedThetaContinuation L23 w ≠ 0 :=
    discriminant23_dedekind_ne_zero_to_seven_sixths hlo hhi (him.trans hT)
  constructor
  · apply NonzeroEntireFunction.stripZeroCount_eq_zero_of_no_selection
    intro w hw _
    obtain ⟨hlo, hhi, him, hz⟩ := ((mixedThetaCountingFunction L23).mem_stripZeros T w).mp hw
    exact hL w hlo hhi him ((mixedThetaEntireReading_zero_iff L23 w hlo hhi).mp hz)
  · apply NonzeroEntireFunction.stripZeroCount_eq_zero_of_no_selection
    intro w hw _
    obtain ⟨hlo, hhi, him, hz⟩ := (discriminant23CharacterCountingFunction.mem_stripZeros T w).mp hw
    exact hL w hlo hhi him ((discriminant23_dedekind_zero_iff_base_or_character w hlo hhi).mpr (.inr hz))

/-- With the Dirichlet input at 23, equality of the complete character
counts at cofinal checkpoints is equivalent to Dedekind RH for the field. -/
theorem discriminant23_dedekindRH_iff_cofinal_character_counts
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH L23 ↔ ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      discriminant23CharacterCountingFunction.stripZeroCount T (fun _ ↦ True) =
        discriminant23CharacterCountingFunction.stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  rw [← discriminant23CharacterCountingFunction.stripZerosOnLine_iff_cofinalCounts]
  exact discriminant23_dedekindRH_iff_character_of_dirichlet_mod23 hD

/-- The two halves of the fold are conjugate on the critical line. -/
theorem discriminant23_characterFold_im_eq_zero_on_line {w : ℂ} (hw : w.re = 1 / 2) :
    (discriminant23CharacterFold w).im = 0 := by
  have hExp : w - 1 = conj (-w) := by
    apply Complex.ext
    · simp only [sub_re, one_re, conj_re, neg_re]
      linarith only [hw]
    · simp
  have hWeight (x : ℝ) (hx : 1 < x) : (discriminant23FoldWeight w x).im = 0 := by
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg (by linarith only [hx])]
      exact Real.pi_ne_zero.symm
    rw [discriminant23FoldWeight, hExp, cpow_conj _ _ harg, Complex.conj_ofReal,
      add_im, conj_im, neg_add_cancel]
  have hClass (A : ClassGroup (𝓞 F23)) : ((idealClassThetaPair F23 A).Λ₀ w).im = 0 := by
    rw [discriminant23_classLambdaZero_eq_fold]
    change RCLike.im (∫ x : ℝ in Ioi 1, discriminant23FoldWeight w x * discriminant23ClassKernel A x) = 0
    rw [← integral_im (discriminant23_fold_integrable A w)]
    calc
      _ = ∫ _ : ℝ in Ioi 1, (0 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hKernel : (discriminant23ClassKernel A x).im = 0 := by
          unfold discriminant23ClassKernel
          split <;> simp only [Complex.ofReal_im]
        change (discriminant23FoldWeight w x * discriminant23ClassKernel A x).im = 0
        rw [mul_im, hKernel, hWeight x hx, mul_zero, zero_mul, add_zero]
      _ = 0 := integral_zero _ _
  rw [discriminant23CharacterFold, sub_im, hClass, hClass, sub_self]

/-- Signed real readings at two heights give a same-input zero on the line. -/
theorem discriminant23_dedekind_zero_between_character_signs {a b : ℝ} (hab : a ≤ b)
    (ha : 0 < (discriminant23CharacterFold ⟨1 / 2, a⟩).re)
    (hb : (discriminant23CharacterFold ⟨1 / 2, b⟩).re < 0) :
    ∃ t ∈ Ioo a b, discriminant23CharacterFold ⟨1 / 2, t⟩ = 0 ∧
      mixedThetaContinuation L23 ⟨1 / 2, t⟩ = 0 := by
  let z : ℝ → ℂ := fun t ↦ ⟨1 / 2, t⟩
  have hz : Continuous z :=
    equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
  let f : ℝ → ℝ := fun t ↦ (discriminant23CharacterFold (z t)).re
  have hf : Continuous f := continuous_re.comp (discriminant23CharacterFold_differentiable.continuous.comp hz)
  have hInterval : (0 : ℝ) ∈ Ioo (f b) (f a) := ⟨hb, ha⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Ioo' hab hf.continuousOn hInterval
  have hchar : discriminant23CharacterFold (z t) = 0 :=
    Complex.ext hzero (discriminant23_characterFold_im_eq_zero_on_line rfl)
  refine ⟨t, ht, hchar, ?_⟩
  exact (discriminant23_dedekind_zero_iff_base_or_character (z t)
    (by change (0 : ℝ) < 1 / 2; norm_num) (by change (1 / 2 : ℝ) < 1; norm_num)).mpr (.inr hchar)

#check @discriminant23_dedekind_orderNat_eq_base_add_character
#check @discriminant23_stripZeroCount_eq_base_add_character
#check @discriminant23_offLine_stripZeroCount_eq_twice_character
#check @discriminant23_counts_zero_through_low_band
#check @discriminant23_dedekindRH_iff_cofinal_character_counts
#check @discriminant23_dedekind_zero_between_character_signs
#print axioms discriminant23_entireReading_eq_base_mul_character_sq
#print axioms discriminant23_dedekind_orderNat_eq_base_add_character
#print axioms discriminant23_stripZeroCount_eq_base_add_character
#print axioms discriminant23_offLine_stripZeroCount_eq_twice_character
#print axioms discriminant23_counts_zero_through_low_band
#print axioms discriminant23_dedekindRH_iff_cofinal_character_counts
#print axioms discriminant23_characterFold_im_eq_zero_on_line
#print axioms discriminant23_dedekind_zero_between_character_signs

end
end FieldTarget
