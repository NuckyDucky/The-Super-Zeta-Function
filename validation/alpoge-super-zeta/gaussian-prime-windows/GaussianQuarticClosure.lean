import QuarticAt73
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Galois.Basic

/-! A concrete splitting field of the archived quartic. The degree-one
place at 73 detects that its rational discriminant parameter is still
a nonsquare in the quartic itself. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open NumberField Polynomial

noncomputable section

private def normParameter : ℕ := 26509772707289

/-- The actual quartic has a degree-one residue map at the marked prime 73. -/
theorem exists_residueMap73 : Nonempty (𝓞 QuarticModel.K →+* ZMod 73) := by
  classical
  have hPositive : 0 < Nat.card {P : Ideal (𝓞 QuarticModel.K) // P.absNorm = 73} := by
    rw [QuarticAt73.ideal_count]
    decide
  obtain ⟨P⟩ := (Nat.card_pos_iff.mp hPositive).1
  have hCard : Nat.card (𝓞 QuarticModel.K ⧸ P.val) = 73 := P.property
  have hCardPos : 0 < Nat.card (𝓞 QuarticModel.K ⧸ P.val) := by rw [hCard]; decide
  let : Finite (𝓞 QuarticModel.K ⧸ P.val) := (Nat.card_pos_iff.mp hCardPos).2
  let : Fintype (𝓞 QuarticModel.K ⧸ P.val) := Fintype.ofFinite _
  have hF : Fintype.card (𝓞 QuarticModel.K ⧸ P.val) = 73 := by
    rw [← Nat.card_eq_fintype_card, hCard]
  let e := ZMod.ringEquivOfPrime (𝓞 QuarticModel.K ⧸ P.val) (by decide : Nat.Prime 73) hF
  exact ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk P.val)⟩

/-- Reducing an integral square root at 73 excludes it from the actual quartic. -/
theorem normParameter_not_square (w : QuarticModel.K) :
    w ^ 2 ≠ (26509772707289 : QuarticModel.K) := by
  intro hw
  have hwIntegral : IsIntegral ℤ w := by
    refine ⟨X ^ 2 - C (26509772707289 : ℤ), monic_X_pow_sub_C _ (by decide), ?_⟩
    change aeval w (X ^ 2 - C (26509772707289 : ℤ)) = 0
    simp [hw, map_ofNat]
  let w_int : 𝓞 QuarticModel.K := ⟨w, hwIntegral⟩
  have hi : w_int ^ 2 = (26509772707289 : 𝓞 QuarticModel.K) := by
    apply Subtype.ext
    exact hw
  obtain ⟨φ⟩ := exists_residueMap73
  have he := congrArg φ hi
  simp only [map_pow, map_ofNat] at he
  have hNo : ∀ r : ZMod 73, r ^ 2 ≠ 26509772707289 := by decide +kernel
  exact hNo _ he

/-- The quadratic adjoining the product of the two marked roots. -/
def quadratic : QuarticModel.K[X] :=
  X ^ 2 - C (normParameter : QuarticModel.K)

theorem quadratic_irreducible : Irreducible quadratic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadratic, Polynomial.natDegree_X_pow_sub_C]
    decide
  · intro a ha
    apply normParameter_not_square a
    have h : a ^ 2 - (normParameter : QuarticModel.K) = 0 := by
      simpa only [IsRoot, quadratic, eval_sub, eval_pow, eval_X, eval_C] using ha
    simpa only [normParameter, Nat.cast_ofNat] using sub_eq_zero.mp h

instance quadratic_fact : Fact (Irreducible quadratic) := ⟨quadratic_irreducible⟩

/-- The quartic with one square root of its norm parameter adjoined. -/
abbrev L := AdjoinRoot quadratic

instance : Module.Finite QuarticModel.K L :=
  (monic_X_pow_sub_C _ (by decide : (2 : ℕ) ≠ 0)).finite_adjoinRoot

instance : NumberField L := NumberField.of_module_finite QuarticModel.K L

theorem degree_two : Module.finrank QuarticModel.K L = 2 := by
  change Module.finrank QuarticModel.K (QuarticModel.K[X] ⧸ Ideal.span {quadratic}) = 2
  rw [finrank_quotient_span_eq_natDegree, quadratic, Polynomial.natDegree_X_pow_sub_C]

theorem degree_eight : Module.finrank ℚ L = 8 := by
  rw [← Module.finrank_mul_finrank ℚ QuarticModel.K L, QuarticModel.degree_four, degree_two]

def alpha : L := algebraMap QuarticModel.K L (QuarticModel.theta : QuarticModel.K)

def gamma : L := AdjoinRoot.root quadratic

def iLift : L := algebraMap QuarticModel.K L QuarticModel.gaussianI

theorem gamma_sq : gamma ^ 2 = (26509772707289 : L) := by
  have h : aeval gamma quadratic = 0 := by rw [gamma, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h' : gamma ^ 2 - (normParameter : L) = 0 := by
    simpa only [quadratic, map_sub, map_pow, aeval_X, aeval_C, map_natCast] using h
  simpa only [normParameter, Nat.cast_ofNat] using sub_eq_zero.mp h'

theorem alpha_sq : alpha ^ 2 = -5045155 + 1027708 * iLift := by
  have h := congrArg (algebraMap QuarticModel.K L) QuarticModel.theta_sq
  simpa only [alpha, iLift, map_pow, map_add, map_mul, map_neg, map_ofNat] using h

theorem iLift_sq : iLift ^ 2 = -1 := by
  have h := congrArg (algebraMap QuarticModel.K L) QuarticModel.gaussianI_sq
  simpa only [iLift, map_pow, map_neg, map_one] using h

private theorem delta_product : alpha ^ 2 * ((-5045155 : L) - 1027708 * iLift) = 26509772707289 := by
  rw [alpha_sq]
  linear_combination -(1027708 : L) ^ 2 * iLift_sq

theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  simpa [h] using delta_product

theorem gamma_ne_zero : gamma ≠ 0 := by
  intro h
  simpa [h] using gamma_sq

def beta : L := gamma / alpha

theorem beta_sq : beta ^ 2 = -5045155 - 1027708 * iLift := by
  rw [beta, div_pow, gamma_sq, div_eq_iff (pow_ne_zero _ alpha_ne_zero)]
  exact delta_product.symm.trans (mul_comm _ _)

theorem alpha_mul_beta : alpha * beta = gamma := by
  rw [beta, mul_comm, div_mul_cancel₀ _ alpha_ne_zero]

theorem beta_ne_zero : beta ≠ 0 := div_ne_zero gamma_ne_zero alpha_ne_zero

theorem alpha_sq_ne_beta_sq : alpha ^ 2 ≠ beta ^ 2 := by
  intro he
  have hi : iLift ≠ 0 := by intro hz; simpa [hz] using iLift_sq
  rw [alpha_sq, beta_sq] at he
  have h : (2055416 : L) * iLift = 0 := by linear_combination he
  exact mul_ne_zero (by norm_num) hi h

private theorem pair_factor (a : L) :
    (X - C a) * (X - C (-a)) = X ^ 2 - C (a ^ 2) := by
  simp only [map_neg, map_pow]
  ring

theorem mapped_quartic_factor :
    QuarticModel.rationalPolynomial.map (algebraMap ℚ L) =
      ((X - C alpha) * (X - C (-alpha))) *
      ((X - C beta) * (X - C (-beta))) := by
  have hSum : alpha ^ 2 + beta ^ 2 = -(10090310 : L) := by rw [alpha_sq, beta_sq]; ring
  have hMul : alpha ^ 2 * beta ^ 2 = (26509772707289 : L) := by rw [beta_sq]; exact delta_product
  rw [pair_factor, pair_factor]
  calc
    _ = X ^ 4 + 10090310 * X ^ 2 + 26509772707289 := by
      simp only [QuarticModel.rationalPolynomial, QuarticCoefficient.sqrtDeltaPolynomial,
        Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat]
    _ = X ^ 4 - C (alpha ^ 2 + beta ^ 2) * X ^ 2 + C (alpha ^ 2 * beta ^ 2) := by
      rw [hSum, hMul, map_neg, Polynomial.C_ofNat, Polynomial.C_ofNat]
      ring
    _ = _ := by rw [map_add, map_mul]; ring

/-- The four marked roots exhaust the roots of the original rational polynomial. -/
theorem mem_iff_marked_root (z : L) :
    z ∈ QuarticModel.rationalPolynomial.rootSet L ↔
      z = alpha ∨ z = -alpha ∨ z = beta ∨ z = -beta := by
  rw [(QuarticModel.monic_g.map (algebraMap ℤ ℚ)).mem_rootSet, ← Polynomial.eval_map_algebraMap,
    mapped_quartic_factor]
  simp only [eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero]
  tauto

theorem adjoin_marked_roots :
    Algebra.adjoin ℚ ({alpha, beta} : Set L) = ⊤ := by
  let S := Algebra.adjoin ℚ ({alpha, beta} : Set L)
  have hα : alpha ∈ S := Algebra.subset_adjoin (by simp)
  have hβ : beta ∈ S := Algebra.subset_adjoin (by simp)
  have hγ : gamma ∈ S := alpha_mul_beta ▸ S.mul_mem hα hβ
  have hImage : (algebraMap QuarticModel.K L) '' ({(QuarticModel.theta : QuarticModel.K)} : Set QuarticModel.K)
      ⊆ ({alpha, beta} : Set L) := by
    rw [Set.image_singleton]
    exact Set.singleton_subset_iff.mpr (by simp [alpha])
  have hM : (Algebra.adjoin ℚ ({(QuarticModel.theta : QuarticModel.K)} : Set QuarticModel.K)).map
      (IsScalarTower.toAlgHom ℚ QuarticModel.K L) ≤ S := by
    rw [← Algebra.adjoin_algebraMap]
    exact Algebra.adjoin_mono hImage
  have hK (u : QuarticModel.K) : algebraMap QuarticModel.K L u ∈ S := by
    apply hM
    exact Subalgebra.mem_map.mpr ⟨u, by rw [QuarticModel.theta_generates]; simp, rfl⟩
  change S = ⊤
  apply eq_top_iff.mpr
  intro z _
  have hz : z ∈ Algebra.adjoin QuarticModel.K ({gamma} : Set L) := by
    rw [gamma, AdjoinRoot.adjoinRoot_eq_top]
    simp
  exact Algebra.adjoin_induction (p := fun u _ => u ∈ S)
    (fun u hu => by simpa only [Set.mem_singleton_iff.mp hu] using hγ)
    hK (fun _ _ _ _ hx hy => S.add_mem hx hy) (fun _ _ _ _ hx hy => S.mul_mem hx hy) hz

/-- The concrete quadratic tower is a splitting field of the original quartic. -/
instance isSplittingField : QuarticModel.rationalPolynomial.IsSplittingField ℚ L := by
  constructor
  · rw [mapped_quartic_factor]
    exact ((Splits.X_sub_C _).mul (Splits.X_sub_C _)).mul
      ((Splits.X_sub_C _).mul (Splits.X_sub_C _))
  · apply eq_top_iff.mpr
    rw [← adjoin_marked_roots]
    apply Algebra.adjoin_mono
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz : z = alpha ∨ z = beta)
      with h | h
    · exact (mem_iff_marked_root z).mpr (Or.inl h)
    · exact (mem_iff_marked_root z).mpr (Or.inr (Or.inr (Or.inl h)))

instance isGalois : IsGalois ℚ L :=
  IsGalois.of_separable_splitting_field
    ((Fact.out : Irreducible QuarticModel.rationalPolynomial).separable)

#print axioms exists_residueMap73
#print axioms normParameter_not_square
#print axioms quadratic_irreducible
#print axioms degree_eight
#print axioms mapped_quartic_factor
#print axioms adjoin_marked_roots
#print axioms isSplittingField
#print axioms isGalois

end
end GaussianQuarticClosure
end AlpogeSuperZeta
