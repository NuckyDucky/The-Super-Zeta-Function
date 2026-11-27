import DedekindDiscriminant23ClassNumber
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldExists
import ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.SmallHilbertClassFieldPrimeSplitting

namespace FieldTarget

open scoped NumberField
open NumberField IsDedekindDomain ClassFieldTheory

noncomputable section

/-- An everywhere-unramified abelian extension of degree equal to the class
number has the small Hilbert class field's embedding property. -/
theorem isSmallHilbertClassField_of_finrank_eq_classNumber
    {K : Type} [Field K] [NumberField K] (E : FiniteAbelianExtension K)
    (hUnram : ClassFieldTheory.IsEverywhereUnramified K E)
    (hDegree : Module.finrank K E = NumberField.classNumber K) :
    IsSmallHilbertClassField E := by
  refine ⟨hUnram, ?_⟩
  obtain ⟨H, hH⟩ := ClassFieldTheory.exists_smallHilbertClassField K
  obtain ⟨f⟩ := hH.2 E hUnram
  have hRank : Module.finrank K E = Module.finrank K H :=
    hDegree.trans (GlobalClassFieldComparison.smallHilbertClassField_degree_eq_classNumber_of_isSmall K H hH).symm
  have hOnto : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hRank).mp f.injective
  let e := AlgEquiv.ofBijective f ⟨f.injective, hOnto⟩
  intro M hM
  obtain ⟨g⟩ := hH.2 M hM
  exact ⟨e.symm.toAlgHom.comp g⟩

local notation "F" => (discriminant23QuadraticSubfield : Type)
local notation "L23" => Discriminant23GaloisField

/-- The cubic extension over the quadratic subfield is unramified at every
place. At infinity all places of the base are complex. -/
theorem discriminant23_relative_everywhereUnramified :
    ClassFieldTheory.IsEverywhereUnramified F L23 := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro v P hP hOver
    exact discriminant23_relative_unramified
      ⟨P, hP, Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP, hOver⟩⟩
  · intro w
    exact InfinitePlace.isUnramified_iff.mpr
      (Or.inr (discriminant23_quadratic_totallyComplex.isComplex _))

private def discriminant23SeparableEmbedding : L23 →ₐ[F] SeparableClosure F :=
  IsSepClosed.lift

/-- The image of the actual cubic extension in the chosen separable closure
of its quadratic base. -/
def discriminant23AbelianExtension : FiniteAbelianExtension F := by
  let i := discriminant23SeparableEmbedding
  let : IsCyclic (L23 ≃ₐ[F] L23) := discriminant23_relative_galois_cyclic
  let : IsAbelianGalois F L23 := IsAbelianGalois.of_isCyclic F L23
  exact ⟨i.fieldRange, i.equivFieldRange.toLinearEquiv.finiteDimensional,
    IsAbelianGalois.of_algHom i.equivFieldRange.symm.toAlgHom⟩

/-- The embedding represents the same field over the same quadratic base. -/
def discriminant23AbelianEquiv : L23 ≃ₐ[F] discriminant23AbelianExtension :=
  discriminant23SeparableEmbedding.equivFieldRange

/-- The splitting field of the archive's cubic realizes the small Hilbert
class field of its quadratic subfield of discriminant `-23`. -/
theorem discriminant23_isSmallHilbertClassField :
    IsSmallHilbertClassField discriminant23AbelianExtension := by
  apply isSmallHilbertClassField_of_finrank_eq_classNumber
  · exact (ClassFieldTheory.isEverywhereUnramified_iff_of_algEquiv F L23
      discriminant23AbelianExtension discriminant23AbelianEquiv).mp
        discriminant23_relative_everywhereUnramified
  · rw [← discriminant23AbelianEquiv.toLinearEquiv.finrank_eq,
      discriminant23_relative_finrank, discriminant23_class_number]

/-- In the actual cubic extension, a prime of the quadratic field splits
completely exactly when its ideal class is trivial. -/
theorem discriminant23_relative_splitsCompletely_iff_class_eq_one
    (v : HeightOneSpectrum (𝓞 F)) :
    FinitePrimeSplitsCompletely F L23 v ↔
      ClassGroup.mk F (finitePrimeFractionalIdeal v) = 1 := by
  let E := discriminant23AbelianExtension
  let e := discriminant23AbelianEquiv
  let cmp := GlobalClassFieldComparison.finitePrimeSplitsCompletely_iff_original
  calc
    _ ↔ _root_.FinitePlaceSplitsCompletely (K := F) (L := L23) v := cmp F L23 v
    _ ↔ _root_.FinitePlaceSplitsCompletelyInExtension (K := F) (E := L23) v :=
      _root_.finitePlaceSplitsCompletely_iff_inExtension (K := F) (E := L23) v
    _ ↔ _root_.FinitePlaceSplitsCompletelyInExtension (K := F) (E := E) v :=
      _root_.finitePlaceSplitsCompletelyInExtension_algEquiv e v
    _ ↔ _root_.FinitePlaceSplitsCompletely (K := F) (L := E) v :=
      (_root_.finitePlaceSplitsCompletely_iff_inExtension (K := F) (E := E) v).symm
    _ ↔ FinitePrimeSplitsCompletely F E v := (cmp F E v).symm
    _ ↔ (finitePrimeFractionalIdeal v) ∈ (toPrincipalIdeal (𝓞 F) F).range :=
      finitePrime_splitsCompletelyInSmallHilbertClassField_iff_principal
        F E discriminant23_isSmallHilbertClassField v
    _ ↔ _ := by
      rw [← (ClassGroup.equiv F).injective.eq_iff]
      simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
        RingEquiv.coe_mulEquiv_refl, QuotientGroup.mk'_apply, map_one, QuotientGroup.eq_one_iff]
      have h : Units.mapEquiv (MulEquiv.refl _) (finitePrimeFractionalIdeal v) =
          finitePrimeFractionalIdeal v := Units.ext (by rfl)
      rw [h]

local notation "G23" => (L23 ≃ₐ[F] L23)

/-- In the unramified cubic step, the number of primes above a given prime
times their common residue degree is three. -/
theorem discriminant23_relative_prime_count_mul_residue_degree
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L23))
    (hOver : P.asIdeal.LiesOver v.asIdeal) :
    (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L23)).card *
      P.asIdeal.inertiaDeg (𝓞 F) = 3 := by
  let : Finite G23 := IsGaloisGroup.finite G23 F L23
  let : IsGaloisGroup G23 (𝓞 F) (𝓞 L23) :=
    IsGaloisGroup.of_isFractionRing G23 (𝓞 F) (𝓞 L23) F L23
  let : P.asIdeal.LiesOver v.asIdeal := hOver
  let : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := discriminant23_relative_unramified P
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.asIdeal (𝓞 L23) G23
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P.asIdeal G23,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.asIdeal G23,
    Ideal.ramificationIdx_eq_one P.asIdeal (𝓞 F), one_mul,
    IsGalois.card_aut_eq_finrank, discriminant23_relative_finrank] at h
  rwa [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot]

/-- The order of the base prime's ideal class is the residue degree of each
prime above it in the actual cubic extension. -/
theorem discriminant23_relative_residue_degree_eq_class_order
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L23))
    (hOver : P.asIdeal.LiesOver v.asIdeal) :
    P.asIdeal.inertiaDeg (𝓞 F) = orderOf (ClassGroup.mk F (finitePrimeFractionalIdeal v)) := by
  let : Finite G23 := IsGaloisGroup.finite G23 F L23
  let : IsGaloisGroup G23 (𝓞 F) (𝓞 L23) :=
    IsGaloisGroup.of_isFractionRing G23 (𝓞 F) (𝓞 L23) F L23
  let : P.asIdeal.LiesOver v.asIdeal := hOver
  have hSplit : P.asIdeal.inertiaDeg (𝓞 F) = 1 ↔
      ClassGroup.mk F (finitePrimeFractionalIdeal v) = 1 := by
    refine Iff.trans ?_ (discriminant23_relative_splitsCompletely_iff_class_eq_one v)
    constructor
    · intro hP Q hQ
      let : Q.asIdeal.LiesOver v.asIdeal := hQ
      let : Algebra.IsUnramifiedAt (𝓞 F) Q.asIdeal := discriminant23_relative_unramified Q
      refine ⟨Ideal.ramificationIdx_eq_one Q.asIdeal (𝓞 F), ?_⟩
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q.asIdeal G23,
        Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal P.asIdeal G23, hP]
    · exact fun h ↦ (h P hOver).2
  have hCard : Nat.card (ClassGroup (𝓞 F)) = 3 := by
    rw [Nat.card_eq_fintype_card, ← NumberField.classNumber, discriminant23_class_number]
  have hOrder := orderOf_dvd_natCard (ClassGroup.mk F (finitePrimeFractionalIdeal v))
  rw [hCard] at hOrder
  have hDegree : P.asIdeal.inertiaDeg (𝓞 F) ∣ 3 :=
    ⟨(IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L23)).card,
      by simpa only [Nat.mul_comm] using
        (discriminant23_relative_prime_count_mul_residue_degree v P hOver).symm⟩
  have h3 : Nat.Prime 3 := by decide +kernel
  rcases (Nat.dvd_prime h3).mp hDegree with hD | hD
  · exact hD.trans (orderOf_eq_one_iff.mpr (hSplit.mp hD)).symm
  · rcases (Nat.dvd_prime h3).mp hOrder with hO | hO
    · have := hSplit.mpr (orderOf_eq_one_iff.mp hO)
      omega
    · exact hD.trans hO.symm

#check @discriminant23_isSmallHilbertClassField
#check @discriminant23_relative_splitsCompletely_iff_class_eq_one
#check @discriminant23_relative_residue_degree_eq_class_order
#print axioms isSmallHilbertClassField_of_finrank_eq_classNumber
#print axioms discriminant23_relative_everywhereUnramified
#print axioms discriminant23AbelianExtension
#print axioms discriminant23_isSmallHilbertClassField
#print axioms discriminant23_relative_splitsCompletely_iff_class_eq_one
#print axioms discriminant23_relative_prime_count_mul_residue_degree
#print axioms discriminant23_relative_residue_degree_eq_class_order

end
end FieldTarget
