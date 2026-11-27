import DedekindDiscriminant23Quadratic
import DedekindUnramifiedFrobenius
import Mathlib.NumberTheory.NumberField.Discriminant.Different

namespace FieldTarget

open Polynomial IsDedekindDomain
open scoped NumberField

local notation "L" => Discriminant23GaloisField
local notation "F" => (discriminant23QuadraticSubfield : Type)

private theorem cubic_root_isIntegral {a : L} (ha : a ^ 3 - a - 1 = 0) : IsIntegral ℤ a := by
  have hdeg : ((X : ℤ[X]) ^ 3 - X).degree = 3 := by
    rw [degree_sub_eq_left_of_degree_lt (by simp), degree_X_pow]
    norm_num
  refine ⟨X ^ 3 - X - 1, ((monic_X.pow _).sub_of_left (by simp)).sub_of_left (by simp [hdeg]), ?_⟩
  simpa [aeval_def] using ha

private theorem cubic_pair {a b : L} (ha : a ^ 3 - a - 1 = 0) (hb : b ^ 3 - b - 1 = 0)
    (hab : a ≠ b) : a ^ 2 + a * b + b ^ 2 = 1 := by
  have hd : (a - b) * (a ^ 2 + a * b + b ^ 2 - 1) = 0 := by linear_combination ha - hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr hab))

/-- Any inertia in the cyclic cubic step would identify all three roots
in the residue ring. Their sum and quadratic coefficient exclude that. -/
theorem discriminant23_relative_inertia_bot (P : Ideal (𝓞 L)) (hP : P ≠ ⊤) :
    Ideal.inertia Gal(L/F) P = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hne
  have hex : ∃ a ∈ discriminant23Cubic.rootSet L, σ a ≠ a := by
    by_contra! h
    apply hne
    apply AlgEquiv.restrictScalars_injective ℚ
    change (σ.restrictScalars ℚ : discriminant23Cubic.Gal) = 1
    exact Polynomial.Gal.ext discriminant23Cubic h
  obtain ⟨a, ha, hmove⟩ := hex
  let b : L := σ a
  let c : L := σ b
  have hcard : Nat.card Gal(L/F) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, discriminant23_relative_finrank]
  have hpow : σ ^ 3 = 1 := by
    rw [← hcard, pow_card_eq_one']
  have hcycle : σ c = a := by
    have h := DFunLike.congr_fun hpow a
    rw [pow_succ', pow_succ', pow_one, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.one_apply] at h
    exact h
  have hab : a ≠ b := Ne.symm hmove
  have hbc : b ≠ c := fun h ↦ hab (σ.injective h)
  have hac : a ≠ c := fun h ↦ hmove ((congrArg σ h).trans hcycle)
  have hfa : a ^ 3 - a - 1 = 0 := by
    simpa [discriminant23Cubic] using aeval_eq_zero_of_mem_rootSet ha
  have hfb : b ^ 3 - b - 1 = 0 := by
    simpa only [b, map_sub, map_pow, map_one, map_zero] using congrArg σ hfa
  have hfc : c ^ 3 - c - 1 = 0 := by
    simpa only [c, map_sub, map_pow, map_one, map_zero] using congrArg σ hfb
  have hqab := cubic_pair hfa hfb hab
  have hqac := cubic_pair hfa hfc hac
  have hsum : a + b + c = 0 := by
    have hprod : (b - c) * (a + b + c) = 0 := by linear_combination hqab - hqac
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hbc)
  let A : 𝓞 L := ⟨a, cubic_root_isIntegral hfa⟩
  let B : 𝓞 L := σ • A
  let C : 𝓞 L := σ • B
  have hsumI : A + B + C = 0 := by
    apply NumberField.RingOfIntegers.coe_injective
    exact hsum
  have hquadI : A ^ 2 + A * B + B ^ 2 = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    exact hqab
  let : Nontrivial ((𝓞 L) ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
  let π := Ideal.Quotient.mk P
  have hres (x : 𝓞 L) : π (σ • x) = π x := by
    exact Ideal.Quotient.eq.mpr (Ideal.mem_inertia.mp hσ x)
  have hb : π B = π A := hres A
  have hc : π C = π B := hres B
  have hsumR := congrArg π hsumI
  have hquadR := congrArg π hquadI
  simp only [map_add, map_mul, map_pow, map_zero, map_one, hc, hb] at hsumR hquadR
  exact zero_ne_one (calc
    0 = (π A + π A + π A) * π A := by rw [hsumR, zero_mul]
    _ = π A ^ 2 + π A * π A + π A ^ 2 := by ring
    _ = 1 := hquadR)

theorem discriminant23_relative_unramified (P : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
  let p := P.under (𝓞 F)
  exact (unramified_iff_inertia_bot p P ⟨rfl⟩).mpr
    (discriminant23_relative_inertia_bot P.asIdeal P.isPrime.ne_top)

theorem discriminant23_relative_different :
    differentIdeal (𝓞 F) (𝓞 L) = ⊤ := by
  let : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  by_contra h
  obtain ⟨P, hmax, hd⟩ := Ideal.exists_le_maximal _ h
  let P' : HeightOneSpectrum (𝓞 L) :=
    ⟨P, hmax.isPrime, fun hp ↦ (differentIdeal_ne_bot (A := 𝓞 F)) (le_bot_iff.mp (hp ▸ hd))⟩
  exact (not_dvd_differentIdeal_iff.mpr (discriminant23_relative_unramified P'))
    (Ideal.dvd_iff_le.mpr hd)

theorem discriminant23_discriminant_tower :
    (NumberField.discr L).natAbs = (NumberField.discr F).natAbs ^ 3 := by
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L),
    discriminant23_relative_different, discriminant23_relative_finrank]
  simp

#check @discriminant23_relative_unramified
#check @discriminant23_discriminant_tower
#print axioms discriminant23_relative_inertia_bot
#print axioms discriminant23_relative_unramified
#print axioms discriminant23_relative_different
#print axioms discriminant23_discriminant_tower

end FieldTarget
