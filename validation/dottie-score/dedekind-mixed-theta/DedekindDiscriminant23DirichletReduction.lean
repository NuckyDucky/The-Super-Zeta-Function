import DedekindCyclotomicSubfields
import DedekindDiscriminant23DottieReading
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped NumberField ComplexConjugate

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "L23" => Discriminant23GaloisField
local notation "K23" => CyclotomicField 23 ℚ

/-- The quadratic period over the eleven nonzero squares modulo 23. -/
private def discriminant23_quadraticPeriod {R : Type*} [CommRing R] (x : R) : R :=
  x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 6 + x ^ 8 + x ^ 9 + x ^ 12 +
    x ^ 13 + x ^ 16 + x ^ 18

private theorem discriminant23_quadraticPeriod_eq_zero {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 23 = 1) (hsum : ∑ k ∈ Finset.range 23, x ^ k = 0) :
    discriminant23_quadraticPeriod x ^ 2 + discriminant23_quadraticPeriod x + 6 = 0 := by
  have hexpand :
      discriminant23_quadraticPeriod x ^ 2 + discriminant23_quadraticPeriod x + 6 =
        6 * (∑ k ∈ Finset.range 23, x ^ k) +
          (x ^ 23 - 1) * (5 * x + 4 * x ^ 2 + 3 * x ^ 3 + 2 * x ^ 4 + 2 * x ^ 5 +
            2 * x ^ 6 + 2 * x ^ 7 + 2 * x ^ 8 + x ^ 9 + 2 * x ^ 11 + x ^ 13) := by
    norm_num [Finset.sum_range_succ, discriminant23_quadraticPeriod]
    ring
  simp only [hexpand, hx, hsum, sub_self, mul_zero, zero_mul, add_zero]

/-- The quadratic period gives a square root of `-23` inside the
23rd cyclotomic field. -/
theorem discriminant23_exists_square_root_in_cyclotomic : ∃ v : K23, v ^ 2 = -23 := by
  let : IsCyclotomicExtension {23} ℚ K23 := CyclotomicField.isCyclotomicExtension 23 ℚ
  let x : K23 := IsCyclotomicExtension.zeta 23 ℚ K23
  have hx : IsPrimitiveRoot x 23 := IsCyclotomicExtension.zeta_spec 23 ℚ K23
  have hgeom : ∑ k ∈ Finset.range 23, x ^ k = 0 := hx.geom_sum_eq_zero (by norm_num)
  let η := discriminant23_quadraticPeriod x
  have hη : η ^ 2 + η + 6 = 0 :=
    discriminant23_quadraticPeriod_eq_zero x hx.pow_eq_one hgeom
  refine ⟨1 + 2 * η, ?_⟩
  linear_combination 4 * hη

/-- The quadratic base embeds at the single rational modulus 23. -/
def discriminant23_cyclotomicEmbedding : F23 →ₐ[ℚ] K23 := by
  let v := Classical.choose discriminant23_exists_square_root_in_cyclotomic
  have hv := Classical.choose_spec discriminant23_exists_square_root_in_cyclotomic
  let e : Discriminant23QuadraticField →ₐ[ℚ] K23 :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ K23) v (by simp [v, discriminant23Quadratic, hv])
  exact e.comp discriminant23QuadraticEquiv.symm.toAlgHom

theorem discriminant23_dedekindRH_iff_character_of_dirichlet_mod23
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH L23 ↔ StripZerosOnLine discriminant23CharacterFold := by
  exact discriminant23_dedekindRH_iff_character
    (dedekindZetaRH_of_cyclotomic_embedding 23 F23 discriminant23_cyclotomicEmbedding hD)

/-- Once the rational Dirichlet input at modulus 23 is supplied, only the
character fold on the higher right half of the strip is needed. -/
theorem discriminant23_dedekindRH_iff_character_on_higher_right_strip
    (hD : ∀ χ : DirichletCharacter ℂ 23, StripZerosOnLine χ.LFunction) :
    DedekindZetaRH L23 ↔ ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → 7 / 6 < |w.im| →
      discriminant23CharacterFold w ≠ 0 := by
  constructor
  · intro hL w hre hhi _ hzero
    have h0 : 0 < w.re := by linarith only [hre]
    have hC := (discriminant23_dedekindRH_iff_character_of_dirichlet_mod23 hD).mp hL
    exact hre.ne' (hC w h0 hhi hzero)
  · intro h
    have hF := (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind F23)).mp
      (dedekindZetaRH_of_cyclotomic_embedding 23 F23 discriminant23_cyclotomicEmbedding hD)
    have hright (w : ℂ) (hre : 1 / 2 < w.re) (hhi : w.re < 1) :
        mixedThetaContinuation L23 w ≠ 0 := by
      have h0 : 0 < w.re := by linarith only [hre]
      by_cases him : |w.im| ≤ 7 / 6
      · exact discriminant23_dedekind_ne_zero_to_seven_sixths h0 hhi him
      · intro hz
        rcases (discriminant23_dedekind_zero_iff_base_or_character w h0 hhi).mp hz with hb | hc
        · exact hre.ne' (hF w h0 hhi hb)
        · exact h w hre hhi (lt_of_not_ge him) hc
    apply (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind L23)).mpr
    intro w hlo hhi hz
    rcases lt_trichotomy w.re (1 / 2 : ℝ) with hleft | heq | hgt
    · exfalso
      apply hright (1 - conj w) _ _ (mixedThetaContinuation_reflects L23 w hlo hhi hz)
      · simp only [sub_re, one_re, conj_re]
        linarith only [hleft]
      · simp only [sub_re, one_re, conj_re]
        linarith only [hlo]
    · exact heq
    · exact (hright w hgt hhi hz).elim

#check @discriminant23_dedekindRH_iff_character_of_dirichlet_mod23
#check @discriminant23_dedekindRH_iff_character_on_higher_right_strip
#print axioms discriminant23_exists_square_root_in_cyclotomic
#print axioms discriminant23_cyclotomicEmbedding
#print axioms discriminant23_dedekindRH_iff_character_of_dirichlet_mod23
#print axioms discriminant23_dedekindRH_iff_character_on_higher_right_strip

end
end FieldTarget
