import QuarticDualArithmetic
import GaussianInertPrimeWeights
import GaussianNormOrientation

/-! The residue already used in the quartic Fourier proof is the
conductor residue of the same Gaussian prime ideal. -/

namespace QuarticModel

open QuarticDualArithmetic

private theorem conductor_root_sq : (r : ZMod modulus) * (r : ZMod modulus) = -1 := by
  decide +kernel

/-- Evaluate a Gaussian integer at the original conductor root of minus one. -/
def gaussianConductorResidue : GaussianInt →+* ZMod modulus :=
  Zsqrtd.lift ⟨(r : ZMod modulus), conductor_root_sq⟩

theorem gaussianConductorResidue_apply (z : GaussianInt) :
    gaussianConductorResidue z = (z.re : ZMod modulus) + (z.im : ZMod modulus) * r := rfl

private theorem gaussianConductorResidue_discriminant :
    gaussianConductorResidue gaussianDiscriminant = 0 := by
  rw [gaussianConductorResidue_apply]
  decide +kernel

theorem gaussianConductorResidue_ker :
    RingHom.ker gaussianConductorResidue = Ideal.span {gaussianDiscriminant} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hz
    have hcast : ((z.im - r * z.re : ℤ) : ZMod modulus) =
        -(r : ZMod modulus) * gaussianConductorResidue z := by
      rw [gaussianConductorResidue_apply, Int.cast_sub, Int.cast_mul]
      linear_combination (z.im : ZMod modulus) * conductor_root_sq
    rw [hz, mul_zero] at hcast
    obtain ⟨u, v, hre, him⟩ := (dual_lattice z.re z.im).mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast)
    refine ⟨⟨u, v⟩, Zsqrtd.ext ?_ ?_⟩
    · change z.re = a * u + -1 * b * v
      linarith only [hre]
    · change z.im = a * v + b * u
      linarith only [him]
  · rintro ⟨w, rfl⟩
    rw [map_mul, gaussianConductorResidue_discriminant, zero_mul]

/-- The residue ring of the original Gaussian discriminant ideal. -/
noncomputable def gaussianConductorQuotientEquiv :
    (GaussianInt ⧸ Ideal.span {gaussianDiscriminant}) ≃+* ZMod modulus :=
  (Ideal.quotEquivOfEq gaussianConductorResidue_ker.symm).trans
    (gaussianConductorResidue.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective gaussianConductorResidue))

theorem gaussianConductorQuotientEquiv_mk (z : GaussianInt) :
    gaussianConductorQuotientEquiv (Ideal.Quotient.mk _ z) = gaussianConductorResidue z := rfl

theorem gaussianConductorResidue_mul_star (z : GaussianInt) :
    gaussianConductorResidue z * gaussianConductorResidue (star z) = (z.norm : ZMod modulus) := by
  rw [← map_mul, ← Zsqrtd.norm_eq_mul_conj, map_intCast]

noncomputable def gaussianConductorJacobi (u : ZMod modulus) : ℤ :=
  jacobiSym (u.val : ℤ) modulus

theorem archivedGaussianSign_eq_conductorResidue (z : GaussianInt) :
    archivedGaussianSign z = gaussianConductorJacobi (gaussianConductorResidue z) := by
  rw [gaussianConductorJacobi, gaussianConductorResidue_apply,
    mul_comm (z.im : ZMod modulus), ← Int.cast_mul, ← Int.cast_add,
    ZMod.val_intCast, ← jacobiSym.mod_left]
  exact (combined_character z.re z.im).symm

theorem archivedIdealCharacter_span_eq_conductorResidue (z : GaussianInt) :
    archivedIdealCharacter (Ideal.span {z}) =
      gaussianConductorJacobi (gaussianConductorResidue z) :=
  (archivedIdealCharacter_span z).trans (archivedGaussianSign_eq_conductorResidue z)

theorem archivedIdealCharacter_eq_conductorResidue (I : Ideal GaussianInt) :
    archivedIdealCharacter I =
      gaussianConductorJacobi (gaussianConductorResidue (Submodule.IsPrincipal.generator I)) := by
  rw [← archivedIdealCharacter_span_eq_conductorResidue, Ideal.span_singleton_generator]

theorem conductor_residues_at_norm_73 :
    gaussianConductorResidue ⟨3, 8⟩ = 15076377565152 ∧
    gaussianConductorResidue ⟨3, -8⟩ = 11433395142143 ∧
    gaussianConductorJacobi 15076377565152 = -1 ∧
    gaussianConductorJacobi 11433395142143 = 1 := by
  have hl : gaussianConductorResidue ⟨3, 8⟩ = 15076377565152 := by
    rw [gaussianConductorResidue_apply]
    decide +kernel
  have hr : gaussianConductorResidue ⟨3, -8⟩ = 11433395142143 := by
    rw [gaussianConductorResidue_apply]
    decide +kernel
  obtain ⟨hs₁, hs₂⟩ := archivedGaussianSigns_at_norm_73
  rw [archivedGaussianSign_eq_conductorResidue, hl] at hs₁
  rw [archivedGaussianSign_eq_conductorResidue, hr] at hs₂
  exact ⟨hl, hr, hs₁, hs₂⟩

#print axioms gaussianConductorResidue_ker
#print axioms gaussianConductorQuotientEquiv_mk
#print axioms gaussianConductorResidue_mul_star
#print axioms archivedIdealCharacter_eq_conductorResidue
#print axioms conductor_residues_at_norm_73

end QuarticModel

namespace AlpogeSuperZeta

open QuarticModel
open scoped Classical

/-- The weight used by the inert-prime criterion, with the sign evaluated
at each individual Gaussian prime's conductor residue. -/
theorem twice_inert_weight_eq_conductor_sum {p : ℕ} (hp : p.Prime) :
    2 * archivedInertDegreeOneWeight p =
      ∑ I ∈ gaussianPrimesAbove p,
        if I.inertiaDeg ℤ = 1 ∧ archivedIdealCharacter I ≠ 0 then
          (1 : ℝ) - (gaussianConductorJacobi
            (gaussianConductorResidue (Submodule.IsPrincipal.generator I)) : ℝ)
        else 0 := by
  have ha := archivedGaussianPrimeWeight_eq_unramified_sub_twice_inert hp
  have hpw := archivedGaussianPrimeWeight_prime_power hp Nat.one_ne_zero
  rw [pow_one] at hpw
  rw [show 2 * archivedInertDegreeOneWeight p =
      archivedUnramifiedDegreeOneWeight p - archivedGaussianPrimeWeight p by linarith only [ha],
    hpw, archivedUnramifiedDegreeOneWeight, archivedGaussianPrimePowerWeight,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← archivedIdealCharacter_eq_conductorResidue]
  by_cases hf : I.inertiaDeg ℤ = 1
  · by_cases hz : archivedIdealCharacter I = 0
    · simp [hf, hz]
    · simp [hf, hz]
  · have hd : ¬ I.inertiaDeg ℤ ∣ 1 := fun h => hf (Nat.dvd_one.mp h)
    simp [hf, hd]

/-- Euler's criterion forces a prime factor on the negative Gaussian
branch. The exponent uses the norm of the degree-one prime. -/
theorem half_power_add_one_mem_gaussian_prime_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    gaussianDiscriminant ^ (p / 2) + 1 ∈ gaussianPrimeAt r hr ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = -1 := by
  let v : ZMod p := (-5045155 : ZMod p) + 1027708 * r
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hpow := quadraticChar_eq_pow_of_char_ne_two' hchar v
  rw [ZMod.card] at hpow
  rw [archivedIdealCharacter_at_root hp r hr hI, gaussianPrimeAt, RingHom.mem_ker,
    map_add, map_pow, map_one, gaussianResidue_discriminant, add_eq_zero_iff_eq_neg]
  change v ^ (p / 2) = -1 ↔ quadraticChar (ZMod p) v = -1
  rw [← hpow]
  by_cases hv : v = 0
  · simp [hv]
  rcases quadraticChar_dichotomy hv with hpos | hneg
  · have hneq := (Ring.neg_one_ne_one_of_char_ne_two hchar).symm
    simp [hpos, hneq]
  · simp [hneg]

local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

set_option maxRecDepth 20000 in
theorem forced_gaussian_factor_at_73 :
    let c : GaussianInt := gaussianDiscriminant ^ 36 + 1
    (⟨3, 8⟩ : GaussianInt) ∣ c ∧ ¬ (⟨3, -8⟩ : GaussianInt) ∣ c ∧
      c.norm.natAbs % 73 ^ 2 = 2409 := by
  let r : ZMod 73 := 27
  have hplus : r ^ 2 = -1 := by decide +kernel
  have hminus : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hplus
  have h₂ : 73 ≠ 2 := by decide
  have hs := split_gaussian_primes h₂ r hplus hminus
  have hIplus : gaussianPrimeAt r hplus ∈ gaussianPrimesAbove 73 := by simp [hs]
  have hIminus : gaussianPrimeAt (-r) hminus ∈ gaussianPrimesAbove 73 := by simp [hs]
  have hzplus : gaussianResidue r hplus ⟨3, 8⟩ = 0 := by
    change (3 : ZMod 73) + 8 * 27 = 0
    decide +kernel
  have hzminus : gaussianResidue (-r) hminus ⟨3, -8⟩ = 0 := by
    change (3 : ZMod 73) + (-8 : ZMod 73) * (-27 : ZMod 73) = 0
    decide +kernel
  have hA := gaussianPrimeAt_eq_span r hplus ⟨3, 8⟩ (by decide +kernel) hzplus
  have hB := gaussianPrimeAt_eq_span (-r) hminus ⟨3, -8⟩ (by decide +kernel) hzminus
  have hleft := half_power_add_one_mem_gaussian_prime_iff h₂ r hplus hIplus
  have hright := half_power_add_one_mem_gaussian_prime_iff h₂ (-r) hminus hIminus
  rw [hA, Ideal.mem_span_singleton, archivedIdealCharacter_span] at hleft
  rw [hB, Ideal.mem_span_singleton, archivedIdealCharacter_span] at hright
  obtain ⟨hsplus, hsminus⟩ := archivedGaussianSigns_at_norm_73
  refine ⟨hleft.mpr hsplus, fun h => ?_, ?_⟩
  · have he := hright.mp h
    rw [hsminus] at he
    norm_num at he
  · decide +kernel

#print axioms twice_inert_weight_eq_conductor_sum
#print axioms half_power_add_one_mem_gaussian_prime_iff
#print axioms forced_gaussian_factor_at_73

end AlpogeSuperZeta
