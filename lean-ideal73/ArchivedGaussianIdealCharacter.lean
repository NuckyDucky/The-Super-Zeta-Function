import RelativeQuarticConductorPrimes

/-! The archived conductor reading on generators descends to a character
on Gaussian ideals. The descent is the same as in QuarticIdealCharacter. -/

namespace QuarticModel

open Submodule.IsPrincipal

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

private theorem archived_factor {p : ℕ} [Fact p.Prime] (t : ℤ)
    (ht : (t : ZMod p)^2 = -1) (z : GaussianInt) :
    jacobiSym (z.re+z.im*t) p = quadraticChar (ZMod p) (gaussianResidue (t : ZMod p) ht z) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  push_cast
  rfl

theorem archivedGaussianSign_mul (z w : GaussianInt) :
    archivedGaussianSign (z*w) = archivedGaussianSign z * archivedGaussianSign w := by
  unfold archivedGaussianSign
  simp only [archived_factor (p := 41) 32 (by decide), archived_factor (p := 457) 109 (by decide),
    archived_factor (p := 1414835497) 516876951 (by decide), map_mul]
  ring

private theorem gaussian_unit_coordinates (z : GaussianInt) (hz : IsUnit z) :
    (z.re = 1 ∧ z.im = 0) ∨ (z.re = -1 ∧ z.im = 0) ∨
      (z.re = 0 ∧ z.im = 1) ∨ (z.re = 0 ∧ z.im = -1) := by
  have h := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).mpr hz
  rw [Zsqrtd.norm_def] at h
  have hn := GaussianInt.natAbs_norm_eq z
  rw [Zsqrtd.norm_eq_one_iff.mpr hz] at hn
  have hx : z.re.natAbs ≤ 1 := (Nat.le_mul_self _).trans (by omega)
  have hy : z.im.natAbs ≤ 1 := (Nat.le_mul_self _).trans (by omega)
  have xlo : -1 ≤ z.re := by omega
  have xhi : z.re ≤ 1 := by omega
  have ylo : -1 ≤ z.im := by omega
  have yhi : z.im ≤ 1 := by omega
  interval_cases z.re <;> interval_cases z.im <;> norm_num at h <;> norm_num

theorem archivedGaussianSign_unit (z : GaussianInt) (hz : IsUnit z) : archivedGaussianSign z = 1 := by
  rcases gaussian_unit_coordinates z hz with ⟨hre, him⟩ | ⟨hre, him⟩ | ⟨hre, him⟩ | ⟨hre, him⟩ <;>
    norm_num [archivedGaussianSign, hre, him]

private theorem archivedGaussianSign_associated {z w : GaussianInt} (h : Associated z w) :
    archivedGaussianSign z = archivedGaussianSign w := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, archivedGaussianSign_mul, archivedGaussianSign_unit _ u.isUnit, mul_one]

private noncomputable def idealReading (I : Ideal GaussianInt) : ℤ :=
  archivedGaussianSign (generator I)

private theorem idealReading_span (z : GaussianInt) : idealReading (Ideal.span {z}) = archivedGaussianSign z :=
  archivedGaussianSign_associated (Ideal.span_singleton_eq_span_singleton.mp
    (Ideal.span_singleton_generator (Ideal.span {z})))

noncomputable def archivedIdealCharacter : Ideal GaussianInt →* ℤ where
  toFun := idealReading
  map_one' := by
    rw [Ideal.one_eq_top, ← Ideal.span_singleton_one, idealReading_span]
    exact archivedGaussianSign_unit 1 isUnit_one
  map_mul' I J := by
    obtain ⟨x, rfl⟩ : Submodule.IsPrincipal I := inferInstance
    obtain ⟨y, rfl⟩ : Submodule.IsPrincipal J := inferInstance
    change idealReading (Ideal.span {x} * Ideal.span {y}) = idealReading (Ideal.span {x}) * idealReading (Ideal.span {y})
    rw [Ideal.span_singleton_mul_span_singleton, idealReading_span,
      idealReading_span, idealReading_span, archivedGaussianSign_mul]

theorem archivedIdealCharacter_span (z : GaussianInt) :
    archivedIdealCharacter (Ideal.span {z}) = archivedGaussianSign z := idealReading_span z

#print axioms archivedGaussianSign_mul
#print axioms archivedIdealCharacter
#print axioms archivedIdealCharacter_span

end QuarticModel
