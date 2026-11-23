import QuarticFiniteFourier
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime

namespace QuarticFiniteFourier

noncomputable def quarticCharacter : DirichletCharacter ℂ D where
  toFun := signValue
  map_one' := by
    simp only [signValue, ZMod.val_one'' (by decide : D ≠ 1),
      Nat.cast_one, jacobiSym.one_left, Int.cast_one]
  map_mul' x y := by
    have h : (↑(x.val*y.val) : ZMod D) = x*y := by simp [Nat.cast_mul]
    have hval := congrArg ZMod.val h
    rw [ZMod.val_natCast] at hval
    simp only [signValue]
    rw [← hval, Int.natCast_mod, ← jacobiSym.mod_left, Int.natCast_mul,
      jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' x hx := by
    have h : ¬ x.val.Coprime D := fun h =>
      hx (by simpa using (ZMod.isUnit_iff_coprime x.val D).mpr h)
    have hz : jacobiSym (x.val : ℤ) D = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr h
    simp only [signValue, hz, Int.cast_zero]

private theorem bad_conductor_factor {d c : ℕ}
    (hd : d ∣ D) (hc : d ∣ c)
    (hu : IsUnit (((c+1:ℕ):ZMod D)))
    (hχ : quarticCharacter ((c+1:ℕ):ZMod D) = -1) :
    ¬ quarticCharacter.FactorsThrough d := by
  intro h
  let u := hu.unit
  have hz : (c : ZMod d) = 0 := by
    obtain ⟨n, rfl⟩ := hc
    simp [Nat.cast_mul]
  have h₁ : ZMod.unitsMap hd u = 1 := by
    apply Units.ext
    change ZMod.castHom hd (ZMod d) ↑u = 1
    rw [IsUnit.unit_spec, map_natCast, Nat.cast_add, Nat.cast_one, hz, zero_add]
  have h₂ := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp h h₁
  change quarticCharacter.toUnitHom u = 1 at h₂
  have h₃ : quarticCharacter ↑u = 1 := by
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using congrArg Units.val h₂
  rw [IsUnit.unit_spec, hχ] at h₃
  norm_num at h₃

private theorem witness_of_missing_prime {d p c : ℕ}
    (hd : d ∣ D) (hp : p.Prime) (hprod : D = c*p)
    (hu : IsUnit (((c+1:ℕ):ZMod D)))
    (hχ : quarticCharacter ((c+1:ℕ):ZMod D) = -1) :
    quarticCharacter.FactorsThrough d → p ∣ d := by
  intro h
  by_contra hp'
  have hd' : d ∣ c*p := hprod ▸ hd
  have hc := ((hp.coprime_iff_not_dvd.mpr hp').symm.dvd_mul_right).mp hd'
  exact bad_conductor_factor hd hc hu hχ h

private theorem sign_on_nat (n : ℕ) :
    quarticCharacter (n : ZMod D) = (jacobiSym (n : ℤ) D : ℂ) := by
  change signValue (n : ZMod D) = _
  simp only [signValue, ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left n D]

private theorem sign_on_int (n : ℤ) :
    quarticCharacter (n : ZMod D) = (jacobiSym n D : ℂ) := by
  change signValue (n : ZMod D) = _
  simp only [signValue, ZMod.val_intCast, ← jacobiSym.mod_left n D]

theorem quarticCharacter_quadratic : quarticCharacter.IsQuadratic := by
  intro x
  change signValue x = 0 ∨ signValue x = 1 ∨ signValue x = -1
  rcases jacobiSym.trichotomy (x.val : ℤ) D with h | h | h
  · exact Or.inl (by simp only [signValue, h, Int.cast_zero])
  · exact Or.inr (Or.inl (by simp only [signValue, h, Int.cast_one]))
  · exact Or.inr (Or.inr (by simp only [signValue, h, Int.cast_neg, Int.cast_one]))

theorem quarticCharacter_at_neg_one : quarticCharacter (-1 : ZMod D) = 1 := by
  rw [show (-1 : ZMod D) = ((-1:ℤ):ZMod D) by norm_num, sign_on_int]
  norm_num

theorem quarticCharacter_even : Function.Even (quarticCharacter : ZMod D → ℂ) := by
  intro x
  rw [show -x = -1*x by ring, map_mul, quarticCharacter_at_neg_one, one_mul]

theorem quarticCharacter_at_r : quarticCharacter (R : ZMod D) = 1 := by
  rw [sign_on_nat]
  norm_num

/-- The quarter-lattice weights are invariant under multiplication by i. -/
theorem quartic_rotation (a b : ZMod D) :
    signValue (-b+R*a) = signValue (a+R*b) := by
  have hr : (R:ZMod D)^2 = -1 := by decide
  change quarticCharacter (-b+R*a) = quarticCharacter (a+R*b)
  rw [show -b+(R:ZMod D)*a = (R:ZMod D)*(a+R*b) by
    rw [mul_add, ← mul_assoc, ← pow_two, hr]; ring]
  rw [map_mul, quarticCharacter_at_r, one_mul]

/-- Each prime is forced into the conductor by one explicit unit of sign -1. -/
theorem quarticCharacter_primitive : quarticCharacter.IsPrimitive := by
  let d := quarticCharacter.conductor
  have hd : d ∣ D := quarticCharacter.conductor_dvd_level
  have hf : quarticCharacter.FactorsThrough d := quarticCharacter.factorsThrough_conductor
  have h₁ : 41 ∣ d := witness_of_missing_prime hd (by norm_num : Nat.Prime 41)
    (c := 646579822129) (by decide) ((ZMod.isUnit_iff_coprime _ _).mpr (by decide))
    (by rw [sign_on_nat]; norm_num) hf
  have h₂ : 457 ∣ d := witness_of_missing_prime hd (by norm_num : Nat.Prime 457)
    (c := 58008255377) (by decide) ((ZMod.isUnit_iff_coprime _ _).mpr (by decide))
    (by rw [sign_on_nat]; norm_num) hf
  have h₃ : 1414835497 ∣ d := witness_of_missing_prime hd (by norm_num : Nat.Prime 1414835497)
    (c := 18737) (by decide) ((ZMod.isUnit_iff_coprime _ _).mpr (by decide))
    (by rw [sign_on_nat]; norm_num) hf
  have hpq : Nat.Coprime 41 457 := by decide
  have hpqr : Nat.Coprime (41*457) 1414835497 := by decide
  exact Nat.dvd_antisymm hd (hpqr.mul_dvd_of_dvd_of_dvd (hpq.mul_dvd_of_dvd_of_dvd h₁ h₂) h₃)

theorem actual_fourier_line (h k : ZMod D) :
    (∑ b : ZMod D, ∑ a : ZMod D,
      signValue (a+R*b) * ZMod.stdAddChar (h*a+k*b)) =
      (quarticCharacter⁻¹ h * gaussSum quarticCharacter ZMod.stdAddChar) *
        (if k = R*h then (D : ℂ) else 0) :=
  primitive_fourier_line quarticCharacter quarticCharacter_primitive _
    (ZMod.isPrimitive_stdAddChar D) R h k

noncomputable def gaussAmplitude : ℂ := gaussSum quarticCharacter ZMod.stdAddChar

private theorem one_dimensional_fourier :
    ZMod.dft (quarticCharacter : ZMod D → ℂ) =
      gaussAmplitude • (quarticCharacter : ZMod D → ℂ) := by
  funext h
  rw [quarticCharacter_primitive.fourierTransform_eq_inv_mul_gaussSum,
    quarticCharacter_quadratic.inv, quarticCharacter_even h]
  simp only [Pi.smul_apply, smul_eq_mul, gaussAmplitude, mul_comm]

theorem gaussAmplitude_sq : gaussAmplitude^2 = (D : ℂ) := by
  have h := congrFun (ZMod.dft_dft (quarticCharacter : ZMod D → ℂ)) 1
  rw [one_dimensional_fourier, map_smul, one_dimensional_fourier] at h
  simpa only [Pi.smul_apply, smul_eq_mul, quarticCharacter_at_neg_one, map_one,
    mul_one, pow_two] using h

theorem gaussAmplitude_roots :
    gaussAmplitude = (Real.sqrt D : ℂ) ∨ gaussAmplitude = -(Real.sqrt D : ℂ) := by
  have hs : (Real.sqrt D : ℂ)^2 = (D : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  have h : (gaussAmplitude-(Real.sqrt D:ℂ))*(gaussAmplitude+(Real.sqrt D:ℂ)) = 0 := by
    linear_combination gaussAmplitude_sq - hs
  rcases mul_eq_zero.mp h with h₁ | h₂
  · exact Or.inl (sub_eq_zero.mp h₁)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h₂)

#print axioms quarticCharacter_primitive
#print axioms actual_fourier_line
#print axioms quartic_rotation
#print axioms gaussAmplitude_sq
#print axioms gaussAmplitude_roots

end QuarticFiniteFourier
