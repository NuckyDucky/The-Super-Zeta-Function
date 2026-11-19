import SuperZeta.Quartet

/-! The signed twisted cosine equations come from neutral fixed pairs of the
two marked exponentials. The angle may be supplied by the native cap orbit,
while the fixed pair reconstructed here belongs to the marked map. -/

noncomputable section

namespace DottieOriented.MarkedCharacteristic

open Complex
open SuperZeta.Reciprocal (lifts)
open SuperZeta.Quartet (coordinate coordinate_mul coordinate_phase phase)

def markA (φ : ℝ) : ℂ := exp (-(φ : ℂ) * I)
def markB (φ : ℝ) : ℂ := exp ((φ : ℂ) * I)

def markedStep (φ : ℝ) (L : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (markA φ * exp (lifts L p).1, markB φ * exp (lifts L p).2)

def markedScalarReturn (φ : ℝ) (L z : ℂ) : ℂ :=
  markA φ * exp (L * (markB φ * exp (-L * z)))

theorem marked_step_twice_fst (φ : ℝ) (L : ℂ) (p : ℂ × ℂ) :
    (markedStep φ L (markedStep φ L p)).1 = markedScalarReturn φ L p.1 := rfl

def characteristic (φ : ℝ) (α : ℂ) : Prop :=
  α ^ 2 * exp (α - α⁻¹) = -exp (2 * ((φ : ℂ) * I))

private theorem markA_ne_zero (φ : ℝ) : markA φ ≠ 0 := exp_ne_zero _
private theorem markB_ne_zero (φ : ℝ) : markB φ ≠ 0 := exp_ne_zero _

private theorem markA_exp_double (φ : ℝ) :
    markA φ * exp (2 * ((φ : ℂ) * I)) = markB φ := by
  unfold markA markB
  rw [← exp_add]
  congr 1
  ring

private theorem inv_of_mul_one {U V : ℂ} (h : U * V = 1) : V = U⁻¹ := by
  have hU : U ≠ 0 := by intro hu; simp [hu] at h
  calc
    V = U⁻¹ * (U * V) := by rw [← mul_assoc, inv_mul_cancel₀ hU, one_mul]
    _ = U⁻¹ := by rw [h, mul_one]

private theorem characteristic_iff_balance (φ : ℝ) (α : ℂ) :
    characteristic φ α ↔ α ^ 2 * (markA φ * exp α) = -(markB φ * exp α⁻¹) := by
  unfold characteristic
  rw [← mul_right_inj' (mul_ne_zero (markA_ne_zero φ) (exp_ne_zero α⁻¹))]
  have hL : (markA φ * exp α⁻¹) * (α ^ 2 * exp (α - α⁻¹)) =
      α ^ 2 * (markA φ * exp α) := by
    calc
      _ = α ^ 2 * (markA φ * (exp (α - α⁻¹) * exp α⁻¹)) := by ring
      _ = _ := by rw [← exp_add, sub_add_cancel]
  have hR : (markA φ * exp α⁻¹) * (-exp (2 * ((φ : ℂ) * I))) =
      -(markB φ * exp α⁻¹) := by
    calc
      _ = -((markA φ * exp (2 * ((φ : ℂ) * I))) * exp α⁻¹) := by ring
      _ = _ := by rw [markA_exp_double]
  rw [hL, hR]

/-- A fixed pair of the two marked stages at unit multiplier yields the
twisted characteristic equation for its actual first exponent. -/
theorem marked_fixed_characteristic {φ : ℝ} {L : ℂ} {p : ℂ × ℂ}
    (hfixed : markedStep φ L p = p)
    (hunit : (lifts L p).1 * (lifts L p).2 = 1) :
    characteristic φ (lifts L p).1 := by
  let U := (lifts L p).1
  let V := (lifts L p).2
  change U * V = 1 at hunit
  change characteristic φ U
  have hV : V = U⁻¹ := inv_of_mul_one hunit
  have hP : markA φ * exp U = p.1 := congrArg Prod.fst hfixed
  have hQ : markB φ * exp V = p.2 := congrArg Prod.snd hfixed
  apply (characteristic_iff_balance φ U).2
  rw [← hV, hP, hQ]
  calc
    U ^ 2 * p.1 = U * (-V * p.2) := by dsimp [U, V, lifts]; ring
    _ = -p.2 := by rw [neg_mul, mul_neg, ← mul_assoc, hunit, one_mul]

private theorem characteristic_iff_square (φ : ℝ) (α : ℂ) :
    characteristic φ α ↔ (α * exp ((coordinate α - (φ : ℂ)) * I)) ^ 2 = -1 := by
  have hexp (w : ℂ) : exp (2 * w) = (exp w) ^ 2 := by rw [two_mul, exp_add, pow_two]
  have hshift : 2 * ((coordinate α - (φ : ℂ)) * I) = (α - α⁻¹) - 2 * ((φ : ℂ) * I) := by
    calc
      _ = 2 * (coordinate α * I) - 2 * ((φ : ℂ) * I) := by ring
      _ = _ := by rw [coordinate_mul]
  unfold characteristic
  rw [mul_pow, ← hexp, hshift, exp_sub (α - α⁻¹), ← mul_div_assoc,
    div_eq_iff (exp_ne_zero _), neg_one_mul]

/-- The two square roots specify the sign and recover the actual exponent. -/
theorem characteristic_to_signed {φ : ℝ} {α : ℂ} (h : characteristic φ α) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      coordinate α = (σ : ℂ) * cos (coordinate α - (φ : ℂ)) ∧
      phase (σ : ℂ) (coordinate α - (φ : ℂ)) = α := by
  let z := α * exp ((coordinate α - (φ : ℂ)) * I)
  have hsq : z ^ 2 = -1 := (characteristic_iff_square φ α).mp h
  have hfactor : (z - I) * (z + I) = 0 := by linear_combination hsq - I_sq
  have hs : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ z = (σ : ℂ) * I := by
    rcases mul_eq_zero.mp hfactor with hp | hm
    · exact ⟨1, Or.inl rfl, by simpa using sub_eq_zero.mp hp⟩
    · exact ⟨-1, Or.inr rfl, by simpa using eq_neg_of_add_eq_zero_left hm⟩
  obtain ⟨σ, hσ, hs⟩ := hs
  have hσ' : (σ : ℂ) = 1 ∨ (σ : ℂ) = -1 := by rcases hσ with hσ | hσ <;> simp [hσ]
  have hp : phase (σ : ℂ) (coordinate α - (φ : ℂ)) = α := by
    unfold phase
    rw [← hs]
    dsimp [z]
    rw [exp_neg, mul_assoc, mul_inv_cancel₀ (exp_ne_zero _), mul_one]
  exact ⟨σ, hσ, by simpa only [hp] using coordinate_phase hσ' (coordinate α - (φ : ℂ)), hp⟩

theorem signed_to_characteristic {φ σ : ℝ} {u : ℂ} (hσ : σ = 1 ∨ σ = -1)
    (hu : u = (σ : ℂ) * cos (u - (φ : ℂ))) :
    let α := phase (σ : ℂ) (u - (φ : ℂ))
    coordinate α = u ∧ characteristic φ α := by
  let α := phase (σ : ℂ) (u - (φ : ℂ))
  have hσ' : (σ : ℂ) = 1 ∨ (σ : ℂ) = -1 := by rcases hσ with hσ | hσ <;> simp [hσ]
  have hc : coordinate α = u := (coordinate_phase hσ' _).trans hu.symm
  refine ⟨hc, (characteristic_iff_square φ α).2 ?_⟩
  have he : α * exp ((u - (φ : ℂ)) * I) = (σ : ℂ) * I := by
    unfold α phase
    rw [exp_neg, mul_assoc, inv_mul_cancel₀ (exp_ne_zero _), mul_one]
  rw [hc, he]
  rcases hσ' with hσ' | hσ' <;> simp [hσ', I_sq]

/-- Recover the parameter and both ordered outputs from the characteristic phase. -/
def recoverMarked (φ : ℝ) (α : ℂ) : ℂ × (ℂ × ℂ) :=
  (α / (markB φ * exp α⁻¹), (markA φ * exp α, markB φ * exp α⁻¹))

theorem marked_scalar_hasDerivAt (φ : ℝ) (L z : ℂ) :
    HasDerivAt (markedScalarReturn φ L)
      (-L ^ 2 * (markB φ * exp (-L * z)) * markedScalarReturn φ L z) z := by
  have hinner := ((hasDerivAt_id z).const_mul (-L)).cexp.const_mul (markB φ)
  have h := ((hinner.const_mul L).cexp).const_mul (markA φ)
  convert h using 1
  dsimp [markedScalarReturn]
  ring

theorem marked_fixed_multiplier {φ : ℝ} {L : ℂ} {p : ℂ × ℂ}
    (hfixed : markedStep φ L p = p) :
    deriv (markedScalarReturn φ L) p.1 = (lifts L p).1 * (lifts L p).2 := by
  have hQ : markB φ * exp (-L * p.1) = p.2 := congrArg Prod.snd hfixed
  have hret : markedScalarReturn φ L p.1 = p.1 := by
    rw [← marked_step_twice_fst, hfixed, hfixed]
  rw [(marked_scalar_hasDerivAt φ L p.1).deriv, hret, hQ]
  dsimp [lifts]
  ring

/-- The reconstructed values satisfy both marked equations with actual
exponents `(α, α⁻¹)` and complete return multiplier one. -/
theorem recoverMarked_from_characteristic {φ : ℝ} {α : ℂ} (h : characteristic φ α) :
    let x := recoverMarked φ α
    markedStep φ x.1 x.2 = x.2 ∧ lifts x.1 x.2 = (α, α⁻¹) ∧
      deriv (markedScalarReturn φ x.1) x.2.1 = 1 := by
  have hα : α ≠ 0 := by intro ha; simp [characteristic, ha, exp_ne_zero] at h
  let x := recoverMarked φ α
  have hQ : x.2.2 ≠ 0 := mul_ne_zero (markB_ne_zero φ) (exp_ne_zero _)
  have hU : x.1 * x.2.2 = α := div_mul_cancel₀ α hQ
  have hV : -x.1 * x.2.1 = α⁻¹ := by
    have hbal := (characteristic_iff_balance φ α).mp h
    change α ^ 2 * x.2.1 = -x.2.2 at hbal
    change -(α / x.2.2) * x.2.1 = α⁻¹
    field_simp [hα, hQ]
    linear_combination -hbal
  have hL : lifts x.1 x.2 = (α, α⁻¹) := Prod.ext hU hV
  have hf : markedStep φ x.1 x.2 = x.2 := by
    unfold markedStep
    rw [hL]
    rfl
  refine ⟨hf, hL, ?_⟩
  rw [marked_fixed_multiplier hf, hL]
  exact mul_inv_cancel₀ hα

theorem recoverMarked_actual {φ : ℝ} {L : ℂ} {p : ℂ × ℂ}
    (hfixed : markedStep φ L p = p)
    (hunit : (lifts L p).1 * (lifts L p).2 = 1) :
    recoverMarked φ (lifts L p).1 = (L, p) := by
  let α := (lifts L p).1
  have hV : (lifts L p).2 = α⁻¹ := inv_of_mul_one hunit
  have hP : markA φ * exp α = p.1 := congrArg Prod.fst hfixed
  have hQ : markB φ * exp α⁻¹ = p.2 := by
    rw [← hV]
    exact congrArg Prod.snd hfixed
  have hQ0 : p.2 ≠ 0 := hQ ▸ mul_ne_zero (markB_ne_zero φ) (exp_ne_zero _)
  change recoverMarked φ α = (L, p)
  unfold recoverMarked
  rw [hP, hQ]
  exact Prod.ext (mul_div_cancel_right₀ L hQ0) (Prod.eta p)

def recoverSigned (φ σ : ℝ) (u : ℂ) : ℂ × (ℂ × ℂ) :=
  recoverMarked φ (phase (σ : ℂ) (u - (φ : ℂ)))

/-- From a marked fixed pair, the signed root reproduces the same parameter
and both ordered outputs. -/
theorem marked_fixed_to_signed {φ : ℝ} {L : ℂ} {p : ℂ × ℂ}
    (hfixed : markedStep φ L p = p)
    (hunit : (lifts L p).1 * (lifts L p).2 = 1) :
    let u := coordinate (lifts L p).1
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ u = (σ : ℂ) * cos (u - (φ : ℂ)) ∧
      recoverSigned φ σ u = (L, p) := by
  obtain ⟨σ, hσ, hu, hp⟩ := characteristic_to_signed (marked_fixed_characteristic hfixed hunit)
  refine ⟨σ, hσ, hu, ?_⟩
  unfold recoverSigned
  rw [hp, recoverMarked_actual hfixed hunit]

/-- Conversely each signed cosine root at the chosen phase gives a marked
fixed pair at multiplier one with that same characteristic coordinate. -/
theorem signed_to_marked_fixed {φ σ : ℝ} {u : ℂ} (hσ : σ = 1 ∨ σ = -1)
    (hu : u = (σ : ℂ) * cos (u - (φ : ℂ))) :
    let x := recoverSigned φ σ u
    let uv := lifts x.1 x.2
    markedStep φ x.1 x.2 = x.2 ∧ uv.1 * uv.2 = 1 ∧ coordinate uv.1 = u ∧
      deriv (markedScalarReturn φ x.1) x.2.1 = 1 := by
  obtain ⟨hc, hchar⟩ := signed_to_characteristic hσ hu
  obtain ⟨hf, hl, hm⟩ := recoverMarked_from_characteristic hchar
  dsimp [recoverSigned] at *
  refine ⟨hf, ?_, ?_, hm⟩
  · rw [hl]
    apply mul_inv_cancel₀
    intro hα
    change phase (σ : ℂ) (u - (φ : ℂ)) = 0 at hα
    simp [characteristic, hα, exp_ne_zero] at hchar
  · rw [hl]
    exact hc

end DottieOriented.MarkedCharacteristic
