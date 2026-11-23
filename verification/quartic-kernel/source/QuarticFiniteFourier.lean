import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace QuarticFiniteFourier

/-- The two-coordinate additive transform of a coefficient depending on a + r b. -/
theorem fourier_line {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (e : AddChar (ZMod N) ℂ) (he : e.IsPrimitive) (r h k : ZMod N) :
    (∑ b : ZMod N, ∑ a : ZMod N, f (a + r*b) * e (h*a + k*b)) =
      (∑ u : ZMod N, f u * e (h*u)) * (if k = r*h then (N : ℂ) else 0) := by
  calc
    _ = ∑ b : ZMod N, ∑ u : ZMod N, (f u * e (h*u)) * e (b*(k-r*h)) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Fintype.sum_equiv (Equiv.addRight (r*b)) _ _ fun a => ?_
      change f (a + r*b) * e (h*a + k*b) =
        (f (a + r*b) * e (h*(a+r*b))) * e (b*(k-r*h))
      rw [mul_assoc, ← e.map_add_eq_mul]
      congr 2
      ring
    _ = _ := by
      simp_rw [← Finset.sum_mul]
      rw [← Finset.mul_sum, AddChar.sum_mulShift _ he, ZMod.card]
      by_cases hkr : k = r*h <;> simp [sub_eq_zero, hkr]

/-- On the selected line the remaining coefficient is the primitive Gauss transform. -/
theorem primitive_fourier_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (e : AddChar (ZMod N) ℂ) (he : e.IsPrimitive)
    (r h k : ZMod N) :
    (∑ b : ZMod N, ∑ a : ZMod N, χ (a + r*b) * e (h*a + k*b)) =
      (χ⁻¹ h * gaussSum χ e) * (if k = r*h then (N : ℂ) else 0) := by
  rw [fourier_line _ e he]
  congr 1
  simpa [gaussSum, AddChar.mulShift_apply, mul_comm] using
    (gaussSum_mulShift_of_isPrimitive e hχ h)

abbrev D : ℕ := 26509772707289
abbrev R : ℕ := 11825711960877

def signValue (u : ZMod D) : ℂ := (jacobiSym (u.val : ℤ) D : ℂ)

private theorem residue_factor (a b : ℤ) (p : ℕ) (t : ℤ)
    (ht : (R : ℤ) ≡ t [ZMOD (p : ℤ)]) :
    jacobiSym (a + R*b) p = jacobiSym (a + t*b) p :=
  jacobiSym.mod_left' ((Int.ModEq.refl a).add (ht.mul_right b))

theorem sign_at_integer_point (a b : ℤ) :
    signValue ((a : ZMod D) + R * (b : ZMod D)) =
      ((jacobiSym (a+32*b) 41 * jacobiSym (a+109*b) 457 *
        jacobiSym (a+516876951*b) 1414835497 : ℤ) : ℂ) := by
  have e : ((a : ZMod D) + R * (b : ZMod D)) = ((a+R*b : ℤ) : ZMod D) := by push_cast; rfl
  rw [e, signValue, ZMod.val_intCast, ← jacobiSym.mod_left]
  congr 1
  change jacobiSym (a+R*b) ((41*457)*1414835497) = _
  rw [jacobiSym.mul_right, jacobiSym.mul_right, residue_factor a b 41 32 (by decide),
    residue_factor a b 457 109 (by decide), residue_factor a b 1414835497 516876951 (by decide)]

/-- The actual three-residue quartic weights vanish on every off-line frequency. -/
theorem quartic_off_line (h k : ZMod D) (hk : k ≠ R*h) :
    (∑ b : ZMod D, ∑ a : ZMod D,
      signValue (a+R*b) * ZMod.stdAddChar (h*a+k*b)) = 0 := by
  rw [fourier_line _ _ (ZMod.isPrimitive_stdAddChar _) _ _ _, if_neg hk, mul_zero]

#print axioms fourier_line
#print axioms primitive_fourier_line
#print axioms sign_at_integer_point
#print axioms quartic_off_line

end QuarticFiniteFourier

