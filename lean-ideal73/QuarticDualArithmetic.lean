import ArchivedGaussianIdealCharacter
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace QuarticDualArithmetic

noncomputable def conductorReading (m n : ℤ) : ℤ := QuarticModel.archivedGaussianSign ⟨m,n⟩

abbrev a : ℤ := -5045155
abbrev b : ℤ := 1027708
abbrev modulus : ℕ := 26509772707289
abbrev r : ℤ := 11825711960877

theorem norm_identity : a^2 + b^2 = (modulus : ℤ) := by norm_num

/-- Exact integer description of the selected dual frequencies. -/
theorem dual_lattice (h k : ℤ) :
    (modulus : ℤ) ∣ k-r*h ↔ ∃ u v : ℤ, h = a*u-b*v ∧ k = b*u+a*v := by
  have ha : (modulus : ℤ) ∣ a+b*r := by decide
  have hb : (modulus : ℤ) ∣ -b+a*r := by decide
  constructor
  · rintro ⟨q,hq⟩
    have hk : k = r*h + modulus*q := by linarith only [hq]
    obtain ⟨c,hc⟩ := ha
    obtain ⟨d,hd⟩ := hb
    have hu : a*h+b*k = modulus*(c*h+b*q) := by
      rw [hk]
      calc
        _ = (a+b*r)*h+b*(modulus*q) := by ring
        _ = _ := by rw [hc]; ring
    have hv : -b*h+a*k = modulus*(d*h+a*q) := by
      rw [hk]
      calc
        _ = (-b+a*r)*h+a*(modulus*q) := by ring
        _ = _ := by rw [hd]; ring
    refine ⟨c*h+b*q,d*h+a*q,?_,?_⟩
    · apply mul_left_cancel₀ (show (modulus : ℤ) ≠ 0 by decide)
      linear_combination a*hu-b*hv
    · apply mul_left_cancel₀ (show (modulus : ℤ) ≠ 0 by decide)
      linear_combination b*hu+a*hv
  · rintro ⟨u,v,rfl,rfl⟩
    rw [show (b*u+a*v)-r*(a*u-b*v) = -(-b+a*r)*u+(a+b*r)*v by ring]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr hb) u) (dvd_mul_of_dvd_left ha v)

theorem dual_norm (u v : ℤ) :
    (a*u-b*v)^2 + (b*u+a*v)^2 = (modulus : ℤ)*(u^2+v^2) := by ring

private theorem residue_factor (x y : ℤ) (p : ℕ) (s : ℤ)
    (hs : r ≡ s [ZMOD (p : ℤ)]) :
    jacobiSym (x+r*y) p = jacobiSym (x+s*y) p :=
  jacobiSym.mod_left' ((Int.ModEq.refl x).add (hs.mul_right y))

theorem combined_character (x y : ℤ) :
    jacobiSym (x+r*y) modulus = QuarticDualArithmetic.conductorReading x y := by
  unfold QuarticDualArithmetic.conductorReading QuarticModel.archivedGaussianSign
  change jacobiSym (x+r*y) ((41*457)*1414835497) = _
  rw [jacobiSym.mul_right, jacobiSym.mul_right, residue_factor x y 41 32 (by decide),
    residue_factor x y 457 109 (by decide), residue_factor x y 1414835497 516876951 (by decide)]
  ring

theorem dual_character (u v : ℤ) :
    jacobiSym (a*u-b*v) modulus = QuarticDualArithmetic.conductorReading u (-v) := by
  have h : (a*u-b*v) ≡ a*(u+r*(-v)) [ZMOD (modulus : ℤ)] := by
    have hh : b ≡ a*r [ZMOD (modulus : ℤ)] := by decide
    convert (Int.ModEq.refl (a*u)).sub (hh.mul_right v) using 1
    all_goals ring
  rw [jacobiSym.mod_left' h, jacobiSym.mul_left]
  have ha : jacobiSym a modulus = 1 := by norm_num
  rw [ha, one_mul, combined_character]

#print axioms dual_lattice
#print axioms dual_norm
#print axioms combined_character
#print axioms dual_character

end QuarticDualArithmetic
