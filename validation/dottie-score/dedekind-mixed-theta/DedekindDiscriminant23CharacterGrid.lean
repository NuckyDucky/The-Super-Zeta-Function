import DedekindDiscriminant23CharacterSamples
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

namespace FieldTarget

open Finset
open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

private def gridIndex (k : ℕ) : Fin 1025 := ⟨k % 1025, Nat.mod_lt _ (by decide)⟩

/-- An interval sum of consecutive interior samples, indexed from one. -/
def discriminant23CharacterGridBlock (high : Bool) (start : ℕ) : ℕ → Box
  | 0 => constant 0
  | k + 1 => add (discriminant23CharacterGridBlock high start k)
      (discriminant23CharacterSample high (gridIndex (start + k + 1)))

private theorem box_add_assoc (a b c : Box) : add (add a b) c = add a (add b c) := by
  cases a
  cases b
  cases c
  simp [add, Int.add_assoc]

/-- The interval additions for separately replayed consecutive blocks are exact. -/
theorem discriminant23_characterGridBlock_append (high : Bool) (start m n : ℕ) :
    discriminant23CharacterGridBlock high start (m + n) =
      add (discriminant23CharacterGridBlock high start m)
        (discriminant23CharacterGridBlock high (start + m) n) := by
  induction n with
  | zero =>
    cases discriminant23CharacterGridBlock high start m
    simp [discriminant23CharacterGridBlock, add, constant]
  | succ n ih =>
    rw [Nat.add_succ, discriminant23CharacterGridBlock,
      discriminant23CharacterGridBlock, ih, box_add_assoc]
    simp only [Nat.add_assoc]

def discriminant23CharacterGridBox (high : Bool) : Box :=
  divInt (mul (constant 3) (add
    (divInt (add (discriminant23CharacterSample high 0)
      (discriminant23CharacterSample high 1024)) 2)
    (discriminant23CharacterGridBlock high 0 1023))) 1024

private theorem gridBlock_contains (high : Bool) (start n : ℕ) :
    Contains (discriminant23CharacterGridBlock high start n)
      (∑ k ∈ range n, discriminant23CharacterLogPolynomial (discriminant23EndpointHeight high)
        (discriminant23LogNode (gridIndex (start + k + 1)))) := by
  induction n with
  | zero => simpa only [discriminant23CharacterGridBlock, range_zero, sum_empty, Int.cast_zero]
      using constant_contains 0
  | succ n ih =>
    rw [sum_range_succ]
    exact add_contains ih (discriminant23_characterSample_contains high (gridIndex (start + n + 1)))

theorem discriminant23_characterGridBox_contains (high : Bool) :
    Contains (discriminant23CharacterGridBox high)
      (trapezoidal_integral
        (discriminant23CharacterLogPolynomial (discriminant23EndpointHeight high))
        1024 0 3) := by
  let f := discriminant23CharacterLogPolynomial (discriminant23EndpointHeight high)
  have hzero : discriminant23LogNode 0 = 0 := by norm_num [discriminant23LogNode]
  have htop : discriminant23LogNode 1024 = 3 := by norm_num [discriminant23LogNode]
  have h₀ := discriminant23_characterSample_contains high (0 : Fin 1025)
  have h₁ := discriminant23_characterSample_contains high (1024 : Fin 1025)
  rw [hzero] at h₀
  rw [htop] at h₁
  have he := divInt_contains (add_contains h₀ h₁) (d := 2) (by decide)
  have hi := gridBlock_contains high 0 1023
  have heq : (∑ k ∈ range 1023, f (discriminant23LogNode (gridIndex (0 + k + 1)))) =
      ∑ k ∈ range (1024 - 1), f (0 + (k + 1) * ((3 : ℝ) - 0) / 1024) := by
    apply sum_congr rfl
    intro k hk
    have hsmall : k + 1 < 1025 := by
      have h := mem_range.mp hk
      omega
    congr 1
    simp only [discriminant23LogNode, gridIndex, Nat.mod_eq_of_lt hsmall,
      Nat.cast_add, Nat.cast_one, sub_zero, zero_add]
    ring
  change Contains (discriminant23CharacterGridBlock high 0 1023) (∑ k ∈ range 1023,
    f (discriminant23LogNode (gridIndex (0 + k + 1)))) at hi
  rw [heq] at hi
  have h := divInt_contains (mul_contains (constant_contains 3) (add_contains he hi))
    (d := 1024) (by decide)
  change Contains (discriminant23CharacterGridBox high) (trapezoidal_integral f 1024 0 3)
  rw [trapezoidal_integral]
  convert h using 1 <;> try rfl
  norm_num [Int.cast_ofNat]
  ring

#print axioms discriminant23_characterGridBlock_append
#print axioms discriminant23_characterGridBox_contains

end

end FieldTarget
