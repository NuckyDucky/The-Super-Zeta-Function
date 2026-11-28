import GaussianFixedPointSquaring
import GaussianFixedPointHorner

namespace FieldTarget

open Finset

/-- Keep the current Taylor term and their running sum together. -/
def gaussianTaylorPrefix (a : GaussianInt) (d s : ℕ) : ℕ → GaussianInt × GaussianInt
  | 0 => ((s : GaussianInt), 0)
  | k + 1 =>
    match gaussianTaylorPrefix a d s k with
    | (term, sum) => (gaussianFloorDiv (a * term) (d * (k + 1)), sum + term)

private theorem gaussianTaylorPrefix_spec (a : GaussianInt) (d s n : ℕ) :
    gaussianTaylorPrefix a d s n =
      (gaussianTaylorTerm a d s n, gaussianTaylorSum a d s n) := by
  induction n with
  | zero => simp [gaussianTaylorPrefix, gaussianTaylorTerm, gaussianTaylorSum]
  | succ n ih =>
    simp only [gaussianTaylorPrefix, ih, gaussianTaylorTerm, gaussianTaylorSum, sum_range_succ]

def gaussianFixedPointExpFast (a : GaussianInt) (d s K n : ℕ) : GaussianInt :=
  gaussianFixedPointSquares (gaussianTaylorPrefix a (d * 2 ^ K) s n).2 s K

theorem gaussianFixedPointExpFast_eq (a : GaussianInt) (d s K n : ℕ) :
    gaussianFixedPointExpFast a d s K n = gaussianFixedPointExp a d s K n := by
  simp only [gaussianFixedPointExpFast, gaussianFixedPointExp, gaussianTaylorPrefix_spec]

private theorem real_gaussian_mul (a b : ℤ) :
    (⟨a, 0⟩ : GaussianInt) * ⟨b, 0⟩ = ⟨a * b, 0⟩ := by
  ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem real_gaussian_add (a b : ℤ) :
    (⟨a, 0⟩ : GaussianInt) + ⟨b, 0⟩ = ⟨a + b, 0⟩ := by
  ext <;> simp

private theorem real_gaussian_floor (a : ℤ) (d : ℕ) :
    gaussianFloorDiv ⟨a, 0⟩ d = ⟨a / (d : ℤ), 0⟩ := by
  simp [gaussianFloorDiv]

/-- The real inputs do not need a second arithmetic coordinate. -/
def intTaylorPrefix (a : ℤ) (d s : ℕ) : ℕ → ℤ × ℤ
  | 0 => ((s : ℤ), 0)
  | k + 1 =>
    match intTaylorPrefix a d s k with
    | (term, sum) => (a * term / (d * (k + 1) : ℕ), sum + term)

private theorem gaussianTaylorPrefix_real (a : ℤ) (d s n : ℕ) :
    gaussianTaylorPrefix ⟨a, 0⟩ d s n =
      ((⟨(intTaylorPrefix a d s n).1, 0⟩ : GaussianInt), ⟨(intTaylorPrefix a d s n).2, 0⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gaussianTaylorPrefix, ih, intTaylorPrefix, real_gaussian_mul,
      real_gaussian_add, real_gaussian_floor]

theorem gaussianTaylorTerm_real_eq (a : ℤ) (d s n : ℕ) :
    gaussianTaylorTerm ⟨a, 0⟩ d s n = ⟨(intTaylorPrefix a d s n).1, 0⟩ := by
  have h := congrArg Prod.fst (gaussianTaylorPrefix_real a d s n)
  simpa only [gaussianTaylorPrefix_spec] using h

def intFixedPointSquares (a : ℤ) (s : ℕ) : ℕ → ℤ
  | 0 => a
  | k + 1 =>
    let z := intFixedPointSquares a s k
    z * z / (s : ℤ)

private theorem gaussianFixedPointSquares_real (a : ℤ) (s n : ℕ) :
    gaussianFixedPointSquares ⟨a, 0⟩ s n = ⟨intFixedPointSquares a s n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gaussianFixedPointSquares, ih, real_gaussian_mul, real_gaussian_floor, intFixedPointSquares]

def intFixedPointExp (a : ℤ) (d s K n : ℕ) : ℤ :=
  intFixedPointSquares (intTaylorPrefix a (d * 2 ^ K) s n).2 s K

theorem gaussianFixedPointExp_real_eq (a : ℤ) (d s K n : ℕ) :
    gaussianFixedPointExp ⟨a, 0⟩ d s K n = ⟨intFixedPointExp a d s K n, 0⟩ := by
  rw [← gaussianFixedPointExpFast_eq]
  simp only [gaussianFixedPointExpFast, gaussianTaylorPrefix_real, gaussianFixedPointSquares_real,
    intFixedPointExp]

def intFixedPointHorner (coeff : ℕ → ℤ) (q : ℤ) (s : ℕ) : ℕ → ℕ → ℤ
  | _, 0 => 0
  | k, n + 1 => coeff k * (s : ℤ) + q * intFixedPointHorner coeff q s (k + 1) n / (s : ℤ)

theorem gaussianFixedPointHorner_real_eq (coeff : ℕ → ℤ) (q : ℤ) (s k n : ℕ) :
    gaussianFixedPointHorner coeff ⟨q, 0⟩ s k n = ⟨intFixedPointHorner coeff q s k n, 0⟩ := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [gaussianFixedPointHorner, intFixedPointHorner, ih, real_gaussian_mul, real_gaussian_floor,
      real_gaussian_add]

#print axioms gaussianFixedPointExpFast_eq
#print axioms gaussianFixedPointExp_real_eq
#print axioms gaussianFixedPointHorner_real_eq

end FieldTarget
