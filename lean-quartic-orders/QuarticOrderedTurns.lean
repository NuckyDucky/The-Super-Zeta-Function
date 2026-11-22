import HiddenQuarticQuaternion
import Mathlib.Algebra.Quaternion

namespace SuperZeta.QuarticOrderedTurns
noncomputable section
open QuarticTurn ReflectedGaussianReading RingReversibility GaussianRingMidpoint
open scoped ComplexConjugate

/-- Hamilton's a + b j in mathlib's real quaternion algebra. -/
def pack (a b : ℂ) : Quaternion ℝ := ⟨a.re, a.im, b.re, b.im⟩
def J : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def K : Quaternion ℝ := ⟨0, 0, 0, 1⟩
def jk (q : Quaternion ℝ) := J * q * K
def kj (q : Quaternion ℝ) := K * q * J

theorem order_difference (a b : ℂ) :
    jk (pack a b) - kj (pack a b) = pack (2 * Complex.I * conj a) 0 := by
  apply Quaternion.ext <;>
    simp [jk, kj, J, K, pack, Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ,
      Quaternion.mul_imK, Complex.mul_re, Complex.mul_im] <;> ring

/-- Adding any label in the j,k plane changes neither the order difference
    nor the zero test. The ink may be chosen differently at every input. -/
theorem order_difference_after_paint (a b ink : ℂ) :
    jk (pack a b + pack 0 ink) - kj (pack a b + pack 0 ink) =
      jk (pack a b) - kj (pack a b) := by
  have h : pack a b + pack 0 ink = pack a (b + ink) := by
    apply Quaternion.ext <;> simp [pack]
  rw [h, order_difference, order_difference]

def scalar (q : Quaternion ℝ) : ℂ := ⟨q.re, q.imI⟩

/-- Recover the complex Gaussian value (including its phase) from the two orders. -/
theorem recover_from_orders (a b : ℂ) :
    conj (scalar (jk (pack a b) - kj (pack a b)) / (2 * Complex.I)) = a := by
  rw [order_difference]
  change conj ((2 * Complex.I * conj a) / (2 * Complex.I)) = a
  have h : (2 * Complex.I * conj a) / (2 * Complex.I) = conj a := by
    apply (div_eq_iff (by simp : (2 * Complex.I) ≠ 0)).mpr
    ring
  simp [h]

theorem zero_orders (b : ℂ) :
    jk (pack 0 b) = pack 0 (-Complex.I * conj b) ∧
    kj (pack 0 b) = pack 0 (-Complex.I * conj b) := by
  constructor <;> apply Quaternion.ext <;>
    simp [jk, kj, J, K, pack, Quaternion.mul_re, Quaternion.mul_imI, Quaternion.mul_imJ,
      Quaternion.mul_imK, Complex.mul_re, Complex.mul_im]

private theorem pack_first_zero (a : ℂ) : pack a 0 = 0 ↔ a = 0 := by
  constructor
  · intro he
    exact Complex.ext (congrArg (fun q : Quaternion ℝ => q.re) he)
      (congrArg (fun q : Quaternion ℝ => q.imI) he)
  · rintro rfl
    rfl

theorem order_eq_iff (a b : ℂ) : jk (pack a b) = kj (pack a b) ↔ a = 0 := by
  rw [← sub_eq_zero, order_difference, pack_first_zero]
  simp

/-- This reading has the fixed quartic's full theta integral and raw Dirichlet total.
    Its input is recovered through the original super-zeta chart. -/
def reading (ξ : Set.range address) : Quaternion ℝ :=
  let q := inChart (fun x => HiddenQuarticQuaternion.hidden x.val) ξ
  pack q.1 q.2

theorem fixed_input_test (x : Input) :
    jk (reading (chart x)) ≠ kj (reading (chart x)) ↔ completed x.val ≠ 0 := by
  unfold reading
  rw [same_reading]
  exact (order_eq_iff _ _).not

theorem ring_exclusion_iff :
    (∀ w, ∀ hw : w ∈ rightRing,
      jk (reading (chart (inputOfRing hw))) ≠ kj (reading (chart (inputOfRing hw)))) ↔
    ∀ w ∈ rightRing, completed w ≠ 0 := by
  constructor
  · exact fun disorder w hw => (fixed_input_test (inputOfRing hw)).mp (disorder w hw)
  · exact fun clear w hw => (fixed_input_test (inputOfRing hw)).mpr (clear w hw)

end
end SuperZeta.QuarticOrderedTurns

#print axioms SuperZeta.QuarticOrderedTurns.order_difference
#print axioms SuperZeta.QuarticOrderedTurns.order_difference_after_paint
#print axioms SuperZeta.QuarticOrderedTurns.recover_from_orders
#print axioms SuperZeta.QuarticOrderedTurns.zero_orders
#print axioms SuperZeta.QuarticOrderedTurns.order_eq_iff
#print axioms SuperZeta.QuarticOrderedTurns.fixed_input_test
#print axioms SuperZeta.QuarticOrderedTurns.ring_exclusion_iff
