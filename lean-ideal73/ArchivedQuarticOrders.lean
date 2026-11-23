import ArchivedQuarticTotal
import Mathlib.Algebra.Quaternion

/-! The Hamilton definitions and algebra below come from QuarticOrderedTurns.lean
at 7053444979826a20e4393085454a38835602c48f. -/
namespace SuperZeta.QuarticOrderedTurns
noncomputable section
open scoped ComplexConjugate Quaternion

/-- Hamilton's a + b j in mathlib's real quaternion algebra. -/
def pack (a b : ℂ) : Quaternion ℝ := ⟨a.re, a.im, b.re, b.im⟩
def J : Quaternion ℝ := ⟨0, 0, 1, 0⟩
def K : Quaternion ℝ := ⟨0, 0, 0, 1⟩
def jk (q : Quaternion ℝ) := J * q * K
def kj (q : Quaternion ℝ) := K * q * J

theorem order_difference (a b : ℂ) :
    jk (pack a b) - kj (pack a b) = pack (2 * Complex.I * conj a) 0 := by
  apply Quaternion.ext <;> unfold jk kj
  all_goals
    first | rw [Quaternion.re_sub] | rw [Quaternion.imI_sub] |
      rw [Quaternion.imJ_sub] | rw [Quaternion.imK_sub]
    repeat' first | rw [Quaternion.re_mul] | rw [Quaternion.imI_mul] |
      rw [Quaternion.imJ_mul] | rw [Quaternion.imK_mul]
    simp [J, K, pack, Complex.mul_re, Complex.mul_im] <;> ring

private theorem pack_add_ink (a b ink : ℂ) : pack a b + pack 0 ink = pack a (b+ink) := by
  apply Quaternion.ext
  all_goals
    first | rw [Quaternion.re_add] | rw [Quaternion.imI_add] |
      rw [Quaternion.imJ_add] | rw [Quaternion.imK_add]
    simp [pack]

/-- Adding any label in the j,k plane changes neither the order difference
    nor the zero test. The ink may be chosen differently at every input. -/
theorem order_difference_after_paint (a b ink : ℂ) :
    jk (pack a b + pack 0 ink) - kj (pack a b + pack 0 ink) =
      jk (pack a b) - kj (pack a b) := by
  rw [pack_add_ink, order_difference, order_difference]

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
  constructor <;> apply Quaternion.ext
  all_goals
    first | unfold jk | unfold kj
    repeat' first | rw [Quaternion.re_mul] | rw [Quaternion.imI_mul] |
      rw [Quaternion.imJ_mul] | rw [Quaternion.imK_mul]
    simp [J, K, pack, Complex.mul_re, Complex.mul_im]

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

theorem J_and_K_square : J * J = -1 ∧ K * K = -1 := by
  constructor <;> apply Quaternion.ext
  all_goals
    first | rw [Quaternion.re_mul] | rw [Quaternion.imI_mul] |
      rw [Quaternion.imJ_mul] | rw [Quaternion.imK_mul]
    norm_num [J, K]

private theorem j_reading_k (a b : ℂ) : (J * pack a b).imK = -a.im := by
  rw [Quaternion.imK_mul]
  simp [J, pack]

open QuarticModel SuperZeta.StirlingCorrection

def paintedReading (w ink : ℂ) : Quaternion ℝ :=
  pack (archivedMellin w) (HiddenQuarticQuaternion.total w) + pack 0 ink

private theorem paintedReading_eq (w ink : ℂ) :
    paintedReading w ink = pack (archivedMellin w) (HiddenQuarticQuaternion.total w+ink) := by
  exact pack_add_ink _ _ _

/-- The signed boundary margin persists in the original Hamilton ordering
at each ring input and its mirror, for every label painted in the j,k slot. -/
theorem dottie_ring_painted_orders_of_replay {S : ℝ} (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (H w).im ≤ -(190*((w.re-1/2)*S)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (archivedMellin w / (archivedDottieCompletionScale : ℂ)-H w).im ≤ 189*((w.re-1/2)*S))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink inkMirror : ℂ) :
    let q := paintedReading w ink
    let qm := paintedReading (1-conj w) inkMirror
    0 < (J*q).imK ∧ (J*qm).imK < 0 ∧ jk q ≠ kj q ∧ jk qm ≠ kj qm := by
  have hs := archivedDottieRing_exclusion_of_normalized_remainder
    archivedDottieCompletionScale_pos hS H model tail hw
  have hp : 0 < archivedDottieCompletionScale*S/2048 :=
    div_pos (mul_pos archivedDottieCompletionScale_pos hS) (by norm_num)
  dsimp only
  simp only [paintedReading_eq, j_reading_k]
  refine ⟨by linarith [hs.1], by linarith [hs.2.1], ?_, ?_⟩
  · intro eq
    have hf := hs.1
    rw [(order_eq_iff _ _).mp eq, Complex.zero_im] at hf
    linarith
  · intro eq
    have hf := hs.2.1
    rw [(order_eq_iff _ _).mp eq, Complex.zero_im] at hf
    linarith

#print axioms J_and_K_square
#print axioms order_difference_after_paint
#print axioms recover_from_orders
#print axioms dottie_ring_painted_orders_of_replay

end
end SuperZeta.QuarticOrderedTurns
