import FieldCoefficientTransfer

/-! The two class sums at one input, in the Formal Conjectures formulation for
the quartic field. The height is free, so the Dottie height is a specialization.
The analytic identification of the product and the two class identities are
explicit hypotheses. -/

namespace QuarticRingMidpoint

open ArtinPrimitiveRootsConjecture FieldCoefficientTransfer

noncomputable section

/-- Use the same open annulus as the spectral package, at a supplied height. -/
def rightRing (T : ℝ) : Set ℂ :=
  {w | let d := ‖w - (⟨33 / 64, T - 1 / 512⟩ : ℂ)‖
       (30 / 2048 : ℝ) < d ∧ d < (31 / 2048 : ℝ)}

theorem rightRing_in_right_strip {T : ℝ} {w : ℂ} (hw : w ∈ rightRing T) :
    1 / 2 < w.re ∧ w.re < 1 := by
  have hout : ‖w - (⟨33 / 64, T - 1 / 512⟩ : ℂ)‖ < (31 / 2048 : ℝ) := hw.2
  have hb := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hout)
  change -(31 / 2048 : ℝ) < w.re - 33 / 64 ∧ w.re - 33 / 64 < 31 / 2048 at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Either class reading hitting half the total detects the same Gaussian zero. -/
theorem zero_iff_either_midpoint {G Z₀ Z₂ D : ℂ → ℂ} {w : ℂ}
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) :
    G w = 0 ↔ Z₀ w = D w / 2 ∨ Z₂ w = D w / 2 := by
  rw [hG, sub_eq_zero, hD]
  constructor
  · intro he
    left
    rw [he]
    ring
  · rintro (h | h)
    · linear_combination 2 * h
    · linear_combination -2 * h

/-- In the quartic application B is the character of discriminant
26509772707289 and AB is its product with the beta character. -/
def dirichletExpression {q r : ℕ} [NeZero q] [NeZero r] (B : DirichletCharacter ℂ q)
    (AB : DirichletCharacter ℂ r) (w : ℂ) : ℂ :=
  riemannZeta w * AB.LFunction w + chi4.LFunction w * B.LFunction w

/-- The two differences from one quarter of the unscaled Dirichlet
expression are exactly half the signed Gaussian value and its negative. -/
theorem differences_from_quarter {q r : ℕ} [NeZero q] [NeZero r] {B : DirichletCharacter ℂ q}
    {AB : DirichletCharacter ℂ r} {G Z₀ Z₂ : ℂ → ℂ} {w : ℂ}
    (hG : G w = Z₀ w - Z₂ w)
    (heven : Z₀ w + Z₂ w = dirichletExpression B AB w / 2) :
    Z₀ w - dirichletExpression B AB w / 4 = G w / 2 ∧
    Z₂ w - dirichletExpression B AB w / 4 = -(G w / 2) := by
  rw [hG]
  constructor <;> linear_combination heven / 2

/-- A single midpoint hit supplies an off-line zero of the admissible product,
and therefore a counterexample to the field statement. -/
theorem midpoint_refutes_quarticRH {T : ℝ} {w : ℂ} (hw : w ∈ rightRing T)
    {G Z₀ Z₂ D : ℂ → ℂ}
    (hP : IsDedekindZeta QuarticModel.K (fun s => riemannZeta s * chi4.LFunction s * G s))
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w)
    (hit : Z₀ w = D w / 2 ∨ Z₂ w = D w / 2) : ¬ DedekindZetaRH QuarticModel.K := by
  intro erh
  obtain ⟨hr, h1⟩ := rightRing_in_right_strip hw
  have hz := (zero_iff_either_midpoint hG hD).mpr hit
  exact (ne_of_gt hr) (erh _ hP w (by linarith) h1 (by simp [hz]))

/-- If the two rational factors are nonzero at w, every admissible field
continuation detects exactly the same midpoint hit at w. -/
theorem field_zero_iff_either_midpoint {T : ℝ} {w : ℂ} (hw : w ∈ rightRing T)
    {Z G Z₀ Z₂ D : ℂ → ℂ} (hZ : IsDedekindZeta QuarticModel.K Z)
    (hP : IsDedekindZeta QuarticModel.K (fun s => riemannZeta s * chi4.LFunction s * G s))
    (hζ : riemannZeta w ≠ 0) (hβ : chi4.LFunction w ≠ 0)
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) :
    Z w = 0 ↔ Z₀ w = D w / 2 ∨ Z₂ w = D w / 2 := by
  have h1 := (rightRing_in_right_strip hw).2
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact lt_irrefl 1 h1
  have he := FieldTarget.continuation_eq_off_one hZ hP hw1
  change Z w = riemannZeta w * chi4.LFunction w * G w at he
  rw [he, ← zero_iff_either_midpoint hG hD]
  simp [mul_eq_zero, hζ, hβ]

end
end QuarticRingMidpoint
