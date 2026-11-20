import SuperZeta.Hasse
import SuperZeta.Multiplicity
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum.Prime

/-! Prime-power weights and splitting tests for the two fields in the proof.
The variable t stands for p^{-w} in a single Euler factor. -/
namespace SuperZeta.FieldWeights

/-- Weight at exponent m in the sum of the ordinary and marked prime readings.
Use b = 1/7 for the normalized detector and b = 1 for the quadratic field. -/
def primePowerWeight (b c : ℝ) (m : ℕ) : ℝ := 1 + b * c ^ m

/-- Partial fractions give the coefficients at every positive power of t. -/
theorem primePower_generating_function (b c t : ℝ) (ht : |t| < 1)
    (hct : |c*t| < 1) :
    HasSum (fun k : ℕ => primePowerWeight b c (k + 1) * t ^ (k + 1))
      (t / (1-t) + b*(c*t) / (1-c*t)) := by
  have h := ((hasSum_geometric_of_abs_lt_one ht).mul_left t).add
    ((hasSum_geometric_of_abs_lt_one hct).mul_left (b*(c*t)))
  simpa only [div_eq_mul_inv] using h.congr_fun (fun k => by
    dsimp [primePowerWeight]
    rw [mul_pow, pow_succ, pow_succ]
    ring)

/-- The two arithmetic readings use the same character at every prime power.
Multiplicity seven gives the one-seventh coefficient. -/
theorem detector_to_field (c : ℝ) (m : ℕ) :
    7 * primePowerWeight (1/7) c m - 6 = primePowerWeight 1 c m := by
  unfold primePowerWeight
  ring

/-- The logarithmic derivative of the field Euler factor has weights 2 above
a split prime, alternating 0 and 2 above an inert prime, and 1 above a ramified prime. -/
theorem field_cases (k : ℕ) :
    primePowerWeight 1 1 (k+1) = 2 ∧
    primePowerWeight 1 (-1) (2*k+1) = 0 ∧
    primePowerWeight 1 (-1) (2*k+2) = 2 ∧ primePowerWeight 1 0 (k+1) = 1 := by
  norm_num [primePowerWeight, pow_add, pow_mul]

/-- For the Eisenstein field the character is the actual quadratic character
modulo three. Its value at a prime power recovers the same coefficient. -/
theorem mod_three_prime_power (p m : ℕ) :
    primePowerWeight 1 (legendreSym 3 p : ℝ) m =
      1 + (legendreSym 3 ((p : ℤ)^m) : ℝ) := by
  have h : legendreSym 3 ((p : ℤ)^m) = (legendreSym 3 p)^m := by
    induction m with
    | zero => simp
    | succ m ih => simp only [pow_succ, legendreSym.mul, ih]
  simp [primePowerWeight, h]

/-- The sign on the two invertible classes modulo three, with complex values
so it can be supplied to Mathlib's analytically continued L-function. -/
noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

theorem chiMinusThree_apply (n : ℤ) :
    chiMinusThree n = (legendreSym 3 n : ℂ) := rfl

open scoped Topology in
theorem analytic_angular_factor {w : ℂ} (hw : w ≠ 1) :
    AnalyticAt ℂ chiMinusThree.LFunction w := by
  have h : DifferentiableOn ℂ chiMinusThree.LFunction ({1}ᶜ : Set ℂ) := fun z hz =>
    (chiMinusThree.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt
  exact h.analyticAt (isOpen_compl_singleton.mem_nhds hw)

/-- For the actual two analytic functions at the same input, coincident
zeros contribute both multiplicities. The detector counts each zeta zero
seven times, the arithmetic product counts it once. Identification of the
latter product with the Dedekind zeta function uses the field factorization. -/
theorem factor_orders {w : ℂ} (hw : w ≠ 1) :
    let hZ := Multiplicity.analytic_zeta hw
    let hL := analytic_angular_factor hw
    (hZ.mul hL).order = hZ.order + hL.order ∧
      ((hZ.pow 7).mul hL).order = 7 • hZ.order + hL.order := by
  let hZ := Multiplicity.analytic_zeta hw
  let hL := analytic_angular_factor hw
  exact ⟨hZ.order_mul hL, ((hZ.pow 7).order_mul hL).trans
    (congrArg (fun a => a+hL.order) hZ.order_pow)⟩

/-- The Gaussian quadratic A+2iN after reducing i to the residue r. -/
def branch {K : Type*} [CommRing K] (r x : K) : K :=
  (310+930*r)*(x*x) + (-579-366*r)*x + (277-1318*r)

def branchDisc {K : Type*} [CommRing K] (r : K) : K := -5045155 + 1027708*r

/-- The two signs of the reduction of i recover the original six-coefficient quartic. -/
theorem branch_product {K : Type*} [CommRing K] {r : K} (hr : r^2 = -1) (x : K) :
    branch r x * branch (-r) x = Hasse.quartic x 1 := by
  unfold branch Hasse.quartic
  linear_combination -(930*x^2-366*x-1318)^2 * hr

theorem branch_discriminant {K : Type*} [CommRing K] {r : K} (hr : r^2 = -1) :
    discrim (310+930*r) (-579-366*r) (277-1318*r) = branchDisc r := by
  unfold discrim branchDisc
  linear_combination 5036916 * hr

/-- For each admissible residue of i the branch has a root exactly when the
specialized discriminant is square. Both sides come from the original coefficients. -/
theorem branch_root_iff {K : Type*} [Field K] [NeZero (2 : K)] {r : K}
    (hr : r^2 = -1) (ha : 310+930*r ≠ 0) :
    (∃ x, branch r x = 0) ↔ IsSquare (branchDisc r) := by
  rw [← branch_discriminant hr]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨_, by simpa only [sq] using discrim_eq_sq_of_quadratic_eq_zero hx⟩
  · exact exists_quadratic_eq_zero ha

/-- Direct finite enumeration on the branch quadratic, in each labelled residue field. -/
noncomputable def rootCount (p : ℕ) [NeZero p] (r : ZMod p) : ℕ :=
  (Finset.univ.filter (fun x : ZMod p => branch r x = 0)).card

/-- Reducing a labelled Gaussian generator m+n i at a prime dividing its
norm determines a *unique* image of i. The residue is read from the
generator before evaluating the branch polynomial or its discriminant. -/
theorem residue_from_generator {K : Type*} [Field K] {m n : K}
    (hn : n ≠ 0) (hnorm : m^2+n^2 = 0) :
    ∃! r, r^2 = -1 ∧ m+n*r = 0 := by
  refine ⟨-m/n, ⟨?_, ?_⟩, ?_⟩
  · field_simp
    linear_combination hnorm
  · field_simp
    ring
  · intro z hz
    apply (eq_div_iff hn).mpr
    linear_combination hz.2

/-- Multiplication of a Gaussian generator by i preserves its residue
condition. Conjugation carries the generator to the opposite residue. -/
theorem mark_symmetries {K : Type*} [CommRing K] {m n r : K}
    (hr : r^2 = -1) (hm : m+n*r = 0) :
    -n + m*r = 0 ∧ m+(-n)*(-r) = 0 := by
  constructor
  · linear_combination r*hm - n*hr
  · simpa using hm

theorem root_counts_13 : rootCount 13 5 = 0 ∧ rootCount 13 8 = 0 := by decide
theorem root_counts_37 : rootCount 37 6 = 2 ∧ rootCount 37 31 = 2 := by decide
theorem root_counts_73 : rootCount 73 27 = 0 ∧ rootCount 73 46 = 2 := by decide

theorem gaussian_marks_73 :
    ((27 : ZMod 73)^2 = -1 ∧ 3+8*(27 : ZMod 73) = 0) ∧
    ((46 : ZMod 73)^2 = -1 ∧ 3-8*(46 : ZMod 73) = 0) ∧
    branchDisc (27 : ZMod 73) = 34 ∧ branchDisc (46 : ZMod 73) = 8 := by decide

/-- Any prediction made from the rational norm alone fails on at least one
of the two marked branches above 73. The predicted sign is compared with
the independent root count minus one. -/
theorem norm_only_fails (predict : ℕ → ℤ) :
    ¬ (predict 73 = (rootCount 73 27 : ℤ)-1 ∧
       predict 73 = (rootCount 73 46 : ℤ)-1) := by
  rw [root_counts_73.1, root_counts_73.2]
  omega

/-- Conjugating the mark need not negate the splitting sign. -/
theorem conjugation_can_preserve_sign :
    (rootCount 13 5 : ℤ)-1 = -1 ∧ (rootCount 13 8 : ℤ)-1 = -1 ∧
    (rootCount 37 6 : ℤ)-1 = 1 ∧ (rootCount 37 31 : ℤ)-1 = 1 := by
  rw [root_counts_13.1, root_counts_13.2, root_counts_37.1, root_counts_37.2]
  decide

/-- At a labelled Gaussian reduction, multiplying the readings of a vector
and its conjugate gives a single Legendre symbol of the rational norm. -/
theorem conjugate_legendre_product (p : ℕ) [Fact p.Prime] (r m n : ℤ)
    (hr : (r : ZMod p)^2 = -1) :
    legendreSym p (m+n*r) * legendreSym p (m+(-n)*r) =
      legendreSym p (m^2+n^2) := by
  rw [← legendreSym.mul]
  unfold legendreSym
  congr 1
  push_cast
  linear_combination -(n : ZMod p)^2 * hr

section Conductor
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

/-- The three reductions used in the reading annihilate the quartic branch
discriminant. Their distinct rational primes multiply to its norm. -/
theorem conductor_reductions :
    (32 : ZMod 41)^2 = -1 ∧ branchDisc (32 : ZMod 41) = 0 ∧
    (109 : ZMod 457)^2 = -1 ∧ branchDisc (109 : ZMod 457) = 0 ∧
    (516876951 : ZMod 1414835497)^2 = -1 ∧
    branchDisc (516876951 : ZMod 1414835497) = 0 ∧
    ((-5045155 : ℤ)^2 + 1027708^2 = 41*457*1414835497) := by decide

/-- The explicit product on coordinates of a Gaussian generator. -/
noncomputable def conductorReading (m n : ℤ) : ℤ :=
  legendreSym 41 (m+n*32) * legendreSym 457 (m+n*109) *
    legendreSym 1414835497 (m+n*516876951)

/-- This identity includes zero values on nonunits. Identification of the
explicit reading with the relative Hecke character uses quadratic reciprocity. -/
theorem conductor_norm_product (m n : ℤ) :
    conductorReading m n * conductorReading m (-n) =
      legendreSym 41 (m^2+n^2) * legendreSym 457 (m^2+n^2) *
      legendreSym 1414835497 (m^2+n^2) := by
  obtain ⟨h₁, _, h₂, _, h₃, _⟩ := conductor_reductions
  rw [← conjugate_legendre_product 41 32 m n (by exact h₁),
      ← conjugate_legendre_product 457 109 m n (by exact h₂),
      ← conjugate_legendre_product 1414835497 516876951 m n (by exact h₃)]
  unfold conductorReading
  ring
end Conductor

end SuperZeta.FieldWeights
