import SuperZeta.QuarterLine.QuarterOriginalUnivalent

/-! The marked turn, the squared spectrum, and pointwise recovery in the
actual super-zeta coordinate. No sign or nonvanishing hypothesis on a
transported reading is required. -/
namespace SuperZeta.QuarticTurn
noncomputable section
open UnitSpectrum QuarterOriginalUnivalent

/-- On coefficients of a*u + b*v, the arithmetic substitution
u ↦ v, v ↦ -u with conjugation on coefficients has this action.
In complex-pair coordinates for a + b*j it is left multiplication by j. -/
def jTurn (p : ℂ × ℂ) : ℂ × ℂ := (-star p.2, star p.1)

theorem twice_jTurn (p : ℂ × ℂ) : jTurn (jTurn p) = -p := by
  rcases p with ⟨a,b⟩
  simp [jTurn]

theorem four_jTurns (p : ℂ × ℂ) :
    jTurn (jTurn (jTurn (jTurn p))) = p := by simp only [twice_jTurn, neg_neg]

/-- The two signs mark the real and imaginary coordinates of a quartet.
This choice orients the quartet by taking (+,+) to (-,+). -/
def turn (p : Bool × Bool) : Bool × Bool := (!p.2, p.1)

def markedRoot (z : ℂ) (p : Bool × Bool) : ℂ :=
  ⟨if p.1 then z.re else -z.re, if p.2 then z.im else -z.im⟩

theorem four_turns (p : Bool × Bool) : turn (turn (turn (turn p))) = p := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem half_turn (z : ℂ) (p : Bool × Bool) :
    markedRoot z (turn (turn p)) = -markedRoot z p := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> apply Complex.ext <;> simp [turn, markedRoot]

theorem square_turn (z : ℂ) (p : Bool × Bool) :
    markedRoot z (turn p) ^ 2 = star (markedRoot z p ^ 2) := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [turn, markedRoot, pow_two, Complex.mul_re, Complex.mul_im]

def swapSquares : Unit ⊕ (ℕ ⊕ ℕ) ≃ Unit ⊕ (ℕ ⊕ ℕ) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumComm ℕ ℕ)

theorem actual_square_turn (k : Unit ⊕ (ℕ ⊕ ℕ)) :
    squaredRoot (swapSquares k) = star (squaredRoot k) := by
  rcases k with k | (k | k) <;> simp [squaredRoot, RootBounds.family, swapSquares]

/-- On every numbered level, squaring the turned marked root gives
exactly the other branch in the project's original squaredRoot list. -/
theorem marked_to_other_square (n : ℕ) :
    markedRoot (RootBounds.u (levelHeight n)) (turn (true, true)) ^ 2 =
      squaredRoot (Sum.inr (Sum.inr n)) := by
  rw [square_turn]
  rfl

theorem actual_sum_after_turn {s : ℂ} (hl : 1/2 < s.re) (hu : s.re < 1) :
    HasSum (fun k => (squaredRoot (swapSquares k)) ^ (-s)) (continuation s) :=
  swapSquares.hasSum_iff.mpr (root_hasSum hl hu)

/-- w is the input before passing to s = w/2. The permitted inputs are
exactly those covered by continuation_injective. -/
abbrev Input := {w : ℂ // w/2 ∈ strip}

def address (w : Input) : ℂ := continuation (w.val / 2)

def chart : Input ≃ Set.range address :=
  Equiv.ofInjective address (by
    intro x y h
    apply Subtype.ext
    have hhalf := continuation_injective x.property y.property h
    calc
      x.val = x.val / 2 * 2 := by ring
      _ = y.val / 2 * 2 := congrArg (fun z : ℂ => z * 2) hhalf
      _ = y.val := by ring)

theorem same_input (w : Input) : chart.symm (chart w) = w := chart.symm_apply_apply w

theorem same_address (ξ : Set.range address) : chart (chart.symm ξ) = ξ :=
  chart.apply_symm_apply ξ

/-- Change the coordinate of the independent variable in any marked
reading. The inverse reads it back at the original input. -/
def inChart {V : Type*} (f : Input → V) (ξ : Set.range address) : V := f (chart.symm ξ)

theorem same_reading {V : Type*} (f : Input → V) (w : Input) :
    inChart f (chart w) = f w := congrArg f (same_input w)

theorem j_commutes_with_chart (f : Input → ℂ × ℂ) (ξ : Set.range address) :
    inChart (fun w => jTurn (f w)) ξ = jTurn (inChart f ξ) := rfl

theorem recover_ordered_classes (A B : Input → ℂ) (w : Input) :
    let q := inChart (fun t => (A t - B t, A t + B t)) (chart w)
    ((q.2 + q.1)/2, (q.2 - q.1)/2) = (A w, B w) := by
  dsimp only
  rw [same_reading]
  apply Prod.ext <;> dsimp <;> ring

/-- The coordinates after right multiplication by 1+j. -/
def classSwap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 - p.2, p.1 + p.2)

/-- Left multiplication by j commutes with the change from the two
class readings to their difference and total. -/
theorem j_commutes_with_classSwap (p : ℂ × ℂ) :
    jTurn (classSwap p) = classSwap (jTurn p) := by
  rcases p with ⟨a, b⟩
  apply Prod.ext <;> simp [classSwap, jTurn] <;> ring

/-- The zero set of the Gaussian component at the original inputs is
carried exactly to the zero set of the j coefficient at their addresses.
Both functions are supplied as readings. -/
theorem gaussian_zero_set_after_j (G D : Input → ℂ) :
    chart '' {w | G w = 0} =
      {ξ | (jTurn (inChart (fun t => (G t, D t)) ξ)).2 = 0} := by
  ext ξ
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (jTurn (inChart (fun t => (G t, D t)) (chart w))).2 = 0
    rw [same_reading]
    change star (G w) = 0
    simpa using hw
  · intro h
    refine ⟨chart.symm ξ, ?_, chart.apply_symm_apply ξ⟩
    change star (G (chart.symm ξ)) = 0 at h
    simpa using h

/-- Starting at any Gaussian zero, the total is free. These are the
four successive turns, including the return to the original pair. -/
theorem orbit_at_gaussian_zero (d : ℂ) :
    jTurn (0, d) = (-star d, 0) ∧
    jTurn (-star d, 0) = (0, -d) ∧
    jTurn (0, -d) = (star d, 0) ∧
    jTurn (star d, 0) = (0, d) := by
  simp [jTurn]

end
end SuperZeta.QuarticTurn

#print axioms SuperZeta.QuarticTurn.four_jTurns
#print axioms SuperZeta.QuarticTurn.four_turns
#print axioms SuperZeta.QuarticTurn.square_turn
#print axioms SuperZeta.QuarticTurn.marked_to_other_square
#print axioms SuperZeta.QuarticTurn.actual_sum_after_turn
#print axioms SuperZeta.QuarticTurn.same_reading
#print axioms SuperZeta.QuarticTurn.recover_ordered_classes
#print axioms SuperZeta.QuarticTurn.j_commutes_with_classSwap
#print axioms SuperZeta.QuarticTurn.gaussian_zero_set_after_j
#print axioms SuperZeta.QuarticTurn.orbit_at_gaussian_zero
