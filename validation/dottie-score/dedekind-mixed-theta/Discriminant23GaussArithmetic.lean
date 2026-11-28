import Discriminant23GaussCoefficientData

namespace FieldTarget

open Finset

structure GaussPhaseTriple where
  plus : GaussianInt
  minus : GaussianInt
  inverse : GaussianInt
  deriving DecidableEq, Inhabited

def gaussPhaseSeed (m : ℤ) : GaussPhaseTriple :=
  ⟨gaussExpSeed (-1) 116 m, gaussExpSeed (-3) (-116) m, gaussExpSeed (-4) 0 m⟩

def gaussPhaseAdvance (step initial : GaussPhaseTriple) : GaussPhaseTriple :=
  ⟨gaussianFloorDiv (step.plus * initial.plus) gaussExpScale,
    gaussianFloorDiv (step.minus * initial.minus) gaussExpScale,
    gaussianFloorDiv (step.inverse * initial.inverse) gaussExpScale⟩

def gaussPhaseValues (p : ℕ) (i : Fin 24) : GaussPhaseTriple :=
  ⟨gaussPanelExpNumerator (-1) 116 p i, gaussPanelExpNumerator (-3) (-116) p i,
    gaussPanelExpNumerator (-4) 0 p i⟩

theorem gaussPhaseValues_zero (i : Fin 24) :
    gaussPhaseValues 0 i = gaussPhaseSeed (gauss24Pair i).1 := rfl

theorem gaussPhaseValues_succ (p : ℕ) (i : Fin 24) :
    gaussPhaseValues (p + 1) i = gaussPhaseAdvance (gaussPhaseSeed (10 ^ 30)) (gaussPhaseValues p i) := rfl

/-- Values kept between the seed, panel recurrence, heat and polynomial checks. -/
structure GaussPanelTrace where
  phases : GaussPhaseTriple
  expNode : ℤ
  heat : ℤ
  principal : ℤ
  other : ℤ
  deriving Inhabited

def GaussPanelTrace.approximation (t : GaussPanelTrace) : GaussPanelApproximation :=
  ⟨t.expNode, ⟨t.principal, 0⟩, ⟨t.other, 0⟩, t.phases.plus, t.phases.minus⟩

def GaussPanelTraceAgrees (initial : Fin 24 → GaussPhaseTriple) (step : GaussPhaseTriple)
    (trace : Fin 32 → Fin 24 → GaussPanelTrace) (p : Fin 32) (i : Fin 24) : Prop :=
  let t := trace p i
  t.phases = (if p.val = 0 then initial i
    else gaussPhaseAdvance step (trace ⟨p.val - 1, by omega⟩ i).phases) ∧
  t.expNode = (gaussExpScale : ℤ) * (gaussExpScale : ℤ) / t.phases.inverse.re.natAbs ∧
  t.heat = gaussHeatOfPositiveExp t.expNode ∧
  t.principal = gaussThetaOfHeat true t.heat ∧
  t.other = gaussThetaOfHeat false t.heat

instance (initial : Fin 24 → GaussPhaseTriple) (step : GaussPhaseTriple)
    (trace : Fin 32 → Fin 24 → GaussPanelTrace) (p : Fin 32) (i : Fin 24) :
    Decidable (GaussPanelTraceAgrees initial step trace p i) := by
  unfold GaussPanelTraceAgrees
  infer_instance

theorem gaussTraceApproximations_eq
    {initial : Fin 24 → GaussPhaseTriple} {step : GaussPhaseTriple}
    {trace : Fin 32 → Fin 24 → GaussPanelTrace}
    (hStart : ∀ i : Fin 24, initial i = gaussPhaseSeed (gauss24Pair i).1)
    (hStep : step = gaussPhaseSeed (10 ^ 30))
    (hCheck : ∀ (p : Fin 32) (i : Fin 24), GaussPanelTraceAgrees initial step trace p i)
    (p : Fin 32) (i : Fin 24) :
    (trace p i).approximation = gaussPanelApproximation p.val i := by
  have hPhase (j : ℕ) (hj : j < 32) :
      (trace ⟨j, hj⟩ i).phases = gaussPhaseValues j i := by
    induction j with
    | zero =>
      have h := (hCheck ⟨0, hj⟩ i).1
      change (trace ⟨0, hj⟩ i).phases = initial i at h
      simpa only [hStart i, gaussPhaseValues_zero] using h
    | succ j ih =>
      have hJ : j < 32 := by omega
      have h := (hCheck ⟨j + 1, hj⟩ i).1
      rw [ite_eq_right (Nat.succ_ne_zero j)] at h
      have hPrev : (⟨j + 1 - 1, by omega⟩ : Fin 32) = ⟨j, hJ⟩ := by
        apply Fin.ext
        change j + 1 - 1 = j
        omega
      rw [hPrev, ih hJ, hStep, ← gaussPhaseValues_succ] at h
      exact h
  have hP := hPhase p.val p.isLt
  have hExp := (hCheck p i).2.1
  rw [hP] at hExp
  simp only [gaussPhaseValues, ← gaussPanelPositiveExpNumerator_eq] at hExp
  have hHeat := (hCheck p i).2.2.1
  rw [hExp, ← gaussPanelHeatNumerator_eq] at hHeat
  have hPrincipal := (hCheck p i).2.2.2.1
  have hOther := (hCheck p i).2.2.2.2
  rw [hHeat] at hPrincipal hOther
  simp only [GaussPanelTrace.approximation, gaussPanelApproximation, hExp, hPrincipal, hOther,
    hP, gaussPhaseValues, gaussPanelThetaNumerator_eq]

def gaussTracedPanelCoefficientSum (trace : Fin 32 → Fin 24 → GaussPanelTrace)
    (b : ℤ) (p : Fin 32) (k : ℕ) : GaussianInt :=
  ∑ i : Fin 24,
    let t := trace p i
    let common := (gauss24Pair i).2 * gaussPanelMomentNumerator p.val i k * t.expNode *
      (t.principal + b * t.other)
    let sign := (-1 : ℤ) ^ k
    ⟨common * (t.phases.plus.re + sign * t.phases.minus.re),
      common * (t.phases.plus.im + sign * t.phases.minus.im)⟩

theorem gaussTracedPanelCoefficientSum_eq {trace : Fin 32 → Fin 24 → GaussPanelTrace}
    (h : ∀ (p : Fin 32) (i : Fin 24), (trace p i).approximation = gaussPanelApproximation p.val i)
    (b : ℤ) (p : Fin 32) (k : ℕ) :
    gaussTracedPanelCoefficientSum trace b p k = gaussPanelCoefficientSum b p.val k := by
  unfold gaussTracedPanelCoefficientSum gaussPanelCoefficientSum
  apply Finset.sum_congr rfl
  intro i _
  rw [← h p i]
  have hSign : (-1 : GaussianInt) ^ k = (((-1 : ℤ) ^ k : ℤ) : GaussianInt) := by
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  unfold gaussPanelCoefficientNumerator GaussPanelTrace.approximation
  rw [hSign]
  ext
  all_goals
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  all_goals ring

#print axioms gaussTraceApproximations_eq
#print axioms gaussTracedPanelCoefficientSum_eq

end FieldTarget
