import DottieFixedCircle
import DottieSharpFactoredArcs

/-! Executable circle enclosure definitions. The archive replay uses
these definitions directly and can run before their analytic proofs. -/

namespace QuarticModel.DottieFixedIntervals

open Complex SuperZeta.StirlingCorrection
set_option autoImplicit false

def shiftBox : Interval := Interval.rational (1/512) (1/512)

def slopeBox : Rect :=
  ⟨Interval.rational 43.45042342189746392492 43.45042342189746392492,
    Interval.rational 1.57079632679489661923 1.57079632679489661923⟩

def reflectedBoxHorner (v : Rect) (xSquared : Interval) : ℕ → (ℕ → Rect) → Rect × Rect
  | 0, _ => (Rect.zero,Rect.zero)
  | n+1, f =>
    let p := reflectedBoxHorner v xSquared n (fun k => f (k+1))
    (((f 0).add (v.mul p.1)).add (xSquared.scaleBy p.2),p.1.add (v.mul p.2))

def referenceProjectionBox (reference : ℕ → Rect) : Interval :=
  let P := ((imaginaryBox shiftBox.neg).horner 17 reference).pad (3/10^30)
  (circleUnitBox.mul P).re

def fixedReferenceUpper (reference : ℕ → Rect) : ℤ := (referenceProjectionBox reference).absTicks

def fixedFactoredReading (sharp : ℕ → Rect) (xb yb : Interval) : Interval :=
  let p := reflectedBoxHorner (imaginaryBox (yb.sub shiftBox)) (xb.mul xb) 17 sharp
  let z := xb.scaleBy slopeBox
  let projection := (circleUnitBox.mul ((slopeBox.mul (imaginaryBox yb)).expBox)).mul
    ((z.coshBox.mul p.2).add ((slopeBox.dividedSinhBox z).mul p.1))
  let odd := xb.scaleBy p.2
  let mass := ((p.1.add odd).normUpperTicks + (p.1.sub odd).normUpperTicks)
  let tail := ((Interval.rational (18/10^12) (18/10^12)).mul ⟨0,mass⟩).add
    (Interval.rational (18/10^11) (18/10^11))
  projection.im.add (tail.mul ((xb.add xb).inv))

def fixedArcQuadrant (a : DottieSharpFactoredArc) : ℕ := ⌊4*a.lo⌋.toNat

def fixedArcPass (sharp : ℕ → Rect) (refTicks : ℤ) (a : DottieSharpFactoredArc) : Bool :=
  let q := fixedArcQuadrant a
  let trig := circleTrigBox q a.lo a.hi
  let xb := circleXBox trig
  let yb := circleYBox trig
  decide (q < 4 ∧ (q:ℚ)/4 ≤ a.lo ∧ a.hi ≤ ((q:ℚ)+1)/4 ∧
    (quarterArgBox q a.lo).normUpperTicks ≤ 2*scale ∧ (quarterArgBox q a.hi).normUpperTicks ≤ 2*scale ∧
    0 < (xb.add xb).lo ∧ (xb.scaleBy slopeBox).normUpperTicks ≤ 2*scale ∧
    (slopeBox.mul (imaginaryBox yb)).normUpperTicks ≤ 2*scale ∧
    (fixedFactoredReading sharp xb yb).hi*scale ≤ -a.lowerTicks*refTicks)

end QuarticModel.DottieFixedIntervals
