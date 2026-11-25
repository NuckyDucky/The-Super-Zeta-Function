import MellinFixedFunctions
import Mathlib.Data.Nat.Choose.Basic

/-! Integer enclosures for the two finite eta readings at the original center. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

structure EtaBounds where
  valueRe : Box
  valueIm : Box
  slopeRe : Box
  slopeIm : Box

def addEta (p q : EtaBounds) : EtaBounds :=
  ⟨add p.valueRe q.valueRe, add p.valueIm q.valueIm,
    add p.slopeRe q.slopeRe, add p.slopeIm q.slopeIm⟩

def scaleEta (w : Box) (p : EtaBounds) : EtaBounds :=
  ⟨mul w p.valueRe, mul w p.valueIm, mul w p.slopeRe, mul w p.slopeIm⟩

def zeroEta : EtaBounds := ⟨constant 0, constant 0, constant 0, constant 0⟩

def logTwoBox : Box := neg (logGapFixed (fromRatio 1 3))

def binaryExponent128 (n : Nat) : Nat :=
  [2,4,8,16,32,64,128].countP (fun cutoff => decide (cutoff ≤ n))

def logRatioBox (n : Nat) : Box :=
  let dyadic : Int := ↑((2:Nat)^binaryExponent128 n)
  fromRatio ((n:Int)-dyadic) ((n:Int)+dyadic)

def logNaturalBox (n : Nat) : Box :=
  add (mul (constant ↑(binaryExponent128 n)) logTwoBox) (neg (logGapFixed (logRatioBox n)))

def etaBasis (j : Nat) : Option EtaBounds :=
  let n := j+1
  let ℓ := logNaturalBox n
  let phase := mul (fromRatio 7067363 500000) ℓ
  if inLogDomain (logRatioBox n) && inUnit (divInt (reducedPhase phase) 4) then
    let amp := expFixed (divInt (neg ℓ) 2)
    let cs := cosSinFixed phase
    let realPart := mul amp cs.1
    let imagPart := neg (mul amp cs.2)
    let slope := mul (constant (-2)) ℓ
    some ⟨realPart, imagPart, mul slope realPart, mul slope imagPart⟩
  else none

def binomial128 (j : Nat) : Nat := (128:Nat).descFactorial j / j.factorial

def signedWeight128 (j tally : Nat) : Box :=
  fromRatio ((-1:Int)^j*((2:Int)^128-(tally:Int))) ((2:Int)^128)

def etaColumns (j tally : Nat) : Nat → Option EtaBounds
  | 0 => some zeroEta
  | count+1 =>
    let total := tally+binomial128 j
    match etaBasis j, etaColumns (j+1) total count with
    | some current, some rest => some (addEta (scaleEta (signedWeight128 j total) current) rest)
    | _, _ => none

def inside (b : Box) (lo hi : Int) : Bool := decide (lo ≤ b.lo ∧ b.hi ≤ hi)

def etaReadingCheck (r : Option EtaBounds) : Bool :=
  match r with
  | none => false
  | some a =>
    inside a.valueRe (-10^18) (10^18) &&
      inside a.valueIm (-2*10^18) (2*10^18) &&
      inside a.slopeRe (149*(scale/40)) (151*(scale/40)) &&
      inside a.slopeIm (-11*(scale/40)) (-9*(scale/40))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 12000000 in
theorem etaCenterCheck_passes : etaReadingCheck (etaColumns 0 0 128) = true := by
  decide +kernel

#print axioms etaCenterCheck_passes

end DottieOriented.NativeSpectrum.MellinFixed
