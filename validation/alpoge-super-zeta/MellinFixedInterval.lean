/-! Directed fixed-point intervals used by the Mellin sample checker. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

def scale : Int := 10^24

structure Box where
  lo : Int
  hi : Int
  deriving DecidableEq, Repr

def ceilDiv (n d : Int) : Int := -((-n)/d)

def fromRatio (n d : Int) : Box := ⟨(n*scale)/d, ceilDiv (n*scale) d⟩

def constant (n : Int) : Box := ⟨n*scale, n*scale⟩

def add (a b : Box) : Box := ⟨a.lo+b.lo, a.hi+b.hi⟩

def neg (a : Box) : Box := ⟨-a.hi, -a.lo⟩

def sub (a b : Box) : Box := add a (neg b)

def widen (a : Box) (units : Nat) : Box := ⟨a.lo-(units:Int), a.hi+(units:Int)⟩

def divInt (a : Box) (d : Int) : Box := ⟨a.lo/d, ceilDiv a.hi d⟩

def mul (a b : Box) : Box :=
  let ll := a.lo*b.lo
  let lh := a.lo*b.hi
  let hl := a.hi*b.lo
  let hh := a.hi*b.hi
  ⟨min (min ll lh) (min hl hh) / scale, ceilDiv (max (max ll lh) (max hl hh)) scale⟩

/-- Enclose the quotient when the numerator is nonnegative and the denominator is positive. -/
def divPositive (a b : Box) : Box :=
  ⟨(a.lo*scale)/b.hi, ceilDiv (a.hi*scale) b.lo⟩

def nonnegative (a : Box) : Box := ⟨max 0 a.lo, a.hi⟩

def horner (x : Box) : List Box → Box
  | [] => constant 0
  | a::as => add a (mul x (horner x as))

def coefficients (f : Nat → Box) (start : Nat) : Nat → List Box
  | 0 => []
  | n+1 => f start :: coefficients f (start+1) n

def squareSteps : Nat → Box → Box
  | 0, a => a
  | n+1, a => let r := squareSteps n a; mul r r

/-- On the same decimal grid as the stored quadrature sample. -/
def fitsSample (a : Box) (target : Int) : Bool :=
  decide ((target-1)*10^10 ≤ a.lo ∧ a.hi ≤ (target+1)*10^10)

end DottieOriented.NativeSpectrum.MellinFixed
