import DottieDirectJointMomentRows

open QuarticModel QuarticModel.DottieFixedIntervals

set_option autoImplicit false

private def renderSharpRow (row : ℕ) (ticks : List (ℤ × ℤ)) : String :=
  "\t".intercalate (toString row :: ticks.flatMap fun p => [toString p.1,toString p.2])

/-- Emit exact integer candidates for consecutive, zero-based rows. -/
def main (args : List String) : IO Unit := do
  let [firstArg,stopArg] := args
    | throw (IO.userError "Expected FIRST STOP, with STOP exclusive")
  let some first := firstArg.toNat?
    | throw (IO.userError "FIRST must be a natural number")
  let some stop := stopArg.toNat?
    | throw (IO.userError "STOP must be a natural number")
  if first > stop || stop > dottiePrefixEnd.sqrt then
    throw (IO.userError "The requested range is outside the sharp prefix")
  let out ← IO.getStdout
  for row in [first:stop] do
    let ticks := dottieDirectJointMomentRow 11 dottiePrefixEnd row
    if ticks.length != 11 then
      throw (IO.userError s!"Unexpected number of columns at row {row}")
    out.putStrLn (renderSharpRow row ticks)
    out.flush
