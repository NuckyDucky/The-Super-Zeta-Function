import DottieQuickScore

open QuarticModel

/-- Emit proposed exact block values for subsequent kernel certificate
generation. Each completed block gets its own newline-delimited record. -/
def main (args : List String) : IO Unit := do
  let options := if args.length = 4 then "standard" :: args else args
  let [scheme, path, startArg, stopArg, widthArg] := options
    | throw (IO.userError "expected standard or quick, output path, first row, row limit, block width")
  let weight ← match scheme with
    | "standard" => pure dottieWeightTicks
    | "quick" => pure dottieQuickWeightTicks
    | _ => throw (IO.userError "unknown weight method")
  let some start := startArg.toNat? | throw (IO.userError "invalid first row")
  let some stop := stopArg.toNat? | throw (IO.userError "invalid row limit")
  let some width := widthArg.toNat? | throw (IO.userError "invalid block width")
  let cutoff := 276824064
  if start = 0 || stop ≤ start || stop > cutoff.sqrt + 1 || width = 0 then
    throw (IO.userError "invalid row bounds or block width")
  IO.FS.withFile path .append fun output => do
    for a in [start:stop] do
      let len := dottieReferenceRowSize a
      let full := len/width
      for k in [:full] do
        let lo := k*width
        let value := dottieRowChunk weight a lo width
        output.putStrLn s!"{a},{lo},{width},{value}"
      let rem := len%width
      if rem > 0 then
        let lo := full*width
        let value := dottieRowChunk weight a lo rem
        output.putStrLn s!"{a},{lo},{rem},{value}"
      output.flush
