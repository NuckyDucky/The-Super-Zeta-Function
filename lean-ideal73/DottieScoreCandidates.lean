import DottieSymmetricChunks

open QuarticModel

/-- Emit proposed exact block values for subsequent kernel certificate
generation. Each completed block gets its own newline-delimited record. -/
def main (args : List String) : IO Unit := do
  let options := if args.length = 4 then "standard" :: args else args
  let [scheme, path, startArg, stopArg, widthArg] := options
    | throw (IO.userError "expected standard, quick, or paired, output path, first row, row limit, block width")
  let weight ← match scheme with
    | "standard" => pure dottieWeightTicks
    | "quick" => pure dottieQuickWeightTicks
    | "paired" => pure dottieQuickWeightTicks
    | _ => throw (IO.userError "unknown weight method")
  let some start := startArg.toNat? | throw (IO.userError "invalid first row")
  let some stop := stopArg.toNat? | throw (IO.userError "invalid row limit")
  let some width := widthArg.toNat? | throw (IO.userError "invalid block width")
  let cutoff := 276824064
  if start = 0 || stop ≤ start || stop > cutoff.sqrt + 1 || width = 0 then
    throw (IO.userError "invalid row bounds or block width")
  IO.FS.withFile path .append fun output => do
    for a in [start:stop] do
      let paired := scheme = "paired"
      let len := if paired then dottiePairRowSize cutoff (a-1) else dottieReferenceRowSize a
      let score := if paired then dottiePairRowBlock weight (a-1) else dottieRowChunk weight a
      if paired then
        -- A record with length zero carries that row's axis and diagonal contribution.
        output.putStrLn s!"{a},0,0,{dottiePairRowHead cutoff weight (a-1)}"
      let full := len/width
      for k in [:full] do
        let lo := k*width
        let value := score lo width
        output.putStrLn s!"{a},{lo},{width},{value}"
      let rem := len%width
      if rem > 0 then
        let lo := full*width
        let value := score lo rem
        output.putStrLn s!"{a},{lo},{rem},{value}"
      output.flush
