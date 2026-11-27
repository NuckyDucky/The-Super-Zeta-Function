import DottieFastReferenceScore

namespace QuarticModel

open private cosHornerTicks cosStep from DottieFixedCos
open private referenceAngleNumerator referenceQuarterDenominator referenceCosineTicks
  from DottieFastReferenceScore

set_option autoImplicit false

private def calcCosineTicks (scale square : ℕ) (divisors : List ℕ) : ℕ :=
  divisors.foldl (fun t d => scale - t * square / d) 0

private theorem cosHornerTicks_eq_fold (scale aSq bSq terms i : ℕ) :
    cosHornerTicks scale aSq bSq terms i =
      calcCosineTicks scale aSq ((List.range' i terms).reverse.map fun j => bSq * cosStep j) := by
  induction terms generalizing i with
  | zero => rfl
  | succ terms ih =>
    simp only [cosHornerTicks, List.range'_succ, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, calcCosineTicks, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih]

private def referenceCosineDivisors : List ℕ := [
  29308977219060124416103386894249663136708385711761391616000000000000000000000000000000000000000000000000000000000000,
  22987433112988332875375205407254637754281086832754032640000000000000000000000000000000000000000000000000000000000000,
  17432136777349485763826197433834766963663157514838474752000000000000000000000000000000000000000000000000000000000000,
  12643088212143583081456362973990050764854597758014717952000000000000000000000000000000000000000000000000000000000000,
  8620287417370624828265702027720489157855407562282762240000000000000000000000000000000000000000000000000000000000000,
  5363734393030611004254214595026082142665586927642607616000000000000000000000000000000000000000000000000000000000000,
  2873429139123541609421900675906829719285135854094254080000000000000000000000000000000000000000000000000000000000000,
  1149371655649416643768760270362731887714054341637701632000000000000000000000000000000000000000000000000000000000000,
  191561942608236107294793378393788647952342390272950272000000000000000000000000000000000000000000000000000000000000]

private theorem referenceCosineDivisors_eq :
    referenceCosineDivisors =
      ((List.range' 0 9).reverse.map fun i => referenceQuarterDenominator ^ 2 * cosStep i) := by
  decide +kernel

private def cachedReferenceCosineTicks (n : ℕ) : ℤ :=
  let c := (calcCosineTicks fixedCosScale ((referenceAngleNumerator n).natAbs ^ 2)
    referenceCosineDivisors : ℤ) - 3
  let scale : ℤ := fixedCosScale
  8*c^4 - 8*scale^2*c^2 + scale^4

private theorem cachedReferenceCosineTicks_eq (n : ℕ) :
    cachedReferenceCosineTicks n = referenceCosineTicks n := by
  simp only [cachedReferenceCosineTicks, referenceCosineTicks, fixedCosBounds,
    referenceCosineDivisors_eq, ← cosHornerTicks_eq_fold]

/-- Reuse the checked divisors of the nine fixed-point cosine steps. -/
def dottieCachedReferenceWeight (n : ℕ) : ℤ :=
  if n ≤ 276824064 then (inverseSqrtTicks (2^64) n : ℤ) * cachedReferenceCosineTicks n
  else dottieDirectReferenceWeight n

theorem dottie_cached_reference_weight_eq (n : ℕ) :
    dottieCachedReferenceWeight n = dottieFastReferenceWeight n := by
  simp only [dottieCachedReferenceWeight, dottieFastReferenceWeight, cachedReferenceCosineTicks_eq]

#print axioms dottie_cached_reference_weight_eq

end QuarticModel
