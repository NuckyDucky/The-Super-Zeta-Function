import QuarticAnnulusBands

namespace QuarticKernel

theorem bandStats_join {lo hi a m b n k : ℕ} {x y z : AnnulusStats}
    (boundary : a + m = b) (width : m + n = k)
    (left : bandStats lo hi a m = x) (right : bandStats lo hi b n = y)
    (total : x + y = z) : bandStats lo hi a k = z := by
  subst b
  subst k
  rw [bandStats_append, left, right, total]

theorem annulusStats_of_band {lo hi rows : ℕ} {record : AnnulusStats}
    (count : annulusRowCount hi = rows)
    (stats : bandStats lo hi 0 rows = record) : annulusStats lo hi = record :=
  (annulusStats_band lo hi).trans ((congrArg (bandStats lo hi 0) count).trans stats)

theorem checkSpans_join {i j w : ℕ} {s c m n next t v total : ℤ} {ws : List ℕ}
    (boundary : i + w = j) (balance : s + c = next)
    (mass : (w : ℤ) * s + m + v = total)
    (stats : annulusStats i j = (c,m,n))
    (positive : 1 ≤ s + if w = 1 then c else n)
    (tail : checkSpans j next ws = (t,v,true)) :
    checkSpans i s (w::ws) = (t,total,true) := by
  subst j
  subst next
  subst total
  exact checkSpans_of_annulus stats positive tail

end QuarticKernel
