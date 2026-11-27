import RayHeckeDedekindTransfer

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set
open DedekindZetaZeroFree
open scoped NumberField

/-- A finite pole set on the line `Re w = 1` does not change uniqueness of
the Dedekind continuation on the strip. -/
theorem eq_mixedThetaContinuation_of_right_match
    (K : Type) [Field K] [NumberField K] {f : ℂ → ℂ} {P : Set ℂ}
    (hP : P.Finite) (hPole : ∀ p ∈ P, p.re = 1)
    (hf : DifferentiableOn ℂ f Pᶜ)
    (hSeries : ∀ z : ℂ, 1 < z.re → f z = NumberField.dedekindZeta K z)
    {w : ℂ} (hw : w.re < 1) : f w = mixedThetaContinuation K w := by
  have hOpen : IsOpen ((P ∪ ({1} : Set ℂ))ᶜ) :=
    (hP.union (Set.finite_singleton 1)).isClosed.isOpen_compl
  have hConnected : IsPreconnected ((P ∪ ({1} : Set ℂ))ᶜ) :=
    ((hP.union (Set.finite_singleton 1)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hLarge {z : ℂ} (hz : 1 < z.re) : z ∈ (P ∪ ({1} : Set ℂ))ᶜ := by
    intro h
    rcases h with hp | hone
    · exact (ne_of_gt hz) (hPole z hp)
    · exact (ne_of_gt hz) (by rw [Set.mem_singleton_iff.mp hone, Complex.one_re])
  have hSmall : w ∈ (P ∪ ({1} : Set ℂ))ᶜ := by
    intro h
    rcases h with hp | hone
    · exact (ne_of_lt hw) (hPole w hp)
    · exact (ne_of_lt hw) (by rw [Set.mem_singleton_iff.mp hone, Complex.one_re])
  have hMatch : f =ᶠ[nhds (2 : ℂ)] mixedThetaContinuation K := by
    refine Filter.eventually_of_mem ?_ (fun z (hz : 1 < z.re) ↦ ?_)
    · exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp : 1 < (2 : ℂ).re)
    · exact (hSeries z hz).trans ((mixedThetaContinuation_isDedekind K).2 z hz).symm
  have hf' : DifferentiableOn ℂ f (P ∪ ({1} : Set ℂ))ᶜ :=
    hf.mono (Set.compl_subset_compl.mpr Set.subset_union_left)
  have hZ' : DifferentiableOn ℂ (mixedThetaContinuation K) (P ∪ ({1} : Set ℂ))ᶜ :=
    (mixedThetaContinuation_isDedekind K).1.mono
    (Set.compl_subset_compl.mpr Set.subset_union_right)
  exact (hf'.analyticOnNhd hOpen).eqOn_of_preconnected_of_eventuallyEq
    (hZ'.analyticOnNhd hOpen) hConnected (hLarge (by simp : 1 < (2 : ℂ).re)) hMatch hSmall

/-- Nonvanishing for all Dedekind continuations at a strip input passes to
each ray-character reading at that input. -/
theorem rayHeckeContinuation_ne_zero_of_dedekind
    (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
    (hm : m ≠ ⊥) (χ : RayClassCharacter K m) {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1)
    (hZ : ∀ (E : Type) [Field E] [NumberField E], mixedThetaContinuation E w ≠ 0) :
    rayHeckeContinuation hm χ w ≠ 0 := by
  intro hzero
  obtain ⟨R, hLift⟩ := rayHecke_zero_lifts_to_dedekind K m hm χ
  have hw : w ≠ 1 := by
    rintro rfl
    exact lt_irrefl 1 hhi
  exact hZ R.extension (hLift w hlo hw hzero)

/-- The previous `31/32` equivalence can use any proved Dedekind right edge.
The remaining interval includes the new cutoff. -/
theorem allDedekindRH_iff_rayHecke_right_band_of_dedekind_edge {σ : ℝ} (hσ : σ < 1)
    (hEdge : ∀ (K : Type) [Field K] [NumberField K] (w : ℂ),
      σ < w.re → w.re < 1 → mixedThetaContinuation K w ≠ 0) :
    (∀ (K : Type) [Field K] [NumberField K], DedekindZetaRH K) ↔
      ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K))
        (hm : m ≠ ⊥) (χ : RayClassCharacter K m) (w : ℂ),
        1 / 2 < w.re → w.re ≤ σ → rayHeckeContinuation hm χ w ≠ 0 := by
  constructor
  · intro h K _ _ m hm χ w hlo hhi hz
    have hLine := allDedekindRH_iff_all_rayHeckeRH.mp h K m hm χ w
      (by linarith only [hlo]) (hhi.trans_lt hσ) hz
    exact (ne_of_gt hlo) hLine
  · intro h
    apply allDedekindRH_iff_rayHecke_right_band.mpr
    intro K _ _ m hm χ w hlo hhi
    by_cases hBand : w.re ≤ σ
    · exact h K m hm χ w hlo hBand
    · have hw : w.re < 1 := by linarith only [hhi]
      exact rayHeckeContinuation_ne_zero_of_dedekind K m hm χ
        (by linarith only [hlo]) hw (fun E _ _ ↦ hEdge E w (lt_of_not_ge hBand) hw)

#check @eq_mixedThetaContinuation_of_right_match
#check @allDedekindRH_iff_rayHecke_right_band_of_dedekind_edge
#print axioms eq_mixedThetaContinuation_of_right_match
#print axioms rayHeckeContinuation_ne_zero_of_dedekind
#print axioms allDedekindRH_iff_rayHecke_right_band_of_dedekind_edge

end FieldTarget
