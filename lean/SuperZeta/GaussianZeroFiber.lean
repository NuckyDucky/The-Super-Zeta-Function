import SuperZeta.UnitSpectrum
import SuperZeta.PinchRadius
import Mathlib.Analysis.NormedSpace.Connected

/-! Two Gaussian zeros and the original continued spectral sum at half their inputs. -/

namespace SuperZeta.GaussianZeroFiber

open UnitSpectrum Set Filter Complex
open scoped ComplexConjugate Topology

noncomputable section

private def swapRoots : Unit ⊕ (ℕ ⊕ ℕ) ≃ Unit ⊕ (ℕ ⊕ ℕ) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumComm ℕ ℕ)

private theorem root_swap (j : Unit ⊕ (ℕ ⊕ ℕ)) :
    squaredRoot (swapRoots j) = conj (squaredRoot j) := by
  rcases j with j | (j | j) <;> simp [squaredRoot, RootBounds.family, swapRoots]

private theorem mellin_strip_conj {s : ℂ} (hl : 1 / 2 < s.re) (hu : s.re < 1) :
    continuation (conj s) = conj (continuation s) := by
  have hj (j) : (squaredRoot j).arg ≠ Real.pi :=
    Complex.slitPlane_arg_ne_pi
      ((Ray.indexed_data (s := s) dottie_spec.1.1 levelHeight_spec hl).slit j)
  rw [← (root_hasSum (s := conj s) hl hu).tsum_eq, ← (root_hasSum hl hu).tsum_eq,
    Complex.conj_tsum]
  rw [← swapRoots.tsum_eq (fun j => (squaredRoot j) ^ (-conj s))]
  apply tsum_congr
  intro j
  rw [root_swap, Complex.conj_cpow _ _ (hj j)]
  simp

/-- Reflection for the actual continued root sum. The distinguished real
square is fixed and the other squared roots are exchanged in conjugate pairs.
Agreement on the open Mellin strip extends across the complement of the pole. -/
theorem continuation_conj {s : ℂ} (hs : s ≠ 1 / 2) :
    continuation (conj s) = conj (continuation s) := by
  let U : Set ℂ := {(1 / 2 : ℂ)}ᶜ
  have ha : AnalyticOnNhd ℝ continuation U := by
    intro z hz
    apply (continuation_analytic _).restrictScalars
    intro he
    apply hz
    change z = 1 / 2
    linear_combination (1/2 : ℂ) * he
  have hc (z : ℂ) : AnalyticAt ℝ (fun x : ℂ => conj x) z :=
    Complex.conjCLE.toContinuousLinearMap.analyticAt z
  have hb : AnalyticOnNhd ℝ (fun z => conj (continuation (conj z))) U := by
    intro z hz
    have hn : conj z ∈ U := by
      intro h
      apply hz
      change conj z = 1 / 2 at h
      change z = 1 / 2
      calc z = conj (conj z) := (conj_conj z).symm
           _ = conj (1 / 2 : ℂ) := congrArg _ h
           _ = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    exact (hc _).comp ((ha _ hn).comp (hc z))
  have hbase : (3 / 4 : ℂ) ∈ U := by
    change (3 / 4 : ℂ) ≠ 1 / 2
    norm_num
  have hstrip : continuation =ᶠ[𝓝 (3 / 4 : ℂ)] (fun z => conj (continuation (conj z))) := by
    have ho : IsOpen {z : ℂ | z.re ∈ Ioo (1 / 2 : ℝ) 1} :=
      isOpen_Ioo.preimage continuous_re
    have hp : (3 / 4 : ℂ) ∈ {z : ℂ | z.re ∈ Ioo (1 / 2 : ℝ) 1} := by
      change 1/2 < (3/4 : ℂ).re ∧ (3/4 : ℂ).re < 1
      norm_num
    filter_upwards [ho.mem_nhds hp] with z hz
    rw [mellin_strip_conj hz.1 hz.2, conj_conj]
  have he := ha.eqOn_of_preconnected_of_eventuallyEq hb
    (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    hbase hstrip (show s ∈ U from hs)
  simpa using (congrArg (fun x : ℂ => conj x) he).symm

/-- The original super-zeta reading in the input plane of the Gaussian factor. -/
def reading (w : ℂ) : ℂ := continuation (w / 2)

/-- The critical-line input at signed height t. -/
def linePoint (t : ℝ) : ℂ := ⟨1 / 2, t⟩

theorem reading_neg_height (t : ℝ) : reading (linePoint (-t)) = conj (reading (linePoint t)) := by
  have hc : linePoint (-t) = conj (linePoint t) := rfl
  have hp : linePoint t / 2 ≠ 1 / 2 := by
    intro he
    have := congrArg Complex.re he
    norm_num [linePoint, Complex.div_re] at this
  unfold reading
  rw [hc, ← continuation_conj hp, map_div₀, map_ofNat]

/-- One signed enclosure at the upper point gives a strict lower bound on
the separation of the two spectral readings at the conjugate inputs. -/
theorem reading_separation {t : ℝ} (h : (reading (linePoint t)).im < -47217 / 100000) :
    94434 / 100000 < ‖reading (linePoint (-t)) - reading (linePoint t)‖ := by
  have hb := Complex.im_le_norm (reading (linePoint (-t)) - reading (linePoint t))
  rw [Complex.sub_im, reading_neg_height, Complex.conj_im] at hb
  rw [reading_neg_height]
  linarith

/-- Any single-valued function of the Gaussian output would assign just
one value to zero. The common zero values and the signed upper reading are
the three application inputs supplied by the analytic/interval certificates. -/
theorem no_output_map {G : ℂ → ℂ} {t : ℝ}
    (hUpper : G (linePoint t) = 0) (hLower : G (linePoint (-t)) = 0)
    (h : (reading (linePoint t)).im < -47217 / 100000) :
    ¬ ∃ H : ℂ → ℂ, reading (linePoint t) = H (G (linePoint t)) ∧
                    reading (linePoint (-t)) = H (G (linePoint (-t))) := by
  rintro ⟨H, hr, hl⟩
  rw [hUpper] at hr
  rw [hLower] at hl
  have hb := reading_separation h
  rw [hl.trans hr.symm, sub_self, norm_zero] at hb
  norm_num at hb

/-- The completed Gaussian reading with the same centering as the
arithmetic certificate. The signed ideal coefficients specify its kernel. -/
def completion (K : ℝ → ℝ) (w : ℂ) : ℂ :=
  PinchRadius.halfMellin K (w - 1 / 2)

theorem completion_neg_height (K : ℝ → ℝ) (t : ℝ) :
    completion K (linePoint (-t)) = completion K (linePoint t) := by
  have h : linePoint (-t) - 1/2 = -(linePoint t - 1/2) := by
    apply Complex.ext <;> norm_num [linePoint, Complex.div_re, Complex.div_im]
  simp only [completion, h, PinchRadius.halfMellin_even]

/-- The actual root-sum application needs two external inputs: a zero of
the specified Gaussian kernel in the bracket and an upper spectral enclosure
there. Both lower readings follow from independently proved symmetries. -/
theorem certified_zero_fiber (K : ℝ → ℝ)
    (hz : ∃ t ∈ Ioo (25835/100000 : ℝ) (25838/100000), completion K (linePoint t) = 0)
    (hIm : ∀ t ∈ Ioo (25835/100000 : ℝ) (25838/100000),
      (reading (linePoint t)).im < -47217/100000) :
    ∃ t ∈ Ioo (25835/100000 : ℝ) (25838/100000),
      completion K (linePoint t) = 0 ∧ completion K (linePoint (-t)) = 0 ∧
      94434/100000 < ‖reading (linePoint (-t)) - reading (linePoint t)‖ ∧
      ¬ ∃ H : ℂ → ℂ, reading (linePoint t) = H (completion K (linePoint t)) ∧
        reading (linePoint (-t)) = H (completion K (linePoint (-t))) := by
  obtain ⟨t, ht, hUpper⟩ := hz
  have hLower := (completion_neg_height K t).trans hUpper
  exact ⟨t, ht, hUpper, hLower, reading_separation (hIm t ht),
    no_output_map hUpper hLower (hIm t ht)⟩

end
end SuperZeta.GaussianZeroFiber
