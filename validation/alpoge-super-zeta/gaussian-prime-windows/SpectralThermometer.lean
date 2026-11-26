import SuperZeta.UnitSpectrum
import ArchivedQuarticOrders

/-! A same-input comparison with arbitrary spectral weights and a list of
ordered quaternion readings. Zero transfer and exclusion state their premises. -/

namespace SuperZeta

noncomputable section

structure SpectralThermometer (Weight : Type*) where
  address : ℂ → ℂ
  spectrum : Weight → ℂ → ℂ
  reference : Weight → ℂ → ℂ
  quaternionAt : Weight → ℂ → Quaternion ℝ
  comparisons : List (Quaternion ℝ → Quaternion ℝ)

namespace SpectralThermometer

def gap {Weight : Type*} (m : SpectralThermometer Weight) (weight : Weight) (w : ℂ) : ℂ :=
  m.spectrum weight (m.address w) - m.reference weight (m.address w)

def readings {Weight : Type*} (m : SpectralThermometer Weight) (weight : Weight) (w : ℂ) :
    List (Quaternion ℝ) :=
  m.comparisons.map (fun compare => compare (m.quaternionAt weight w))

/-- The horizontal coordinate and height determine one point for every reading. -/
def atHeight {Weight : Type*} (m : SpectralThermometer Weight) (weight : Weight)
    (σ height : ℝ) : ℂ × ℂ × List (Quaternion ℝ) :=
  let w : ℂ := ⟨σ, height⟩
  (w, m.gap weight w, m.readings weight w)

theorem gap_zero_iff {Weight : Type*} (m : SpectralThermometer Weight)
    {weight : Weight} {w factor : ℂ} {target : ℂ → ℂ}
    (hTransfer : m.gap weight w = factor * target w) (hFactor : factor ≠ 0) :
    m.gap weight w = 0 ↔ target w = 0 := by
  rw [hTransfer, mul_eq_zero]
  exact or_iff_right hFactor

/-- Two settings report the same zero event when both read the same target
at the same point with nonzero factors. -/
theorem same_zero_event {W₁ W₂ : Type*} (left : SpectralThermometer W₁)
    (right : SpectralThermometer W₂) {a : W₁} {b : W₂} {w c d : ℂ} {target : ℂ → ℂ}
    (hLeft : left.gap a w = c * target w) (hc : c ≠ 0)
    (hRight : right.gap b w = d * target w) (hd : d ≠ 0) :
    left.gap a w = 0 ↔ right.gap b w = 0 :=
  (left.gap_zero_iff hLeft hc).trans (right.gap_zero_iff hRight hd).symm

theorem exclude_zero_of_gap {Weight : Type*} (m : SpectralThermometer Weight)
    {weight : Weight} {w factor measured : ℂ} {target : ℂ → ℂ} {error : ℝ}
    (hTransfer : m.gap weight w = factor * target w) (hFactor : factor ≠ 0)
    (hError : ‖m.gap weight w - measured‖ ≤ error) (hGap : error < ‖measured‖) :
    target w ≠ 0 := by
  intro h
  have hz := (m.gap_zero_iff hTransfer hFactor).mpr h
  rw [hz, zero_sub, norm_neg] at hError
  exact (not_lt_of_ge hError) hGap

open QuarticOrderedTurns QuarticModel SuperZeta.StirlingCorrection

/-- The original unit spectrum and painted Gaussian reading share the same
input w. Extra comparisons are retained after the checked j,k comparison. -/
def archived (ink : ℂ → ℂ) (extra : List (Quaternion ℝ → Quaternion ℝ)) :
    SpectralThermometer Unit where
  address := fun w => w / 2
  spectrum := fun _ => UnitSpectrum.continuation
  reference := fun _ => Reference.entireCorrection 1
  quaternionAt := fun _ w => paintedReading w (ink w)
  comparisons := (fun q => jk q - kj q) :: extra

theorem archived_gap_zero_iff (ink : ℂ → ℂ) (extra : List (Quaternion ℝ → Quaternion ℝ))
    {w : ℂ} (h₀ : 0 < w.re) (h₁ : w.re < 1) :
    (archived ink extra).gap () w = 0 ↔ riemannZeta w = 0 := by
  have hs₀ : 0 < (w / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hs₁ : (w / 2).re < 1 / 2 := by rw [Complex.div_ofNat_re]; linarith
  have h := (UnitSpectrum.equality_iff_riemann_zero hs₀ hs₁).2
  rw [show 2 * (w / 2) = w by ring] at h
  change UnitSpectrum.continuation (w / 2) - Reference.entireCorrection 1 (w / 2) = 0 ↔ _
  rw [sub_eq_zero]
  exact h

theorem archived_gaussian_zero_iff (ink : ℂ → ℂ)
    (extra : List (Quaternion ℝ → Quaternion ℝ)) (w : ℂ) :
    ((archived ink extra).readings () w).head? = some 0 ↔ archivedMellin w = 0 := by
  change some (jk (paintedReading w (ink w)) - kj (paintedReading w (ink w))) = some 0 ↔ _
  rw [Option.some.injEq, paintedReading, order_difference_after_paint, sub_eq_zero, order_eq_iff]

#print axioms gap_zero_iff
#print axioms same_zero_event
#print axioms exclude_zero_of_gap
#print axioms archived_gap_zero_iff
#print axioms archived_gaussian_zero_iff

end SpectralThermometer

end
end SuperZeta
