import SuperZeta.CapRecovery.Resonant
import SuperZeta.GaussianDiskCount
import SuperZeta.FactorialPhase

/-! Same-input midpoint test for the quartic. The arguments G, Z₀, Z₂
and D denote the Gaussian factor, its continued class sums, and the Dirichlet
total. Their analytic identities are explicit inputs from fields-and-windows.md.
No nonvanishing statement for the Gaussian factor is assumed. -/

namespace SuperZeta.GaussianRingMidpoint

open SuperZeta SuperZeta.SignWords
noncomputable section

def rightRing : Set ℂ :=
  {w | let d := ‖w - GaussianDiskCount.rightCenter StirlingCorrection.dottieHeight‖
       GaussianDiskCount.radius < d ∧ d < (31 / 2048 : ℝ)}

theorem rightRing_in_right_strip {w : ℂ} (hw : w ∈ rightRing) :
    1 / 2 < w.re ∧ w.re < 1 := by
  have hout : ‖w - GaussianDiskCount.rightCenter StirlingCorrection.dottieHeight‖
      < (31 / 2048 : ℝ) := hw.2
  have hb := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt hout)
  change -(31 / 2048 : ℝ) < w.re - 33 / 64 ∧
    w.re - 33 / 64 < 31 / 2048 at hb
  constructor <;> linarith [hb.1, hb.2]

/-- Exactly the two field hits, with the actual total supplied independently. -/
theorem half_hits_iff_zero {G Z₀ Z₂ D : ℂ → ℂ} {w : ℂ}
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) :
    (Z₀ w = D w / 2 ∧ Z₂ w = D w / 2) ↔ G w = 0 := by
  rw [hG, sub_eq_zero]
  constructor
  · rintro ⟨h₀, h₂⟩
    exact h₀.trans h₂.symm
  · intro he
    rw [hD, he]
    constructor <;> ring

/-- This is the project's W''(1)/W'(1) for two sign words at the same lift.
The derivative is with respect to the tower cap. -/
theorem orders_separate {m : ℤ} (hm : m ≠ 0) {u v : List Sign} (huv : u ≠ v) :
    Resonant.curvature m u ≠ Resonant.curvature m v := by
  exact fun he => huv (Resonant.curvature_injective hm he)

/-- Keeping w and the quartic fixed, a zero forces every common rule to
miss at least one of the two different cap readings. The rule sees w. -/
theorem zero_forces_decoder_miss {G Z₀ Z₂ D : ℂ → ℂ} {w : ℂ}
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) (hz : G w = 0)
    {m : ℤ} (hm : m ≠ 0) {u v : List Sign} (huv : u ≠ v)
    (read : ℂ → ℂ → ℂ) :
    read w (Z₀ w) ≠ Resonant.curvature m u ∨
    read w (Z₂ w) ≠ Resonant.curvature m v := by
  obtain ⟨h₀, h₂⟩ := (half_hits_iff_zero hG hD).mpr hz
  by_cases h : read w (Z₀ w) = Resonant.curvature m u
  · right
    intro h'
    exact orders_separate hm huv
      (h.symm.trans ((congrArg (read w) (h₀.trans h₂.symm)).trans h'))
  · exact Or.inl h

/-- The proposed argument, with its outstanding arithmetic step named.
All applications use the original w. No reflected point enters the proof. -/
theorem contradiction_of_transport {G Z₀ Z₂ D : ℂ → ℂ} {w : ℂ}
    (hw : w ∈ rightRing)
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) (hz : G w = 0)
    {m : ℤ} (hm : m ≠ 0) {u v : List Sign} (huv : u ≠ v)
    (transport : ∀ s ∈ rightRing, Z₀ s = Z₂ s →
      Resonant.curvature m u = Resonant.curvature m v) : False := by
  obtain ⟨h₀, h₂⟩ := (half_hits_iff_zero hG hD).mpr hz
  have he : Z₀ w = Z₂ w := h₀.trans h₂.symm
  apply orders_separate hm huv
  exact transport w hw he

/-- For distinct words at a nonzero lift, the outstanding implication is
equivalent to zero exclusion on this exact ring. This explains why it needs
an independent arithmetic proof. -/
theorem transport_iff_ring_clear {G Z₀ Z₂ : ℂ → ℂ}
    (hG : ∀ w ∈ rightRing, G w = Z₀ w - Z₂ w)
    {m : ℤ} (hm : m ≠ 0) {u v : List Sign} (huv : u ≠ v) :
    (∀ w ∈ rightRing, Z₀ w = Z₂ w →
        Resonant.curvature m u = Resonant.curvature m v) ↔
    (∀ w ∈ rightRing, G w ≠ 0) := by
  constructor
  · intro h w hw hz
    have he := sub_eq_zero.mp ((hG w hw).symm.trans hz)
    exact orders_separate hm huv (h w hw he)
  · intro h w hw he
    exact (h w hw ((hG w hw).trans (sub_eq_zero.mpr he))).elim

end
end SuperZeta.GaussianRingMidpoint
