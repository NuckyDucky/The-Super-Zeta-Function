import SuperZeta.GaussianRingMidpoint

open SuperZeta SuperZeta.SignWords SuperZeta.GaussianRingMidpoint

/-- error: unsolved goals
case intro
G Z₀ Z₂ D : ℂ → ℂ
w : ℂ
hw : w ∈ rightRing
hG : G w = Z₀ w - Z₂ w
hD : D w = Z₀ w + Z₂ w
hz : G w = 0
m : ℤ
hm : m ≠ 0
u v : List Sign
huv : u ≠ v
h₀ : Z₀ w = D w / 2
h₂ : Z₂ w = D w / 2
he : Z₀ w = Z₂ w
⊢ Resonant.curvature m u = Resonant.curvature m v -/
#guard_msgs in
example {G Z₀ Z₂ D : ℂ → ℂ} {w : ℂ} (hw : w ∈ rightRing)
    (hG : G w = Z₀ w - Z₂ w) (hD : D w = Z₀ w + Z₂ w) (hz : G w = 0)
    {m : ℤ} (hm : m ≠ 0) {u v : List Sign} (huv : u ≠ v) : False := by
  obtain ⟨h₀, h₂⟩ := (half_hits_iff_zero hG hD).mpr hz
  have he : Z₀ w = Z₂ w := h₀.trans h₂.symm
  apply orders_separate hm huv
