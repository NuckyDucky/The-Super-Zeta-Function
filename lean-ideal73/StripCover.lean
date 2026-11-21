import FieldTarget
import Mathlib.Tactic

/-! A compact exhaustion for the field target. `FieldTarget` contains the
two definitions from Formal Conjectures. Each box admits
its own lower bound; the bounds may tend to zero along the exhaustion. -/

namespace StripCover

open Complex Set FieldTarget ArtinPrimitiveRootsConjecture

/-- Reflect across the vertical line through 1/2, preserving the height. -/
def reflection (s : ℂ) : ℂ := ⟨1 - s.re, s.im⟩

/-- Positive denominator also for the first box (which has height zero). -/
noncomputable def margin (n : ℕ) : ℝ := 1 / ((n : ℝ) + 5)

def rightBox (n : ℕ) : Set ℂ :=
  Complex.reProdIm (Icc (1 / 2 + margin n) (1 - margin n))
    (Icc (-(n : ℝ)) (n : ℝ))

theorem rightBox_subset {n : ℕ} {s : ℂ} (hs : s ∈ rightBox n) :
    1 / 2 < s.re ∧ s.re < 1 := by
  rcases Complex.mem_reProdIm.mp hs with ⟨⟨hl, hr⟩, _⟩
  have hp : 0 < margin n := by unfold margin; positivity
  constructor <;> linarith

theorem rightBox_exhaustion (s : ℂ) (hl : 1 / 2 < s.re) (hr : s.re < 1) :
    ∃ n : ℕ, s ∈ rightBox n := by
  let edge := min (s.re - 1 / 2) (1 - s.re)
  have he : 0 < edge := lt_min (sub_pos.mpr hl) (sub_pos.mpr hr)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / edge) |s.im|)
  have h₁ := lt_of_le_of_lt (le_max_left (1 / edge) |s.im|) hn
  have h₂ := lt_of_le_of_lt (le_max_right (1 / edge) |s.im|) hn
  have hδ : margin n ≤ edge := by
    apply (one_div_le (by positivity : 0 < (n : ℝ) + 5) he).2
    linarith
  have h₃ : margin n ≤ s.re - 1 / 2 := hδ.trans (min_le_left _ _)
  have h₄ : margin n ≤ 1 - s.re := hδ.trans (min_le_right _ _)
  obtain ⟨h₅, h₆⟩ := abs_lt.mp h₂
  exact ⟨n, Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, h₅.le, h₆.le⟩⟩

/-- Only zero symmetry is used in passing from the right half to the left half. -/
def ReflectsZeros (F : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → F s = 0 → F (reflection s) = 0

/-- Each box must have a positive lower bound for the actual function. -/
def BoxMargins (F : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ rightBox n, ε ≤ ‖F s‖

/-- A disk of inputs, together with a disk in which all its computed values lie. -/
structure Patch where
  center : ℂ
  radius : ℝ
  value : ℂ
  error : ℝ

/-- Finite input disks on each box. Each output enclosure must hold for the
whole intersection of its input disk with the box, and must miss zero. -/
def HasPatchBounds (F : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (P : Fin k → Patch),
    (∀ s ∈ rightBox n, ∃ i, dist s (P i).center ≤ (P i).radius) ∧
    ∀ i, (P i).error < ‖(P i).value‖ ∧
      ∀ s ∈ rightBox n, dist s (P i).center ≤ (P i).radius →
        ‖F s - (P i).value‖ ≤ (P i).error

theorem boxMargins_of_patchBounds {F : ℂ → ℂ}
    (hc : ∀ n, ContinuousOn F (rightBox n)) (cert : HasPatchBounds F) :
    BoxMargins F := by
  intro n
  have hcompact : IsCompact (rightBox n) := isCompact_Icc.reProdIm isCompact_Icc
  apply hcompact.exists_forall_le' (hc n).norm
  intro s hs
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨_, P, cover, valid⟩ := cert n
  obtain ⟨i, hi⟩ := cover s hs
  have h := (valid i).2 s hs hi
  rw [hz, zero_sub, norm_neg] at h
  exact (valid i).1.not_ge h

theorem strip_iff_boxMargins {F : ℂ → ℂ}
    (hc : ∀ n, ContinuousOn F (rightBox n)) (hf : ReflectsZeros F) :
    StripZerosOnLine F ↔ BoxMargins F := by
  constructor
  · intro h n
    by_cases hn : (rightBox n).Nonempty
    · have hcompact : IsCompact (rightBox n) := isCompact_Icc.reProdIm isCompact_Icc
      obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn hn (hc n).norm
      have ⟨hl, hr⟩ := rightBox_subset hz
      have hne : F z ≠ 0 := by
        intro hz0
        exact hl.ne' (h z (by linarith) hr hz0)
      exact ⟨‖F z‖, norm_pos_iff.mpr hne, fun s hs => hmin hs⟩
    · exact ⟨1, by norm_num, fun s hs => (hn ⟨s, hs⟩).elim⟩
  · intro bounds
    have excludes : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → F s ≠ 0 := by
      intro s hl hr hzero
      obtain ⟨n, hn⟩ := rightBox_exhaustion s hl hr
      obtain ⟨ε, hp, hm⟩ := bounds n
      have h := hm s hn
      rw [hzero, norm_zero] at h
      exact hp.not_ge h
    intro s hl hr hz
    rcases lt_trichotomy s.re (1 / 2) with hs | heq | hs
    · have h₁ : 1 / 2 < (reflection s).re := by change 1/2 < 1 - s.re; linarith
      have h₂ : (reflection s).re < 1 := by change 1 - s.re < 1; linarith
      exact (excludes _ h₁ h₂ (hf s hl hs hz)).elim
    · exact heq
    · exact (excludes s hs hr hz).elim

private theorem continuousOnBox {K : Type*} [Field K] [NumberField K] {Z : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z) (n : ℕ) : ContinuousOn Z (rightBox n) := by
  apply hZ.1.continuousOn.mono
  intro s hs
  have hr := (rightBox_subset hs).2
  rintro rfl
  simp at hr

/-- Once a continuation of the ideal-counting series and its zero symmetry
are supplied, this is exactly the fixed-field Formal Conjectures predicate. -/
theorem fieldRH_iff_boxMargins {K : Type*} [Field K] [NumberField K] {Z : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z) (hreflect : ReflectsZeros Z) :
    DedekindZetaRH K ↔ BoxMargins Z :=
  (dedekindZetaRH_iff_strip hZ).trans (strip_iff_boxMargins (continuousOnBox hZ) hreflect)

theorem fieldRH_of_patchBounds {K : Type*} [Field K] [NumberField K] {Z : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z) (hreflect : ReflectsZeros Z) (cert : HasPatchBounds Z) :
    DedekindZetaRH K :=
  (fieldRH_iff_boxMargins hZ hreflect).mpr (boxMargins_of_patchBounds (continuousOnBox hZ) cert)

/-- With a verified three-factor product and critical-line results for the
first two factors, the positive margins are required only for the third. -/
theorem fieldRH_iff_thirdFactorBoxMargins {K : Type*} [Field K] [NumberField K]
    {A B C : ℂ → ℂ} (hp : IsDedekindZeta K (fun s => A s * B s * C s))
    (hA : StripZerosOnLine A) (hB : StripZerosOnLine B)
    (hc : ∀ n, ContinuousOn C (rightBox n)) (hf : ReflectsZeros C) :
    DedekindZetaRH K ↔ BoxMargins C :=
  (dedekindZetaRH_iff_third_factor hp.1 hp.2 hA hB).trans (strip_iff_boxMargins hc hf)

#print axioms rightBox_exhaustion
#print axioms boxMargins_of_patchBounds
#print axioms strip_iff_boxMargins
#print axioms fieldRH_iff_boxMargins
#print axioms fieldRH_of_patchBounds
#print axioms fieldRH_iff_thirdFactorBoxMargins

end StripCover
