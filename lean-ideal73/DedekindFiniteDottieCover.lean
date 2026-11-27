import DottieDyadicGeometry
import FieldTarget
import Mathlib.Analysis.Analytic.Order

/-! On bounded height bands, isolated zeros leave a positive clearance from
the critical line. The inset dyadic disks give a finite cover of the rest. -/

open Set Complex Filter
open scoped Topology

namespace SuperZeta.StirlingCorrection

/-- Every point through `31/32` lies inside a measuring disk with a radial
margin of at least one scaled unit of `1/2048` at its own height. -/
theorem dottieScaledRightDisk_inset_covers {w : ℂ}
    (hl : 1/2 < w.re) (hu : w.re ≤ 31/32) :
    ∃ n : ℕ, dist w (dottieScaledRightCenter (w.im + 1/512) n) ≤
      (30/2048) * dottieRingScale n := by
  let x : ℝ := w.re - 1/2
  have hx : 0 < x := sub_pos.mpr hl
  have hm : x ≤ 15/32 := by dsimp [x]; linarith
  have hex : ∃ n : ℕ, (2/2048) * dottieRingScale n ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 64*x by positivity)
      (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨n, by unfold dottieRingScale; linarith⟩
  let n := Nat.find hex
  have hlo : (2/2048) * dottieRingScale n ≤ x := Nat.find_spec hex
  have hhi : x ≤ (62/2048) * dottieRingScale n := by
    rcases Nat.eq_zero_or_pos n with hzero | hpos
    · rw [hzero, dottieRingScale, pow_zero]
      linarith
    · obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hmn : m < Nat.find hex := by
        simpa only [← show n = Nat.find hex from rfl, hm'] using Nat.lt_succ_self m
      have hprev : x < (2/2048) * dottieRingScale m := lt_of_not_ge (Nat.find_min hex hmn)
      have hs : 0 < (1/2 : ℝ)^m := by positivity
      rw [hm', dottieRingScale, pow_succ]
      unfold dottieRingScale at hprev
      linarith
  refine ⟨n, ?_⟩
  have hdiff : w - dottieScaledRightCenter (w.im + 1/512) n =
      ((x - dottieRingScale n / 64 : ℝ) : ℂ) := by
    apply Complex.ext
    · change w.re - (1/2 + dottieRingScale n / 64) = x - dottieRingScale n / 64
      dsimp [x]
      ring
    · simp [dottieScaledRightCenter]
  rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A reference height for a disk is offset by `1/512` from its center. -/
abbrev DottieBandRing (l u : ℝ) := {a : ℝ × ℕ // a.1 - 1/512 ∈ Icc l u}

theorem exists_finite_dottie_band_cover (l u ε : ℝ) (hε : 0 < ε) :
    ∃ disks : Finset (DottieBandRing l u),
      ∀ w : ℂ, w.im ∈ Icc l u → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
        ∃ a ∈ disks, w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2)
          (dottieScaledRadius a.val.2) := by
  let patch (a : DottieBandRing l u) : Set ℂ :=
    Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2)
  let box := Icc ((1/2 : ℝ) + ε) (31/32) ×ℂ Icc l u
  have hb : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hcover : box ⊆ ⋃ a, patch a := by
    intro w hw
    have hbox := mem_reProdIm.mp hw
    have hl : 1/2 < w.re := by linarith [hbox.1.1]
    obtain ⟨n, hn⟩ := dottieScaledRightDisk_inset_covers hl hbox.1.2
    let a : DottieBandRing l u := ⟨(w.im + 1/512, n), by simpa using hbox.2⟩
    apply mem_iUnion.mpr
    refine ⟨a, Metric.mem_ball.mpr (hn.trans_lt ?_)⟩
    change (30/2048) * dottieRingScale n < (31/2048) * dottieRingScale n
    have hpos : 0 < dottieRingScale n := by unfold dottieRingScale; positivity
    linarith
  obtain ⟨disks, hdisks⟩ := hb.elim_finite_subcover patch (fun _ => Metric.isOpen_ball) hcover
  refine ⟨disks, fun w him hl hu => ?_⟩
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hdisks (mem_reProdIm.mpr ⟨⟨hl, hu⟩, him⟩))
  obtain ⟨hm, hw⟩ := mem_iUnion.mp ha
  exact ⟨a, hm, hw⟩

end SuperZeta.StirlingCorrection

namespace FieldTarget

open ArtinPrimitiveRootsConjecture SuperZeta.StirlingCorrection

variable {K : Type*} [Field K] [NumberField K] {Z : ℂ → ℂ}

private theorem continuation_exists_nonzero (hZ : IsDedekindZeta K Z) :
    ∃ z ∈ ({1}ᶜ : Set ℂ), Z z ≠ 0 := by
  have hR : (NumberField.dedekindZeta_residue K : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  have hnz := (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne hR
  have hone : ∀ᶠ t : ℝ in 𝓝[>] (1:ℝ), t ∈ Ioi (1:ℝ) := self_mem_nhdsWithin
  obtain ⟨t, ht, hn⟩ := (hone.and hnz).exists
  have ht' : 1 < (t : ℂ).re := by simpa only [ofReal_re, mem_Ioi] using ht
  refine ⟨(t : ℂ), ?_, ?_⟩
  · simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    have he' := congrArg Complex.re he
    rw [one_re] at he'
    linarith
  · intro hz
    apply hn
    rw [← hZ.2 _ ht', hz, mul_zero]

/-- On any bounded height band every Dedekind continuation has some positive
clearance on the right of the line, uniform in height within that band. -/
theorem exists_dedekind_band_clearance (hZ : IsDedekindZeta K Z) (l u : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w.im ∈ Icc l u → 1/2 < w.re → w.re ≤ 31/32 → w.re - 1/2 < ε → Z w ≠ 0 := by
  classical
  let box := Icc (1/2 : ℝ) (31/32) ×ℂ Icc l u
  have hb : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hb1 : box ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw
    simp only [mem_compl_iff, mem_singleton_iff]
    intro he
    subst w
    have hw' := (mem_reProdIm.mp hw).1.2
    norm_num at hw'
  have hc : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _
  obtain ⟨z, hz, hnonzero⟩ := continuation_exists_nonzero hZ
  have hcod := (hZ.1.analyticOnNhd isOpen_compl_singleton).preimage_zero_mem_codiscreteWithin
    hnonzero hz hc
  have hfinite := hb.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hb1 hcod)
  let off := (box \ Z ⁻¹' ({0}ᶜ : Set ℂ)) ∩ {w : ℂ | 1/2 < w.re}
  have hf : off.Finite := hfinite.subset inter_subset_left
  have hmem {w : ℂ} (ht : w.im ∈ Icc l u) (hl : 1/2 < w.re) (hu : w.re ≤ 31/32)
      (hz' : Z w = 0) : w ∈ off := by
    refine ⟨⟨mem_reProdIm.mpr ⟨⟨hl.le, hu⟩, ht⟩, ?_⟩, hl⟩
    simp [hz']
  by_cases hO : off.Nonempty
  · obtain ⟨a, ha, hm⟩ := Set.exists_min_image off (fun w => w.re - 1/2) hf hO
    refine ⟨a.re - 1/2, sub_pos.mpr ha.2, ?_⟩
    intro w ht hl hu hn hz'
    exact (not_le_of_gt hn) (hm w (hmem ht hl hu hz'))
  · exact ⟨1, one_pos, fun _ ht hl hu _ hz' => hO ⟨_, hmem ht hl hu hz'⟩⟩

/-- Each bounded height band has a finite dyadic cover away from its zero-free
clearance. The clearance follows from the field's residue and analyticity. -/
theorem exists_finite_dedekind_band_cover (hZ : IsDedekindZeta K Z) (l u : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ disks : Finset (DottieBandRing l u),
      (∀ w : ℂ, w.im ∈ Icc l u → 1/2 < w.re → w.re ≤ 31/32 →
        w.re - 1/2 < ε → Z w ≠ 0) ∧
      (∀ w : ℂ, w.im ∈ Icc l u → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
        ∃ a ∈ disks, w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2)
          (dottieScaledRadius a.val.2)) := by
  obtain ⟨ε, hε, hz⟩ := exists_dedekind_band_clearance hZ l u
  obtain ⟨disks, hdisks⟩ := exists_finite_dottie_band_cover l u ε hε
  exact ⟨ε, hε, disks, hz, hdisks⟩

end FieldTarget

#print axioms SuperZeta.StirlingCorrection.dottieScaledRightDisk_inset_covers
#print axioms SuperZeta.StirlingCorrection.exists_finite_dottie_band_cover
#print axioms FieldTarget.exists_dedekind_band_clearance
#print axioms FieldTarget.exists_finite_dedekind_band_cover
