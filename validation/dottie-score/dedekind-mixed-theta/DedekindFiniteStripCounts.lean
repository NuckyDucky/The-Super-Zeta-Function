import DedekindMixedThetaSignedRings
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Complete cumulative counts in the critical strip. The pole-cleared
Mellin reading extends across the edges, so its zeros cannot accumulate
at the two ends of a bounded rectangle. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Filter Metric NumberField Set
open DedekindZetaZeroFree.AbelianQuotient
open scoped BigOperators NumberField Topology

noncomputable section

/-- Entire functions with a nonzero value have finite vanishing order
and can be counted with natural multiplicities. -/
structure NonzeroEntireFunction where
  toFun : ℂ → ℂ
  differentiable : Differentiable ℂ toFun
  exists_ne_zero : ∃ z, toFun z ≠ 0

instance : CoeFun NonzeroEntireFunction (fun _ ↦ ℂ → ℂ) := ⟨NonzeroEntireFunction.toFun⟩

namespace NonzeroEntireFunction

theorem analyticOnNhd (f : NonzeroEntireFunction) : AnalyticOnNhd ℂ f.toFun univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr f.differentiable

theorem order_ne_top (f : NonzeroEntireFunction) (w : ℂ) : analyticOrderAt f.toFun w ≠ ⊤ := by
  obtain ⟨z, hz⟩ := f.exists_ne_zero
  exact f.analyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ z) (mem_univ w)
    (by rw [(f.analyticOnNhd z (mem_univ z)).analyticOrderAt_eq_zero.mpr hz]; simp)

theorem orderNat_eq_zero_iff (f : NonzeroEntireFunction) (w : ℂ) :
    analyticOrderNatAt f.toFun w = 0 ↔ f w ≠ 0 := by
  unfold analyticOrderNatAt
  rw [ENat.toNat_eq_zero, or_iff_left (f.order_ne_top w),
    (f.analyticOnNhd w (mem_univ w)).analyticOrderAt_eq_zero]

/-- The set of distinct zeros through height `T`, in the open critical strip. -/
def stripZeroSet (f : NonzeroEntireFunction) (T : ℝ) : Set ℂ :=
  {w | 0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ T ∧ f w = 0}

theorem finite_stripZeroSet (f : NonzeroEntireFunction) (T : ℝ) :
    (f.stripZeroSet T).Finite := by
  let B := closedBall (0 : ℂ) (1 + T)
  obtain ⟨z, hz⟩ := f.exists_ne_zero
  have hcod : f.toFun ⁻¹' ({0}ᶜ : Set ℂ) ∈ codiscreteWithin B :=
    codiscreteWithin_mono (subset_univ B) (f.analyticOnNhd.preimage_zero_mem_codiscrete hz)
  apply ((isCompact_closedBall (0 : ℂ) (1 + T)).finite_sdiff_of_mem_codiscreteWithin hcod).subset
  intro w hw
  rcases hw with ⟨hlo, hhi, him, hzero⟩
  constructor
  · rw [mem_closedBall, dist_zero_right]
    refine (norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hlo]
    linarith only [hhi, him]
  · simp [hzero]

def stripZeros (f : NonzeroEntireFunction) (T : ℝ) : Finset ℂ :=
  (f.finite_stripZeroSet T).toFinset

@[simp] theorem mem_stripZeros (f : NonzeroEntireFunction) (T : ℝ) (w : ℂ) :
    w ∈ f.stripZeros T ↔ 0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ T ∧ f w = 0 :=
  (f.finite_stripZeroSet T).mem_toFinset

/-- Count the selected strip zeros through `T`, with their natural
vanishing orders. Use `True` to count every zero. -/
def stripZeroCount (f : NonzeroEntireFunction) (T : ℝ) (P : ℂ → Prop) : ℕ := by
  classical
  exact ∑ w ∈ (f.stripZeros T).filter P, analyticOrderNatAt f.toFun w

theorem stripZeroCount_eq_zero_of_no_selection (f : NonzeroEntireFunction) (T : ℝ) (P : ℂ → Prop)
    (h : ∀ w ∈ f.stripZeros T, ¬ P w) : f.stripZeroCount T P = 0 := by
  classical
  unfold stripZeroCount
  apply Finset.sum_eq_zero
  intro w hw
  obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hw
  exact (h w hm hp).elim

theorem stripCounts_equal_iff (f : NonzeroEntireFunction) (T : ℝ) :
    f.stripZeroCount T (fun _ ↦ True) = f.stripZeroCount T (fun w ↦ w.re = 1 / 2) ↔
      ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| ≤ T → f w = 0 → w.re = 1 / 2 := by
  classical
  let s := f.stripZeros T
  let p : ℂ → Prop := fun w ↦ w.re = 1 / 2
  let m := analyticOrderNatAt f.toFun
  simp only [stripZeroCount, Finset.filter_true]
  change (∑ w ∈ s, m w) = (∑ w ∈ s.filter p, m w) ↔ _
  constructor
  · intro hcount w hlo hhi him hz
    by_contra hOff
    have hmem : w ∈ s := (f.mem_stripZeros T w).mpr ⟨hlo, hhi, him, hz⟩
    have hOffMem : w ∈ s.filter (fun z ↦ ¬ p z) := Finset.mem_filter.mpr ⟨hmem, hOff⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not s p m
    have hoffZero : (∑ z ∈ s.filter (fun z ↦ ¬ p z), m z) = 0 := by
      rw [hcount] at hsplit
      exact Nat.add_left_cancel (hsplit.trans (Nat.add_zero _).symm)
    have hle := Finset.single_le_sum (f := m) (fun z _ ↦ Nat.zero_le (m z)) hOffMem
    have hpos : 0 < m w :=
      Nat.pos_iff_ne_zero.mpr (fun h ↦ ((f.orderNat_eq_zero_iff w).mp h) hz)
    exact Nat.not_lt_zero _ (hpos.trans_le (hle.trans_eq hoffZero))
  · intro h
    have hfilter : s.filter p = s := Finset.filter_true_of_mem (fun w hw ↦ by
      obtain ⟨hlo, hhi, him, hz⟩ := (f.mem_stripZeros T w).mp hw
      exact h w hlo hhi him hz)
    rw [hfilter]

/-- The counts use every strip zero through each checkpoint. Equality at
cofinal checkpoints characterizes the strip-zero statement. -/
theorem stripZerosOnLine_iff_cofinalCounts (f : NonzeroEntireFunction) :
    StripZerosOnLine f.toFun ↔ ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      f.stripZeroCount T (fun _ ↦ True) = f.stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  constructor
  · intro h H
    exact ⟨H, le_rfl, (f.stripCounts_equal_iff H).mpr (fun w hlo hhi _ hz ↦ h w hlo hhi hz)⟩
  · intro h w hlo hhi hz
    obtain ⟨T, hT, hcount⟩ := h |w.im|
    exact (f.stripCounts_equal_iff T).mp hcount w hlo hhi hT hz

theorem orderNat_eq_factor_square (f g c : NonzeroEntireFunction)
    (hprod : f.toFun = g.toFun * c.toFun ^ 2) (w : ℂ) :
    analyticOrderNatAt f.toFun w =
      analyticOrderNatAt g.toFun w + 2 * analyticOrderNatAt c.toFun w := by
  have hg := g.analyticOnNhd w (mem_univ w)
  have hc := c.analyticOnNhd w (mem_univ w)
  have hCSq : analyticOrderAt (c.toFun ^ 2) w ≠ ⊤ := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (c.order_ne_top w)
    rw [analyticOrderAt_pow hc, ← hm, two_nsmul]
    simp
  rw [hprod, analyticOrderNatAt_mul hg (hc.pow 2) (g.order_ne_top w) hCSq,
    analyticOrderNatAt_pow hc, two_nsmul, two_mul]

theorem stripZeroCount_factor_square (f g c : NonzeroEntireFunction)
    (hprod : f.toFun = g.toFun * c.toFun ^ 2) (T : ℝ) (P : ℂ → Prop) :
    f.stripZeroCount T P = g.stripZeroCount T P + 2 * c.stripZeroCount T P := by
  classical
  let s := (f.stripZeros T).filter P
  have heq (w : ℂ) : f w = g w * c w ^ 2 := congrFun hprod w
  have hsum (r : NonzeroEntireFunction) (hz : ∀ w, r w = 0 → f w = 0) :
      r.stripZeroCount T P = ∑ w ∈ s, analyticOrderNatAt r.toFun w := by
    have hsub : (r.stripZeros T).filter P ⊆ s := by
      intro w hw
      obtain ⟨hm, hP⟩ := Finset.mem_filter.mp hw
      obtain ⟨hlo, hhi, him, hzero⟩ := (r.mem_stripZeros T w).mp hm
      exact Finset.mem_filter.mpr ⟨(f.mem_stripZeros T w).mpr ⟨hlo, hhi, him, hz w hzero⟩, hP⟩
    apply Finset.sum_subset hsub
    intro w hw hn
    apply (r.orderNat_eq_zero_iff w).mpr
    intro hzero
    obtain ⟨hm, hP⟩ := Finset.mem_filter.mp hw
    obtain ⟨hlo, hhi, him, _⟩ := (f.mem_stripZeros T w).mp hm
    exact hn (Finset.mem_filter.mpr ⟨(r.mem_stripZeros T w).mpr ⟨hlo, hhi, him, hzero⟩, hP⟩)
  rw [hsum g (fun w hz ↦ by rw [heq, hz, zero_mul]),
    hsum c (fun w hz ↦ by rw [heq, hz]; simp)]
  change (∑ w ∈ s, analyticOrderNatAt f.toFun w) = _
  calc
    _ = ∑ w ∈ s, (analyticOrderNatAt g.toFun w + 2 * analyticOrderNatAt c.toFun w) :=
      Finset.sum_congr rfl (fun w _ ↦ f.orderNat_eq_factor_square g c hprod w)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

end NonzeroEntireFunction

/-- The entire version of the pole-cleared reading. -/
def mixedThetaEntireReading (K : Type) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀

theorem mixedThetaEntireReading_eq_signed (K : Type) [Field K] [NumberField K] (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaEntireReading K w = mixedThetaSignedReading K w :=
  (mixedThetaSignedReading_eq_mellin_sub K w hlo hhi).symm

theorem mixedThetaEntireReading_zero_iff (K : Type) [Field K] [NumberField K] (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaEntireReading K w = 0 ↔ mixedThetaContinuation K w = 0 := by
  rw [mixedThetaEntireReading_eq_signed K w hlo hhi, mixedThetaSignedReading_zero_iff K w hlo hhi]

theorem mixedThetaEntireReading_orderNat_eq_continuation (K : Type) [Field K] [NumberField K]
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    analyticOrderNatAt (mixedThetaEntireReading K) w =
      analyticOrderNatAt (mixedThetaContinuation K) w := by
  have hOpen : IsOpen (Complex.re ⁻¹' Ioo (0 : ℝ) 1) :=
    continuous_re.isOpen_preimage _ isOpen_Ioo
  have hEq : mixedThetaEntireReading K =ᶠ[𝓝 w] mixedThetaSignedReading K := by
    filter_upwards [hOpen.mem_nhds ⟨hlo, hhi⟩] with z hz
    exact mixedThetaEntireReading_eq_signed K z hz.1 hz.2
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hEq, mixedThetaSignedReading_order_eq_continuation K hlo hhi]

theorem mixedThetaEntireReading_differentiable (K : Type) [Field K] [NumberField K] :
    Differentiable ℂ (mixedThetaEntireReading K) := by
  have hp : Differentiable ℂ (fun z : ℂ ↦ z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  exact (hp.mul (Theta.mixedThetaPair K).differentiable_Λ₀).sub (differentiable_const _)

theorem mixedThetaEntireReading_ne_zero_at_zero (K : Type) [Field K] [NumberField K] :
    mixedThetaEntireReading K 0 ≠ 0 := by
  have ha : 0 < Theta.alpha K := by
    unfold Theta.alpha
    exact div_pos (mul_pos (pow_pos (by norm_num) _) (Units.regulator_pos K))
      (Nat.cast_pos.mpr (Units.torsionOrder_pos K))
  have hf : (Theta.mixedThetaPair K).f₀ ≠ 0 := by
    change (Theta.alpha K : ℂ) * (Fintype.card (ClassGroup (𝓞 K)) : ℂ) ≠ 0
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne')
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simpa [mixedThetaEntireReading] using neg_ne_zero.mpr hf

/-- A nonzero entire counting function for each number field. On the
critical strip its zeros and orders are those of the actual continuation. -/
def mixedThetaCountingFunction (K : Type) [Field K] [NumberField K] : NonzeroEntireFunction :=
  ⟨mixedThetaEntireReading K, mixedThetaEntireReading_differentiable K,
    ⟨0, mixedThetaEntireReading_ne_zero_at_zero K⟩⟩

theorem dedekindZetaRH_iff_cofinal_mixedTheta_counts (K : Type) [Field K] [NumberField K] :
    DedekindZetaRH K ↔ ∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧
      (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
        (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2) := by
  rw [← (mixedThetaCountingFunction K).stripZerosOnLine_iff_cofinalCounts,
    dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind K)]
  exact ⟨fun h w hlo hhi hz ↦ h w hlo hhi ((mixedThetaEntireReading_zero_iff K w hlo hhi).mp hz),
    fun h w hlo hhi hz ↦ h w hlo hhi ((mixedThetaEntireReading_zero_iff K w hlo hhi).mpr hz)⟩

#check @NonzeroEntireFunction.stripZeroCount_factor_square
#check @dedekindZetaRH_iff_cofinal_mixedTheta_counts
#print axioms NonzeroEntireFunction.finite_stripZeroSet
#print axioms NonzeroEntireFunction.orderNat_eq_zero_iff
#print axioms NonzeroEntireFunction.stripZerosOnLine_iff_cofinalCounts
#print axioms NonzeroEntireFunction.orderNat_eq_factor_square
#print axioms NonzeroEntireFunction.stripZeroCount_factor_square
#print axioms mixedThetaEntireReading_orderNat_eq_continuation
#print axioms mixedThetaEntireReading_ne_zero_at_zero
#print axioms dedekindZetaRH_iff_cofinal_mixedTheta_counts

end
end FieldTarget
