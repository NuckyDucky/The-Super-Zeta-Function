import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace FieldTarget

open Finset

def discriminant23PrincipalForm (m n : ℤ) : ℤ := m ^ 2 + m * n + 6 * n ^ 2

def discriminant23OtherForm (m n : ℤ) : ℤ := 2 * m ^ 2 + m * n + 3 * n ^ 2

private def thetaBox : Finset (ℤ × ℤ) :=
  (Icc (-4) 4).product (Icc (-4) 4)

private def normalizedFormTerm {R : Type*} [MonoidWithZero R]
    (Q : ℤ → ℤ → ℤ) (q : R) (p : ℤ × ℤ) : R :=
  if p = (0, 0) then 0 else q ^ (Q p.1 p.2 - 1).toNat

/-- The eighty nonzero lattice points with both coordinates between `-4` and `4`,
plus a geometric upper bound for the omitted points. -/
def discriminant23ThetaEnvelope (Q : ℤ → ℤ → ℤ) : ℚ :=
  (∑ p ∈ thetaBox, normalizedFormTerm Q (3 / 11 : ℚ) p) +
    (440 / 3 : ℚ) * (3 / 5) ^ 25

theorem discriminant23_principal_envelope_lt :
    discriminant23ThetaEnvelope discriminant23PrincipalForm < 21 / 10 := by
  decide +kernel

theorem discriminant23_other_envelope_lt :
    discriminant23ThetaEnvelope discriminant23OtherForm < 3 / 4 := by
  decide +kernel

theorem discriminant23_principal_form_growth (m n : ℤ) :
    m ^ 2 + n ^ 2 ≤ 2 * discriminant23PrincipalForm m n := by
  unfold discriminant23PrincipalForm
  nlinarith only [sq_nonneg (m + n), sq_nonneg n]

theorem discriminant23_other_form_growth (m n : ℤ) :
    m ^ 2 + n ^ 2 ≤ 2 * discriminant23OtherForm m n := by
  unfold discriminant23OtherForm
  nlinarith only [sq_nonneg (m + n), sq_nonneg m, sq_nonneg n]

noncomputable def discriminant23ThetaScale : ℝ := 2 * Real.pi / Real.sqrt 23

theorem discriminant23_thetaScale_interval :
    13 / 10 ≤ discriminant23ThetaScale ∧ discriminant23ThetaScale ≤ 4 / 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 23)
  have hsn := Real.sqrt_nonneg 23
  have hl : (479 / 100 : ℝ) ≤ Real.sqrt 23 := by nlinarith only [hs, hsn]
  have hu : Real.sqrt 23 ≤ (24 / 5 : ℝ) := by nlinarith only [hs, hsn]
  have hp : 0 < Real.sqrt 23 := by positivity
  constructor
  · apply (le_div_iff₀ hp).2
    nlinarith only [hu, Real.pi_gt_d2]
  · apply (div_le_iff₀ hp).2
    nlinarith only [hl, Real.pi_lt_d2]

theorem discriminant23_thetaExp_interval :
    1 / 4 ≤ Real.exp (-discriminant23ThetaScale) ∧
      Real.exp (-discriminant23ThetaScale) ≤ 3 / 11 := by
  obtain ⟨hl, hu⟩ := discriminant23_thetaScale_interval
  have he := Real.exp_bound' (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) (n := 5) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have htwo : Real.exp (2 / 3) ≤ 2 := by linarith only [he]
  have hfour : Real.exp (4 / 3) ≤ 4 := by
    rw [show (4 / 3 : ℝ) = 2 / 3 + 2 / 3 by norm_num, Real.exp_add]
    exact le_trans (mul_le_mul htwo htwo (Real.exp_pos _).le (by norm_num)) (by norm_num)
  have hlow := Real.sum_le_exp_of_nonneg (x := (13 / 10 : ℝ)) (by norm_num) 7
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlow
  have helo : (11 / 3 : ℝ) ≤ Real.exp (13 / 10) := by linarith only [hlow]
  rw [Real.exp_neg]
  constructor
  · simpa only [one_div] using
      one_div_le_one_div_of_le (Real.exp_pos _) ((Real.exp_le_exp.mpr hu).trans hfour)
  · rw [show (3 / 11 : ℝ) = 1 / (11 / 3) by norm_num]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11 / 3)
        (helo.trans (Real.exp_le_exp.mpr hl))

noncomputable section

private def latticeRatio : ℝ := 3 / 5

private def latticeMajor (n : ℤ) : ℝ := latticeRatio ^ n.natAbs

private def latticeTail (n : ℤ) : ℝ :=
  if 5 ≤ n.natAbs then latticeRatio ^ 25 * latticeRatio ^ (n.natAbs - 5) else 0

private theorem latticeMajor_nonneg (n : ℤ) : 0 ≤ latticeMajor n := by
  unfold latticeMajor latticeRatio
  positivity

private theorem latticeTail_nonneg (n : ℤ) : 0 ≤ latticeTail n := by
  unfold latticeTail latticeRatio
  positivity

private theorem lattice_geometric :
    HasSum (fun n : ℕ ↦ latticeRatio ^ n) (1 - latticeRatio)⁻¹ :=
  hasSum_geometric_of_lt_one (by norm_num [latticeRatio]) (by norm_num [latticeRatio])

private theorem latticeMajor_hasSum : HasSum latticeMajor 4 := by
  have hn : HasSum (fun n : ℕ ↦ latticeMajor (-(n + 1))) (latticeRatio * (1 - latticeRatio)⁻¹) := by
    apply (lattice_geometric.mul_left latticeRatio).congr_fun
    intro n
    rw [latticeMajor, Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_natCast,
      pow_succ']
  have hp : HasSum (fun n : ℕ ↦ latticeMajor n) (1 - latticeRatio)⁻¹ := by
    simpa only [latticeMajor, Int.natAbs_natCast] using lattice_geometric
  convert hp.of_nat_of_neg_add_one hn using 1
  norm_num [latticeRatio]

private theorem latticeTail_delayed_hasSum (k : ℕ) :
    HasSum (fun n : ℕ ↦ if k ≤ n then latticeRatio ^ 25 * latticeRatio ^ (n - k) else 0)
      (latticeRatio ^ 25 * (1 - latticeRatio)⁻¹) := by
  let F := fun n : ℕ ↦ if k ≤ n then latticeRatio ^ 25 * latticeRatio ^ (n - k) else 0
  have hShift : HasSum (fun n : ℕ ↦ F (n + k)) (latticeRatio ^ 25 * (1 - latticeRatio)⁻¹) := by
    simpa only [F, Nat.le_add_left, ite_true, Nat.add_sub_cancel] using
      lattice_geometric.mul_left (latticeRatio ^ 25)
  have hSum := hShift.sum_range_add
  have hZero : (∑ n ∈ range k, F n) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp only [mem_range] at hn
    simp [F, Nat.not_le.mpr hn]
  rwa [hZero, zero_add] at hSum

private theorem latticeTail_hasSum :
    HasSum latticeTail (2 * latticeRatio ^ 25 / (1 - latticeRatio)) := by
  have hp : HasSum (fun n : ℕ ↦ latticeTail n) (latticeRatio ^ 25 * (1 - latticeRatio)⁻¹) := by
    simpa only [latticeTail, Int.natAbs_natCast] using latticeTail_delayed_hasSum 5
  have hn : HasSum (fun n : ℕ ↦ latticeTail (-(n + 1))) (latticeRatio ^ 25 * (1 - latticeRatio)⁻¹) := by
    apply (latticeTail_delayed_hasSum 4).congr_fun
    intro n
    rw [latticeTail, Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_natCast]
    by_cases hb : 4 ≤ n
    · rw [ite_eq_left hb, ite_eq_left (show 5 ≤ n + 1 by omega),
        show n + 1 - 5 = n - 4 by omega]
    · rw [ite_eq_right hb, ite_eq_right (show ¬ 5 ≤ n + 1 by omega)]
  convert hp.of_nat_of_neg_add_one hn using 1
  ring

private theorem latticeProduct_hasSum {f g : ℤ → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) :
    HasSum (fun p : ℤ × ℤ ↦ f p.1 * g p.2) (a * b) := by
  have hfn : Summable fun n ↦ ‖f n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hf.summable
  have hgn : Summable fun n ↦ ‖g n‖ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hg.summable
  rw [← hf.tsum_eq, ← hg.tsum_eq, tsum_mul_tsum_of_summable_norm hfn hgn]
  exact (summable_mul_of_summable_norm hfn hgn).hasSum

private theorem form_positive (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {p : ℤ × ℤ} (hp : p ≠ (0, 0)) :
    1 ≤ Q p.1 p.2 := by
  obtain ⟨m, n⟩ := p
  have hpos : 0 < m ^ 2 + n ^ 2 := by
    by_cases hm : m = 0
    · have hn : n ≠ 0 := by
        intro h
        exact hp (by simp [hm, h])
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hn)
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hm) (sq_nonneg _)
  have h := hQ m n
  change 1 ≤ Q m n
  omega

private theorem normFormTerm_nonneg (Q : ℤ → ℤ → ℤ) {q : ℝ} (hq : 0 ≤ q) (p : ℤ × ℤ) :
    0 ≤ normalizedFormTerm Q q p := by
  unfold normalizedFormTerm
  positivity

private theorem normFormTerm_le (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11)
    (p : ℤ × ℤ) :
    normalizedFormTerm Q q p ≤
      (11 / 3) * (latticeRatio ^ (p.1.natAbs ^ 2) * latticeRatio ^ (p.2.natAbs ^ 2)) := by
  by_cases hp : p = (0, 0)
  · norm_num [normalizedFormTerm, hp]
  rw [normalizedFormTerm, ite_eq_right hp]
  have hpos := form_positive Q hQ hp
  have hexp : (Q p.1 p.2).toNat = (Q p.1 p.2 - 1).toNat + 1 := by omega
  have hle : p.1.natAbs ^ 2 + p.2.natAbs ^ 2 ≤ 2 * (Q p.1 p.2).toNat := by
    apply Int.ofNat_le.mp
    push_cast
    rw [sq_abs, sq_abs, Int.toNat_of_nonneg (by omega : 0 ≤ Q p.1 p.2)]
    exact hQ _ _
  have hr0 : 0 ≤ latticeRatio := by norm_num [latticeRatio]
  have hr1 : latticeRatio ≤ 1 := by norm_num [latticeRatio]
  calc
    _ ≤ (3 / 11 : ℝ) ^ (Q p.1 p.2 - 1).toNat := pow_le_pow_left₀ hq hqu _
    _ = (11 / 3) * (3 / 11 : ℝ) ^ (Q p.1 p.2).toNat := by
      rw [hexp, pow_succ]
      ring
    _ ≤ (11 / 3) * (latticeRatio ^ 2) ^ (Q p.1 p.2).toNat :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num [latticeRatio]) _) (by norm_num)
    _ ≤ _ := by
      rw [← pow_mul, ← pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1 hle) (by norm_num)

private theorem lattice_square_le_major (n : ℤ) :
    latticeRatio ^ (n.natAbs ^ 2) ≤ latticeMajor n := by
  apply pow_le_pow_of_le_one (by norm_num [latticeRatio]) (by norm_num [latticeRatio])
  by_cases hz : n.natAbs = 0
  · simp [hz]
  have h := Nat.mul_le_mul_left n.natAbs (show 1 ≤ n.natAbs by omega)
  simpa only [mul_one, pow_two] using h

private theorem lattice_square_le_tail {n : ℤ} (hn : 5 ≤ n.natAbs) :
    latticeRatio ^ (n.natAbs ^ 2) ≤ latticeTail n := by
  rw [latticeTail, ite_eq_left hn, ← pow_add]
  apply pow_le_pow_of_le_one (by norm_num [latticeRatio]) (by norm_num [latticeRatio])
  have h := Nat.mul_le_mul_left n.natAbs hn
  have h' : 25 + (n.natAbs - 5) ≤ 5 * n.natAbs := by omega
  exact h'.trans (by simpa only [pow_two, mul_comm] using h)

private def latticeTailMajor (p : ℤ × ℤ) : ℝ :=
  (11 / 3) * (latticeTail p.1 * latticeMajor p.2 + latticeMajor p.1 * latticeTail p.2)

private theorem latticeTailMajor_hasSum : HasSum latticeTailMajor ((440 / 3) * (3 / 5) ^ 25) := by
  have h1 := latticeProduct_hasSum latticeTail_hasSum latticeMajor_hasSum
    latticeTail_nonneg latticeMajor_nonneg
  have h2 := latticeProduct_hasSum latticeMajor_hasSum latticeTail_hasSum
    latticeMajor_nonneg latticeTail_nonneg
  have h := (h1.add h2).mul_left (11 / 3)
  unfold latticeTailMajor
  convert h using 1
  norm_num [latticeRatio]

private theorem normFormTerm_le_tailMajor (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11)
    {p : ℤ × ℤ} (hp : p ∉ thetaBox) :
    normalizedFormTerm Q q p ≤ latticeTailMajor p := by
  have hr0 : 0 ≤ latticeRatio := by norm_num [latticeRatio]
  have hout : 5 ≤ p.1.natAbs ∨ 5 ≤ p.2.natAbs := by
    by_contra! h
    apply hp
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega)⟩
  apply (normFormTerm_le Q hQ hq hqu p).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rcases hout with h | h
  · apply le_add_of_le_of_nonneg
    · exact mul_le_mul (lattice_square_le_tail h) (lattice_square_le_major _)
        (pow_nonneg hr0 _) (latticeTail_nonneg _)
    · exact mul_nonneg (latticeMajor_nonneg _) (latticeTail_nonneg _)
  · apply le_add_of_nonneg_of_le
    · exact mul_nonneg (latticeTail_nonneg _) (latticeMajor_nonneg _)
    · exact mul_le_mul (lattice_square_le_major _) (lattice_square_le_tail h)
        (pow_nonneg hr0 _) (latticeMajor_nonneg _)

private theorem normalizedForm_sum_le (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    Summable (normalizedFormTerm Q q) ∧
      (∑' p, normalizedFormTerm Q q p) ≤ (discriminant23ThetaEnvelope Q : ℝ) := by
  let f := normalizedFormTerm Q q
  let fBox := fun p ↦ if p ∈ thetaBox then f p else 0
  have hBox : HasSum fBox (∑ p ∈ thetaBox, f p) := by
    have h : HasSum fBox (∑ p ∈ thetaBox, fBox p) :=
      hasSum_sum_of_ne_finset_zero (fun p hp ↦ by simp [fBox, hp])
    simpa [fBox] using h
  have hM := hBox.add latticeTailMajor_hasSum
  have hPoint (p : ℤ × ℤ) : f p ≤ fBox p + latticeTailMajor p := by
    by_cases hp : p ∈ thetaBox
    · rw [show fBox p = f p by simp [fBox, hp]]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (add_nonneg (mul_nonneg (latticeTail_nonneg _) (latticeMajor_nonneg _))
          (mul_nonneg (latticeMajor_nonneg _) (latticeTail_nonneg _))))
    · simpa [fBox, hp] using normFormTerm_le_tailMajor Q hQ hq hqu hp
  have hs := hM.summable.of_nonneg_of_le (normFormTerm_nonneg Q hq) hPoint
  refine ⟨hs, ?_⟩
  have hFin : (∑ p ∈ thetaBox, f p) ≤
      ((∑ p ∈ thetaBox, normalizedFormTerm Q (3 / 11 : ℚ) p : ℚ) : ℝ) := by
    push_cast
    apply sum_le_sum
    intro p hp
    dsimp only [f, normalizedFormTerm]
    split <;> push_cast
    · rfl
    · exact pow_le_pow_left₀ hq hqu _
  have h := hs.tsum_le_tsum hPoint hM.summable
  rw [hM.tsum_eq] at h
  unfold discriminant23ThetaEnvelope
  push_cast at hFin ⊢
  exact h.trans (add_le_add_left hFin _)

/-- The theta reading for a binary form, with the origin removed. -/
def classThetaStar (Q : ℤ → ℤ → ℤ) (q : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = (0, 0) then 0 else q ^ (Q p.1 p.2).toNat

private theorem classThetaStar_eq {Q : ℤ → ℤ → ℤ}
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) (q : ℝ) :
    classThetaStar Q q = q * ∑' p, normalizedFormTerm Q q p := by
  rw [classThetaStar, ← tsum_mul_left]
  apply tsum_congr
  intro p
  by_cases hp : p = (0, 0)
  · simp [normalizedFormTerm, hp]
  · rw [ite_eq_right hp, normalizedFormTerm, ite_eq_right hp]
    have hpos := form_positive Q hQ hp
    have hexp : (Q p.1 p.2).toNat = (Q p.1 p.2 - 1).toNat + 1 := by omega
    rw [hexp, pow_succ']

theorem discriminant23_classThetaStar_bounds {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    2 * q ≤ classThetaStar discriminant23PrincipalForm q ∧
      classThetaStar discriminant23PrincipalForm q ≤ (21 / 10) * q ∧
      0 ≤ classThetaStar discriminant23OtherForm q ∧
      classThetaStar discriminant23OtherForm q ≤ (3 / 4) * q := by
  have h0 := normalizedForm_sum_le discriminant23PrincipalForm
    discriminant23_principal_form_growth hq hqu
  have h1 := normalizedForm_sum_le discriminant23OtherForm
    discriminant23_other_form_growth hq hqu
  rw [classThetaStar_eq discriminant23_principal_form_growth q,
    classThetaStar_eq discriminant23_other_form_growth q]
  have hLo : (2 : ℝ) ≤ ∑' p, normalizedFormTerm discriminant23PrincipalForm q p := by
    let s : Finset (ℤ × ℤ) := {(1, 0), (-1, 0)}
    have h := h0.1.sum_le_tsum s (fun p _ ↦ normFormTerm_nonneg _ hq p)
    have hf : (∑ p ∈ s, normalizedFormTerm discriminant23PrincipalForm q p) = 2 := by
      simp [s, normalizedFormTerm, discriminant23PrincipalForm]
      norm_num
    exact hf ▸ h
  have hU0 : (discriminant23ThetaEnvelope discriminant23PrincipalForm : ℝ) ≤ 21 / 10 := by
    rw [← show (((21 / 10 : ℚ) : ℝ)) = 21 / 10 by norm_num]
    exact Rat.cast_le.mpr discriminant23_principal_envelope_lt.le
  have hU1 : (discriminant23ThetaEnvelope discriminant23OtherForm : ℝ) ≤ 3 / 4 := by
    rw [← show (((3 / 4 : ℚ) : ℝ)) = 3 / 4 by norm_num]
    exact Rat.cast_le.mpr discriminant23_other_envelope_lt.le
  rw [mul_comm 2 q, mul_comm (21 / 10 : ℝ) q, mul_comm (3 / 4 : ℝ) q]
  exact ⟨mul_le_mul_of_nonneg_left hLo hq, mul_le_mul_of_nonneg_left (h0.2.trans hU0) hq,
    mul_nonneg hq (tsum_nonneg (normFormTerm_nonneg _ hq)),
    mul_le_mul_of_nonneg_left (h1.2.trans hU1) hq⟩

/-- The lattice points used for the finite character reading. -/
def characterThetaBox : Finset (ℤ × ℤ) := (Icc (-5 : ℤ) 5).product (Icc (-5 : ℤ) 5)

def characterThetaTerms (Q : ℤ → ℤ → ℤ) : Finset (ℤ × ℤ) :=
  characterThetaBox.filter (fun p ↦ p ≠ (0, 0) ∧ Q p.1 p.2 ≤ 32)

def classThetaFinite (Q : ℤ → ℤ → ℤ) (q : ℝ) : ℝ :=
  ∑ p ∈ characterThetaTerms Q, q ^ (Q p.1 p.2).toNat

private theorem lattice_square_le_scaled_tail {n : ℤ} (hn : 6 ≤ n.natAbs) :
    latticeRatio ^ (n.natAbs ^ 2) ≤ latticeRatio ^ 10 * latticeTail n := by
  rw [latticeTail, ite_eq_left (show 5 ≤ n.natAbs by omega), ← pow_add, ← pow_add]
  apply pow_le_pow_of_le_one (by norm_num [latticeRatio]) (by norm_num [latticeRatio])
  have hmul := Nat.mul_le_mul_left n.natAbs hn
  rw [pow_two]
  omega

private theorem normFormTerm_le_scaled_tail (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11)
    {p : ℤ × ℤ} (hp : p ∉ characterThetaBox) :
    normalizedFormTerm Q q p ≤ latticeRatio ^ 10 * latticeTailMajor p := by
  have hr0 : 0 ≤ latticeRatio := by norm_num [latticeRatio]
  have hout : 6 ≤ p.1.natAbs ∨ 6 ≤ p.2.natAbs := by
    by_contra! h
    apply hp
    exact mem_product.mpr ⟨mem_Icc.mpr (by omega), mem_Icc.mpr (by omega)⟩
  apply (normFormTerm_le Q hQ hq hqu p).trans
  rw [latticeTailMajor, mul_left_comm (latticeRatio ^ 10) (11 / 3 : ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rcases hout with h | h
  · calc
      _ ≤ (latticeRatio ^ 10 * latticeTail p.1) * latticeMajor p.2 :=
        mul_le_mul (lattice_square_le_scaled_tail h) (lattice_square_le_major _)
          (pow_nonneg hr0 _) (mul_nonneg (pow_nonneg hr0 _) (latticeTail_nonneg _))
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg (latticeMajor_nonneg _) (latticeTail_nonneg _)))
          (pow_nonneg hr0 _)
  · calc
      _ ≤ latticeMajor p.1 * (latticeRatio ^ 10 * latticeTail p.2) :=
        mul_le_mul (lattice_square_le_major _) (lattice_square_le_scaled_tail h)
          (pow_nonneg hr0 _) (latticeMajor_nonneg _)
      _ ≤ _ := by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (mul_nonneg (latticeTail_nonneg _) (latticeMajor_nonneg _)))
          (pow_nonneg hr0 _)

private theorem classThetaFinite_eq (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) (q : ℝ) :
    classThetaFinite Q q = q * ∑ p ∈ characterThetaTerms Q, normalizedFormTerm Q q p := by
  rw [classThetaFinite, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hp₀ := ((mem_filter.mp hp).2).1
  have hpos := form_positive Q hQ hp₀
  have hexp : (Q p.1 p.2).toNat = (Q p.1 p.2 - 1).toNat + 1 := by omega
  rw [normalizedFormTerm, ite_eq_right hp₀, hexp, pow_succ']

/-- A finite norm sum with a uniform theta remainder. The estimate uses the
same lattice majorant as the full theta envelope. -/
theorem classThetaStar_sub_finite_bounds (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    0 ≤ classThetaStar Q q - classThetaFinite Q q ∧
      classThetaStar Q q - classThetaFinite Q q ≤ q / 100000 := by
  let f := normalizedFormTerm Q q
  let terms := characterThetaTerms Q
  let g (p : ℤ × ℤ) := if p ∈ terms then f p else 0
  let small (p : ℤ × ℤ) : ℝ := if p ∈ characterThetaBox then (3 / 11 : ℝ) ^ 32 else 0
  let scale := latticeRatio ^ 10
  have hscale : 0 ≤ scale := by norm_num [scale, latticeRatio]
  have hsF : Summable f := (normalizedForm_sum_le Q hQ hq hqu).1
  have hsG : HasSum g (∑ p ∈ terms, f p) := by
    have h : HasSum g (∑ p ∈ terms, g p) :=
      hasSum_sum_of_ne_finset_zero (fun p hp ↦ by simp [g, hp])
    simpa [g] using h
  have hsmallCard : characterThetaBox.card = 121 := by decide +kernel
  have hsSmall : HasSum small (121 * (3 / 11 : ℝ) ^ 32) := by
    have h : HasSum small (∑ p ∈ characterThetaBox, small p) :=
      hasSum_sum_of_ne_finset_zero (fun p hp ↦ by simp [small, hp])
    simpa [small, hsmallCard] using h
  have hsMajor := (latticeTailMajor_hasSum.mul_left scale).add hsSmall
  have hTail0 (p : ℤ × ℤ) : 0 ≤ scale * latticeTailMajor p :=
    mul_nonneg hscale (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (latticeTail_nonneg _) (latticeMajor_nonneg _))
        (mul_nonneg (latticeMajor_nonneg _) (latticeTail_nonneg _))))
  have hgNonneg (p : ℤ × ℤ) : 0 ≤ f p - g p := by
    by_cases hp : p ∈ terms
    · simp [g, hp]
    · simpa [g, hp] using normFormTerm_nonneg Q hq p
  have hpoint (p : ℤ × ℤ) : f p - g p ≤ scale * latticeTailMajor p + small p := by
    by_cases hp : p ∈ terms
    · simp only [g, ite_eq_left hp, sub_self]
      exact add_nonneg (hTail0 p) (by dsimp [small]; positivity)
    rw [show g p = 0 by simp [g, hp], sub_zero]
    by_cases hb : p ∈ characterThetaBox
    · rw [show small p = (3 / 11 : ℝ) ^ 32 by simp [small, hb]]
      apply le_add_of_nonneg_of_le (hTail0 p)
      by_cases hz : p = (0, 0)
      · simp [f, normalizedFormTerm, hz]
        positivity
      have hQp : 32 < Q p.1 p.2 := by
        by_contra! h
        exact hp (mem_filter.mpr ⟨hb, hz, h⟩)
      change normalizedFormTerm Q q p ≤ (3 / 11 : ℝ) ^ 32
      rw [normalizedFormTerm, ite_eq_right hz]
      exact (pow_le_pow_left₀ hq hqu _).trans
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
    · rw [show small p = 0 by simp [small, hb], add_zero]
      exact normFormTerm_le_scaled_tail Q hQ hq hqu hb
  have hsRem := hsF.sub hsG.summable
  have hrem : (∑' p, (f p - g p)) ≤ 1 / (100000 : ℝ) := by
    calc
      _ ≤ ∑' p, (scale * latticeTailMajor p + small p) :=
        hsRem.tsum_le_tsum hpoint hsMajor.summable
      _ = _ := hsMajor.tsum_eq
      _ ≤ _ := by norm_num [scale, latticeRatio]
  have hExact : classThetaStar Q q - classThetaFinite Q q =
      q * ∑' p, (f p - g p) := by
    rw [classThetaStar_eq hQ, classThetaFinite_eq Q hQ, hsF.tsum_sub hsG.summable,
      hsG.tsum_eq, mul_sub]
  rw [hExact, div_eq_mul_inv]
  exact ⟨mul_nonneg hq (tsum_nonneg hgNonneg),
    mul_le_mul_of_nonneg_left (by simpa only [one_div] using hrem) hq⟩


/-- For forms of this growth, every omitted norm is at least 33. Peeling off
23 heat powers leaves a summable lattice majorant of mass 16. -/
theorem classThetaStar_sub_finite_bounds_sharp (Q : ℤ → ℤ → ℤ)
    (hQ : ∀ m n, 9 * (m ^ 2 + n ^ 2) ≤ 10 * Q m n)
    {q : ℝ} (hq : 0 ≤ q) (hqu : q ≤ 3 / 11) :
    0 ≤ classThetaStar Q q - classThetaFinite Q q ∧
      classThetaStar Q q - classThetaFinite Q q ≤ 16 * q ^ 23 := by
  have hWeak (m n : ℤ) : m ^ 2 + n ^ 2 ≤ 2 * Q m n := by
    have h := hQ m n
    have hm := sq_nonneg m
    have hn := sq_nonneg n
    omega
  let f := normalizedFormTerm Q q
  let terms := characterThetaTerms Q
  let g (p : ℤ × ℤ) := if p ∈ terms then f p else 0
  have hsF : Summable f := (normalizedForm_sum_le Q hWeak hq hqu).1
  have hsG : HasSum g (∑ p ∈ terms, f p) := by
    have h : HasSum g (∑ p ∈ terms, g p) :=
      hasSum_sum_of_ne_finset_zero (fun p hp ↦ by simp [g, hp])
    simpa [g] using h
  have hsMajor := (latticeProduct_hasSum latticeMajor_hasSum latticeMajor_hasSum
    latticeMajor_nonneg latticeMajor_nonneg).mul_left (q ^ 22)
  have hgNonneg (p : ℤ × ℤ) : 0 ≤ f p - g p := by
    by_cases hp : p ∈ terms
    · simp [g, hp]
    · simpa [g, hp] using normFormTerm_nonneg Q hq p
  have hpoint (p : ℤ × ℤ) : f p - g p ≤ q ^ 22 * (latticeMajor p.1 * latticeMajor p.2) := by
    by_cases hp : p ∈ terms
    · simp only [g, ite_eq_left hp, sub_self]
      unfold latticeMajor latticeRatio
      positivity
    rw [show g p = 0 by simp [g, hp], sub_zero]
    by_cases hz : p = (0, 0)
    · simp only [f, normalizedFormTerm, ite_eq_left hz]
      unfold latticeMajor latticeRatio
      positivity
    have hpos := form_positive Q hWeak hz
    have hSquares : 9 * (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) ≤ 10 * (Q p.1 p.2).toNat := by
      apply Int.ofNat_le.mp
      push_cast
      rw [sq_abs, sq_abs, Int.toNat_of_nonneg (by omega : 0 ≤ Q p.1 p.2)]
      exact hQ _ _
    have hQp : 33 ≤ (Q p.1 p.2).toNat := by
      by_cases hb : p ∈ characterThetaBox
      · have hgt : 32 < Q p.1 p.2 := by
          by_contra! h
          exact hp (mem_filter.mpr ⟨hb, hz, h⟩)
        omega
      · have hout : 6 ≤ p.1.natAbs ∨ 6 ≤ p.2.natAbs := by
          by_contra! h
          exact hb (mem_product.mpr ⟨mem_Icc.mpr (by omega), mem_Icc.mpr (by omega)⟩)
        rcases hout with h | h
        · have ht : 36 ≤ p.1.natAbs ^ 2 := pow_le_pow_left' h 2
          omega
        · have ht : 36 ≤ p.2.natAbs ^ 2 := pow_le_pow_left' h 2
          omega
    have habs (n : ℕ) : 2 * n ≤ n ^ 2 + 1 := by
      apply Int.ofNat_le.mp
      push_cast
      nlinarith only [sq_nonneg ((n : ℤ) - 1)]
    have hExp : p.1.natAbs + p.2.natAbs ≤ 2 * ((Q p.1 p.2).toNat - 23) := by
      have h₁ := habs p.1.natAbs
      have h₂ := habs p.2.natAbs
      omega
    change normalizedFormTerm Q q p ≤ _
    rw [normalizedFormTerm, ite_eq_right hz,
      show (Q p.1 p.2 - 1).toNat = 22 + ((Q p.1 p.2).toNat - 23) by omega, pow_add]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
    calc
      _ ≤ (latticeRatio ^ 2) ^ ((Q p.1 p.2).toNat - 23) :=
        pow_le_pow_left₀ hq (hqu.trans (by norm_num [latticeRatio])) _
      _ ≤ latticeMajor p.1 * latticeMajor p.2 := by
        unfold latticeMajor
        rw [← pow_mul, ← pow_add]
        exact pow_le_pow_of_le_one (by norm_num [latticeRatio]) (by norm_num [latticeRatio]) hExp
  have hsRem := hsF.sub hsG.summable
  have hrem := (hsRem.tsum_le_tsum hpoint hsMajor.summable).trans_eq hsMajor.tsum_eq
  have hExact : classThetaStar Q q - classThetaFinite Q q = q * ∑' p, (f p - g p) := by
    rw [classThetaStar_eq hWeak, classThetaFinite_eq Q hWeak, hsF.tsum_sub hsG.summable,
      hsG.tsum_eq, mul_sub]
  rw [hExact]
  refine ⟨mul_nonneg hq (tsum_nonneg hgNonneg), ?_⟩
  calc
    _ ≤ q * (q ^ 22 * (4 * 4)) := mul_le_mul_of_nonneg_left hrem hq
    _ = _ := by ring

#print axioms classThetaStar_sub_finite_bounds_sharp
#print axioms discriminant23_principal_envelope_lt
#print axioms discriminant23_other_envelope_lt
#print axioms discriminant23_thetaScale_interval
#print axioms discriminant23_thetaExp_interval
#print axioms discriminant23_classThetaStar_bounds
#print axioms classThetaStar_sub_finite_bounds

end
end FieldTarget
