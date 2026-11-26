import GaussianPrimeCenter

/-! Read the outward-rounded numerical table on the original prime ramp.
The finite integer comparisons and the interpolation are checked here.
Association of the numerical enclosures with the ramp is an explicit input. -/

namespace AlpogeSuperZeta

open Finset Set
open scoped Classical

noncomputable section

private def archivedPrimeMeshPoint (j : ℕ) : ℝ :=
  1000000 + 10000 * (j : ℝ)

-- Columns are the two sample endpoints and the preceding cell's two errors.
-- Every entry has denominator 100. The replay JSON uses the same order.
private def archivedPrimeMeshTable : Array (ℕ × ℕ × ℕ × ℕ) := #[
  (91534, 92384, 0, 0),
  (91481, 92339, 661, 743),
  (91792, 92658, 675, 689),
  (92468, 93343, 608, 683),
  (92897, 93781, 543, 522),
  (93495, 94388, 677, 644),
  (93819, 94720, 658, 579),
  (93471, 94381, 672, 476),
  (92854, 93772, 543, 588),
  (92071, 92997, 615, 481),
  (91195, 92130, 623, 724),
  (90266, 91209, 611, 492),
  (89057, 90008, 594, 519),
  (87780, 88740, 514, 613),
  (86813, 87782, 510, 529),
  (85766, 86743, 482, 500),
  (85286, 86271, 514, 647),
  (84760, 85754, 552, 534),
  (84024, 85027, 607, 464),
  (82952, 83963, 591, 520),
  (81793, 82812, 527, 545),
  (80578, 81606, 454, 512),
  (79397, 80433, 612, 502),
  (77766, 78811, 618, 453),
  (75579, 76632, 523, 500),
  (73403, 74465, 440, 524),
  (72025, 73095, 414, 543),
  (70367, 71446, 573, 495),
  (68717, 69804, 497, 513),
  (67087, 68183, 493, 455),
  (65187, 66291, 533, 468),
  (63272, 64385, 459, 481),
  (61406, 62528, 402, 504),
  (60065, 61195, 458, 511),
  (58866, 60004, 397, 423),
  (57792, 58939, 462, 467),
  (56708, 57863, 485, 469),
  (55511, 56675, 414, 373),
  (54048, 55220, 453, 427),
  (52762, 53943, 399, 496),
  (52103, 53292, 345, 579),
  (51970, 53167, 408, 403),
  (51721, 52927, 446, 406),
  (51304, 52519, 468, 423),
  (50810, 52034, 425, 440),
  (50404, 51636, 349, 403),
  (50126, 51366, 503, 464),
  (49517, 50766, 456, 417),
  (49056, 50313, 424, 439),
  (48459, 49725, 426, 383),
  (47602, 48876, 452, 400),
  (46664, 47947, 454, 407),
  (45565, 46856, 400, 381),
  (44319, 45618, 425, 383),
  (43170, 44478, 390, 395),
  (42096, 43413, 342, 439),
  (41162, 42487, 340, 363),
  (40360, 41694, 401, 392),
  (39689, 41031, 390, 431),
  (39163, 40514, 338, 379),
  (38375, 39734, 475, 341),
  (37354, 38722, 410, 463),
  (36518, 37894, 377, 412),
  (35914, 37299, 410, 414),
  (35345, 36738, 390, 416),
  (34730, 36132, 388, 370),
  (33947, 35357, 399, 342),
  (33095, 34514, 358, 392),
  (32526, 33952, 334, 433),
  (32276, 33711, 332, 371),
  (31994, 33437, 441, 411),
  (31536, 32988, 346, 303),
  (31092, 32553, 390, 381),
  (30598, 32067, 334, 342),
  (30293, 31770, 340, 398),
  (30008, 31495, 359, 355),
  (29663, 31158, 369, 345),
  (29481, 30984, 335, 416),
  (29190, 30702, 369, 321),
  (28972, 30492, 331, 339),
  (28987, 30515, 305, 382),
  (28874, 30412, 431, 328),
  (28515, 30060, 330, 286),
  (27996, 29550, 376, 360),
  (27256, 28819, 382, 299),
  (26560, 28132, 329, 407),
  (26061, 27641, 288, 327),
  (25524, 27112, 333, 318),
  (25146, 26742, 305, 351),
  (24845, 26450, 346, 349),
  (24508, 26122, 370, 344),
  (24123, 25745, 316, 308),
  (23507, 25138, 337, 295),
  (22744, 24384, 358, 294),
  (21852, 23500, 318, 300),
  (20983, 22639, 317, 343),
  (20221, 21886, 338, 319),
  (19328, 21001, 336, 288),
  (18170, 19851, 327, 294),
  (16869, 18559, 348, 300),
  (15516, 17214, 335, 295)
]

private def archRow (j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  archivedPrimeMeshTable.getD j (0, 0, 0, 0)

private def archLo (j : ℕ) : ℕ := (archRow j).1
private def archHi (j : ℕ) : ℕ := (archRow j).2.1
private def archUp (j : ℕ) : ℕ := (archRow j).2.2.1
private def archDown (j : ℕ) : ℕ := (archRow j).2.2.2

private def archHigh (j : ℕ) : ℕ :=
  max (archHi j) (archHi (j + 1)) + archUp (j + 1)

/-- Every rounded cell in the released table satisfies the claimed limits. -/
theorem archivedPrimeMesh_integer_checks :
    ∀ j : Fin 100,
      15200 + archDown (j.val + 1) < min (archLo j.val) (archLo (j.val + 1)) ∧
      archHigh j.val < 95400 ∧
      10^6 * archHigh j.val ^ 2 < 933^2 * 10^4 * (1000000 + 10000*j.val) := by
  decide +kernel

private def positiveSlopeMass (l r : ℝ) : ℝ :=
  ∑ p ∈ range (⌊r⌋₊ + 1),
    if (p : ℝ) ∈ Ioo l r then max (archivedGaussianPrimeSlope p) 0 else 0

private theorem archivedPrimeMesh_lower {l r x : ℝ}
    (hl : 0 ≤ l) (hlr : l < r) (hx : x ∈ Icc l r) :
    gaussianPrimeCellChord archivedGaussianPrimeOnlyRamp l r x -
      (r - l) / 4 * positiveSlopeMass l r ≤ archivedGaussianPrimeOnlyRamp x := by
  refine sub_le_comm.mp ?_
  rw [archivedGaussianPrimeCellChord_gap hl hlr hx]
  unfold positiveSlopeMass
  rw [mul_sum]
  apply sum_le_sum
  intro p _
  by_cases hp : (p : ℝ) ∈ Ioo l r
  · rw [if_pos hp, mul_comm ((r - l) / 4)]
    obtain ⟨ht₀, ht₁, ht₂⟩ := gaussianPrimeCellTent_bounds hlr hx p
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) ht₀).trans
      (mul_le_mul_of_nonneg_left (ht₁.trans ht₂) (le_max_right _ _))
  · simp [hp, gaussianPrimeCellTent]

private theorem archivedPrimeMesh_upper {l r x : ℝ}
    (hl : 0 ≤ l) (hlr : l < r) (hx : x ∈ Icc l r) :
    archivedGaussianPrimeOnlyRamp x ≤
      gaussianPrimeCellChord archivedGaussianPrimeOnlyRamp l r x +
        (r - l) / 4 * archivedGaussianPrimeCellNegativeMass l r := by
  refine (archivedGaussianPrimeCellChord_upper hl hlr hx).trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_right (gaussianPrimeCellTent_bounds hlr hx l).2.2
    (archivedGaussianPrimeCellNegativeMass_nonneg l r)

private theorem archivedPrimeMesh_covers {x : ℝ} (hx : x ∈ Icc (1000000 : ℝ) 2000000) :
    ∃ j : Fin 100, x ∈ Icc (archivedPrimeMeshPoint j.val)
      (archivedPrimeMeshPoint (j.val + 1)) := by
  let y : ℝ := (x - 1000000) / 10000
  have hy : 0 ≤ y := by dsimp [y]; linarith [hx.1]
  have hy₁ : y ≤ 100 := by dsimp [y]; linarith [hx.2]
  let n : ℕ := min ⌊y⌋₊ 99
  refine ⟨⟨n, (min_le_right _ _).trans_lt (by decide)⟩, ?_⟩
  have h₀ : (n : ℝ) ≤ y :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hy)
  have h₁ : y ≤ (n : ℝ) + 1 := by
    by_cases h : ⌊y⌋₊ ≤ 99
    · simpa only [n, min_eq_left h] using (Nat.lt_floor_add_one y).le
    · simpa only [n, min_eq_right (le_of_not_ge h), Nat.cast_ofNat, show (99 : ℝ) + 1 = 100 by norm_num]
        using hy₁
  change archivedPrimeMeshPoint n ≤ x ∧ x ≤ archivedPrimeMeshPoint (n + 1)
  simp only [archivedPrimeMeshPoint, Nat.cast_add, Nat.cast_one]
  dsimp [y] at h₀ h₁
  constructor <;> linarith

/-- Outward numerical enclosures for the fixed archived mesh. -/
structure ArchivedPrimeMeshEnclosures : Prop where
  value : ∀ j : Fin 101,
    (archLo j.val : ℝ) / 100 ≤ archivedGaussianPrimeOnlyRamp (archivedPrimeMeshPoint j.val) ∧
    archivedGaussianPrimeOnlyRamp (archivedPrimeMeshPoint j.val) ≤ (archHi j.val : ℝ) / 100
  error : ∀ j : Fin 100,
    let l := archivedPrimeMeshPoint j.val
    let r := archivedPrimeMeshPoint (j.val + 1)
    (r - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ (archUp (j.val + 1) : ℝ) / 100 ∧
    (r - l) / 4 * positiveSlopeMass l r ≤ (archDown (j.val + 1) : ℝ) / 100

theorem archivedGaussianPrimeMesh_million_window (h : ArchivedPrimeMeshEnclosures)
    {x : ℝ} (hx : x ∈ Icc (1000000 : ℝ) 2000000) :
    152 < archivedGaussianPrimeOnlyRamp x ∧
      archivedGaussianPrimeOnlyRamp x < 954 ∧
      archivedGaussianPrimeOnlyRamp x < (933 / 1000 : ℝ) * Real.sqrt x := by
  obtain ⟨j, hcell⟩ := archivedPrimeMesh_covers hx
  let l := archivedPrimeMeshPoint j.val
  let r := archivedPrimeMeshPoint (j.val + 1)
  have hl : 0 ≤ l := by dsimp [l, archivedPrimeMeshPoint]; positivity
  have hlr : l < r := by dsimp [l, r, archivedPrimeMeshPoint]; push_cast; linarith
  let f := archivedGaussianPrimeOnlyRamp
  let lo := ((min (archLo j.val) (archLo (j.val + 1)) : ℕ) : ℝ) / 100
  let hi := ((max (archHi j.val) (archHi (j.val + 1)) : ℕ) : ℝ) / 100
  let upper := (archUp (j.val + 1) : ℝ) / 100
  let lower := (archDown (j.val + 1) : ℝ) / 100
  have ha := h.value j.castSucc
  have hb := h.value j.succ
  change (archLo j.val : ℝ) / 100 ≤ f l ∧ f l ≤ (archHi j.val : ℝ) / 100 at ha
  change (archLo (j.val + 1) : ℝ) / 100 ≤ f r ∧ f r ≤ (archHi (j.val + 1) : ℝ) / 100 at hb
  have hloₗ : lo ≤ f l :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (min_le_left (archLo j.val)
      (archLo (j.val + 1)))) (by norm_num)).trans ha.1
  have hloᵣ : lo ≤ f r :=
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (min_le_right (archLo j.val)
      (archLo (j.val + 1)))) (by norm_num)).trans hb.1
  have hhiₗ : f l ≤ hi := ha.2.trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_left (archHi j.val)
      (archHi (j.val + 1)))) (by norm_num))
  have hhiᵣ : f r ≤ hi := hb.2.trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (le_max_right (archHi j.val)
      (archHi (j.val + 1)))) (by norm_num))
  let a := (r - x) / (r - l)
  let b := (x - l) / (r - l)
  have hden := sub_pos.mpr hlr
  have ha₀ : 0 ≤ a := div_nonneg (sub_nonneg.mpr hcell.2) hden.le
  have hb₀ : 0 ≤ b := div_nonneg (sub_nonneg.mpr hcell.1) hden.le
  have hab : a + b = 1 := by dsimp [a, b]; rw [← add_div]; field_simp [hden.ne']; ring
  have hloChord : lo ≤ gaussianPrimeCellChord f l r x := by
    change lo ≤ a * f l + b * f r
    calc
      _ = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hloₗ ha₀)
        (mul_le_mul_of_nonneg_left hloᵣ hb₀)
  have hhiChord : gaussianPrimeCellChord f l r x ≤ hi := by
    change a * f l + b * f r ≤ hi
    calc
      _ ≤ a * hi + b * hi := add_le_add (mul_le_mul_of_nonneg_left hhiₗ ha₀)
        (mul_le_mul_of_nonneg_left hhiᵣ hb₀)
      _ = _ := by rw [← add_mul, hab, one_mul]
  have he := h.error j
  change (r - l) / 4 * archivedGaussianPrimeCellNegativeMass l r ≤ upper ∧
    (r - l) / 4 * positiveSlopeMass l r ≤ lower at he
  have hUpper : f x ≤ hi + upper :=
    (archivedPrimeMesh_upper hl hlr hcell).trans (add_le_add hhiChord he.1)
  have hLower : lo - lower ≤ f x :=
    (sub_le_sub hloChord he.2).trans (archivedPrimeMesh_lower hl hlr hcell)
  obtain ⟨hIlo, hIhi, hIsq⟩ := archivedPrimeMesh_integer_checks j
  have hloR : (15200 : ℝ) + archDown (j.val + 1) <
      (min (archLo j.val) (archLo (j.val + 1)) : ℕ) := by exact_mod_cast hIlo
  have hhiR : (archHigh j.val : ℝ) < 95400 := by exact_mod_cast hIhi
  have hT : hi + upper = (archHigh j.val : ℝ) / 100 := by
    simp only [hi, upper, archHigh, Nat.cast_add]
    ring
  refine ⟨lt_of_lt_of_le ?_ hLower, lt_of_le_of_lt hUpper ?_, ?_⟩
  · dsimp [lo, lower]
    linarith
  · rw [hT]
    linarith
  · apply lt_of_le_of_lt hUpper
    rw [hT]
    have hs : (10 : ℝ)^6 * (archHigh j.val : ℝ)^2 <
        933^2 * 10^4 * l := by
      dsimp [l, archivedPrimeMeshPoint]
      exact_mod_cast hIsq
    have hS : ((933 / 1000 : ℝ) * Real.sqrt l)^2 = (933 / 1000 : ℝ)^2 * l := by
      rw [mul_pow, Real.sq_sqrt hl]
    have ht : (archHigh j.val : ℝ) / 100 < (933 / 1000 : ℝ) * Real.sqrt l := by
      apply (sq_lt_sq₀ (by positivity) (by positivity)).mp
      rw [hS]
      nlinarith only [hs]
    exact ht.trans_le (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcell.1) (by norm_num))

#check archivedGaussianPrimeMesh_million_window
#print axioms archivedPrimeMesh_integer_checks
#print axioms archivedGaussianPrimeMesh_million_window

end
end AlpogeSuperZeta
