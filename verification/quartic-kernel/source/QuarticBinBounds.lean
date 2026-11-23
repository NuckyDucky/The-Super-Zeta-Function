import QuarticShellArray
import QuarticFixed
import QuarticCellBounds

open QuarticFixed

namespace QuarticKernel

def binBounds (b : Box) : ℕ → List ShellBin → ℕ × ℕ
  | _, [] => (0,0)
  | n, g :: gs =>
    let tail := binBounds b (n+g.width) gs
    (g.weight * (powBox b 26 (n+g.width)).lo + tail.1,
      g.weight * (powBox b 26 (n+1)).hi + tail.2)

private theorem binBounds_sound {b : Box} {r : ℝ} (hb : Contains b r)
    (hr : 0 ≤ r) (hr' : r ≤ 1) (n : ℕ) (gs : List ShellBin)
    (hc : BinsCorrect n gs) (hN : n+binCount gs ≤ 33554432)
    (positive : ∀ j, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) :
    ((binBounds b n gs).1 : ℝ)/precision ≤
      (∑ j ∈ Finset.range (binCount gs), (prefixSum (n+j+1):ℝ)*r^(n+j+1)) ∧
    (∑ j ∈ Finset.range (binCount gs), (prefixSum (n+j+1):ℝ)*r^(n+j+1)) ≤
      ((binBounds b n gs).2 : ℝ)/precision := by
  induction gs generalizing n with
  | nil => simp [binBounds, binCount]
  | cons g gs ih =>
    obtain ⟨hw, hwgt, htail⟩ := hc
    have hh : n+g.width + binCount gs ≤ 33554432 := by simpa [binCount, Nat.add_assoc] using hN
    have hN₁ : n+g.width ≤ 33554432 := by omega
    have hN₂ : n+1 ≤ 33554432 := by omega
    obtain ⟨htl, hth⟩ := ih (n+g.width) htail hh
    have hpL := contains_lo (powBox_spec hb 26 (n+g.width) (by norm_num; omega))
    have hpU := contains_hi (powBox_spec hb 26 (n+1) (by norm_num; omega))
    have hsum : (g.weight:ℝ) =
        ∑ i ∈ Finset.range g.width, (prefixSum (n+i+1):ℝ) := by exact_mod_cast hwgt
    have hbin (j : ℕ) (hj : j ∈ Finset.range g.width) : 0 ≤ (prefixSum (n+j+1):ℝ) := by
      have hj' := Finset.mem_range.mp hj
      exact_mod_cast (show 0 ≤ prefixSum (n+j+1) from le_trans (by decide) (positive _ (by omega) (by omega)))
    have ha : (g.weight:ℝ)*r^(n+g.width) ≤
        ∑ j ∈ Finset.range g.width, (prefixSum (n+j+1):ℝ)*r^(n+j+1) := by
      rw [hsum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr' (by omega)) (hbin j hj)
    have hh' : (∑ j ∈ Finset.range g.width, (prefixSum (n+j+1):ℝ)*r^(n+j+1)) ≤
        (g.weight:ℝ)*r^(n+1) := by
      rw [hsum, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr' (by omega)) (hbin j hj)
    simp only [binCount, Finset.sum_range_add, binBounds, Nat.cast_add, Nat.cast_mul, add_div]
    have hreindex (j : ℕ) : n+(g.width+j)+1 = (n+g.width)+j+1 := by omega
    simp_rw [hreindex]
    constructor
    · apply add_le_add _ htl
      rw [mul_div_assoc]
      exact (mul_le_mul_of_nonneg_left hpL (by positivity)).trans ha
    · apply add_le_add _ hth
      rw [mul_div_assoc]
      exact hh'.trans (mul_le_mul_of_nonneg_left hpU (by positivity))

def thetaBox (b : Box) (gs : List ShellBin) : ℚ × ℚ :=
  let rl : ℚ := b.lo / precision
  let rh : ℚ := b.hi / precision
  let v := binBounds b 0 gs
  let rn := powBox b 26 33554432
  let tail := 2 * ((powBox b 26 33554433).hi : ℚ)/precision * (33554433 + rh/(1-rh))
  ((1-rh)*(v.1 / precision) + 17505*(rn.lo / precision) - tail,
    (1-rl)*(v.2 / precision) + 17505*(rn.hi / precision) + tail)

theorem thetaBox_sound {b : Box} {u : ℝ} (hu : 0 < u) (hb : Contains b (Real.exp (-u)))
    (hi : (b.hi:ℚ)/precision < 1) (gs : List ShellBin) (hcount : binCount gs = 33554431)
    (hgs : BinsCorrect 0 gs) (hfinal : prefixSum 33554432 = 17505)
    (positive : ∀ j, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) :
    ((thetaBox b gs).1 : ℝ) ≤ theta u ∧ theta u ≤ ((thetaBox b gs).2 : ℝ) := by
  let r := Real.exp (-u)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hRh : (b.hi:ℝ)/precision < 1 := by
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_one] using (Rat.cast_lt (K := ℝ)).mpr hi
  have hb' := binBounds_sound hb hr.le hr'.le 0 gs hgs (by simp [hcount]) positive
  simp only [hcount, zero_add] at hb'
  change _ ≤ headBins 33554431 r ∧ headBins 33554431 r ≤ _ at hb'
  have hdl := mul_le_mul (sub_le_sub_left (contains_hi hb) _) hb'.1 (by positivity)
    (sub_nonneg.mpr hr'.le)
  have hdu := mul_le_mul (sub_le_sub_left (contains_lo hb) _) hb'.2 (by
    exact (by positivity : 0 ≤ ((binBounds b 0 gs).1:ℝ)/precision).trans hb'.1)
    (sub_nonneg.mpr ((contains_lo hb).trans hr'.le))
  have hN := powBox_spec hb 26 33554432 (by decide)
  have hNL := contains_lo hN
  have hNU := contains_hi hN
  have hTU := contains_hi (powBox_spec hb 26 33554433 (by decide))
  have hq : r/(1-r) ≤ ((b.hi:ℝ)/precision)/(1-(b.hi:ℝ)/precision) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hr') (sub_pos.mpr hRh)).mpr
    nlinarith only [contains_hi hb]
  have hcoeff : 0 ≤ (33554433:ℝ)+r/(1-r) :=
    add_nonneg (by norm_num) (div_nonneg hr.le (sub_pos.mpr hr').le)
  have htb : 2*r^33554433*((33554433:ℝ)+r/(1-r)) ≤
      2*((powBox b 26 33554433).hi:ℝ)/precision*(33554433+((b.hi:ℝ)/precision)/(1-(b.hi:ℝ)/precision)) := by
    apply mul_le_mul
    · nlinarith only [hTU]
    · linarith only [hq]
    · exact hcoeff
    · positivity
  have htheta := theta_head_and_tail 33554431 hu
  change theta u = (1-r)*headBins 33554431 r + (prefixSum 33554432:ℝ)*r^33554432 +
    ∑' i : ℕ, (coeff (33554433+i):ℝ)*r^(33554433+i) at htheta
  rw [hfinal, Int.cast_ofNat] at htheta
  have ht := theta_tail_abs 33554432 hr hr'
  change _ ≤ 2*r^33554433*((33554432:ℝ)+1+r/(1-r)) at ht
  rw [show (33554432:ℝ)+1 = 33554433 by norm_num] at ht
  have ht' := abs_le.mp (ht.trans htb)
  have hnl := mul_le_mul_of_nonneg_left hNL (by norm_num : (0:ℝ) ≤ 17505)
  have hnu := mul_le_mul_of_nonneg_left hNU (by norm_num : (0:ℝ) ≤ 17505)
  constructor <;> simp only [thetaBox, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
  · linarith only [htheta, hdl, hnl, ht'.1]
  · linarith only [htheta, hdu, hnu, ht'.2]

#print axioms thetaBox_sound

end QuarticKernel
