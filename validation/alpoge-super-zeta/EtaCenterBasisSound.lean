import EtaCenterFixed
import EtaEulerContourBounds
import MellinFixedLog
import MellinFixedElementary

/-! The fixed-point intervals enclose the exact exponential basis and its derivative. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

def EtaContains (b : EtaBounds) (z dz : ℂ) : Prop :=
  Contains b.valueRe z.re ∧ Contains b.valueIm z.im ∧
    Contains b.slopeRe dz.re ∧ Contains b.slopeIm dz.im

theorem eta_add_contains {p q : EtaBounds} {z dz w dw : ℂ}
    (hp : EtaContains p z dz) (hq : EtaContains q w dw) :
    EtaContains (addEta p q) (z+w) (dz+dw) :=
  ⟨add_contains hp.1 hq.1, add_contains hp.2.1 hq.2.1,
    add_contains hp.2.2.1 hq.2.2.1, add_contains hp.2.2.2 hq.2.2.2⟩

theorem eta_scale_contains {a : Box} {t : ℝ} {p : EtaBounds} {z dz : ℂ}
    (ha : Contains a t) (hp : EtaContains p z dz) :
    EtaContains (scaleEta a p) ((t:ℂ)*z) ((t:ℂ)*dz) := by
  simpa only [EtaContains, scaleEta, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] using
    And.intro (mul_contains ha hp.1)
      (And.intro (mul_contains ha hp.2.1)
        (And.intro (mul_contains ha hp.2.2.1) (mul_contains ha hp.2.2.2)))

theorem eta_zero_contains : EtaContains zeroEta 0 0 := by
  simp only [EtaContains, zeroEta, Complex.zero_re, Complex.zero_im]
  have h : Contains (constant 0) 0 := by simpa only [Int.cast_zero] using constant_contains 0
  exact ⟨h,h,h,h⟩

private theorem logTwo_contains : Contains logTwoBox (Real.log 2) := by
  have h := ratio_contains 1 (d := 3) (by decide)
  have he := neg_contains (logGapFixed_contains h (by decide +kernel))
  simp only [Int.cast_one, Int.cast_ofNat] at he
  have hv : -(Real.log (1-(1:ℝ)/3)-Real.log (1+1/3)) = Real.log 2 := by
    rw [neg_sub, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  exact hv ▸ he

private theorem logNatural_contains {n : ℕ} (hn : 0 < n)
    (hcheck : inLogDomain (logRatioBox n) = true) :
    Contains (logNaturalBox n) (Real.log (n:ℝ)) := by
  let e := binaryExponent128 n
  let p : ℝ := 2^e
  let P : Int := ↑((2:Nat)^e)
  let q : ℝ := ((n:ℝ)-p)/((n:ℝ)+p)
  have hp : 0 < p := by dsimp [p]; positivity
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn
  have hD : 0 < (n:Int)+P := by
    have hPi : (0:Int) < P := by
      change (0:Int) < (↑((2:Nat)^e) : Int)
      exact_mod_cast (pow_pos (by decide : 0 < (2:Nat)) e)
    have hn' : (0:Int) < n := by exact_mod_cast hn
    omega
  have hq : Contains (logRatioBox n) q := by
    have hc : (P:ℝ) = p := by simp [P,p]
    have hv := ratio_contains ((n:Int)-P) hD
    rw [Int.cast_sub, Int.cast_add, hc, Int.cast_natCast] at hv
    exact hv
  obtain ⟨hq0,hq1⟩ := logDomain_contains hq hcheck
  have hp1 : 0 < 1+q := by linarith
  have hm1 : 0 < 1-q := by linarith
  have hratio : (1+q)/(1-q) = (n:ℝ)/p := by
    have hden : (n:ℝ)+p ≠ 0 := (add_pos hN hp).ne'
    apply (div_eq_div_iff hm1.ne' hp.ne').mpr
    dsimp only [q]
    field_simp [hden]
    ring
  have hprod : p*((1+q)/(1-q)) = (n:ℝ) := by rw [hratio, mul_div_cancel₀ _ hp.ne']
  have hlog : (e:ℝ)*Real.log 2 + -(Real.log (1-q)-Real.log (1+q)) = Real.log (n:ℝ) := by
    rw [← hprod, Real.log_mul hp.ne' (div_ne_zero hp1.ne' hm1.ne'),
      Real.log_div hp1.ne' hm1.ne', show Real.log p = (e:ℝ)*Real.log 2 from Real.log_pow 2 e]
    ring
  have hh := add_contains (mul_contains (constant_contains (e:Int)) logTwo_contains)
    (neg_contains (logGapFixed_contains hq hcheck))
  simpa only [Int.cast_natCast, hlog] using hh

private theorem term_coordinates (j : ℕ) (L : ℝ) (hL : L = Real.log ((j:ℝ)+1)) :
    (exponentialTerm j firstCenter).re = Real.exp (-L/2)*Real.cos (7067363/500000*L) ∧
      (exponentialTerm j firstCenter).im = -(Real.exp (-L/2)*Real.sin (7067363/500000*L)) := by
  have hre : (exponentScale j * firstCenter).re = -L/2 := by
    norm_num [exponentScale, firstCenter, hL, Complex.mul_re]
    ring
  have him : (exponentScale j * firstCenter).im = -(7067363/500000*L) := by
    norm_num [exponentScale, firstCenter, hL, Complex.mul_im]
    ring
  simp only [exponentialTerm, Complex.exp_re, Complex.exp_im, hre, him,
    Real.cos_neg, Real.sin_neg, mul_neg, and_self]

private theorem successful_option {α : Type*} {check : Bool} {a b : α}
    (h : (if check then some a else none) = some b) : check = true ∧ a = b := by
  cases check <;> simp_all

theorem etaBasis_contains {j : ℕ} (hj : j+1 ≤ 128) {b : EtaBounds}
    (hcheck : etaBasis j = some b) :
    EtaContains b (exponentialTerm j firstCenter)
      (exponentScale j * exponentialTerm j firstCenter) := by
  let n := j+1
  let L := Real.log (n:ℝ)
  let ell := logNaturalBox n
  let phase := mul (fromRatio 7067363 500000) ell
  let amp := expFixed (divInt (neg ell) 2)
  let cs := cosSinFixed phase
  let r := mul amp cs.1
  let i := neg (mul amp cs.2)
  let slope := mul (constant (-2)) ell
  let ok := inLogDomain (logRatioBox n) && inUnit (divInt (reducedPhase phase) 4)
  have he : (if ok then some (⟨r,i,mul slope r,mul slope i⟩ : EtaBounds) else none) = some b := hcheck
  obtain ⟨hOK, hB⟩ := successful_option he
  have hguards := Bool.and_eq_true_iff.mp hOK
  have hL : Contains ell L := logNatural_contains (Nat.succ_pos _) hguards.1
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.succ_pos j)
  have hmax : (n:ℝ) ≤ 128 := by exact_mod_cast hj
  have hmin : (1:ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le j))
  have hLn0 : 0 ≤ L := Real.log_nonneg hmin
  have hLn : L ≤ (n:ℝ)-1 := Real.log_le_sub_one_of_pos hn
  have hrange : |-L/2| ≤ (128:ℝ) := by
    rw [abs_of_nonpos (by linarith : -L/2 ≤ 0)]
    linarith
  have hhalf : Contains (divInt (neg ell) 2) (-L/2) := by
    simpa only [Int.cast_ofNat] using divInt_contains (neg_contains hL) (d := 2) (by decide)
  have hAmp := expFixed_contains hhalf hrange
  have hω : Contains (fromRatio 7067363 500000) ((7067363:ℝ)/500000) := by
    simpa only [Int.cast_ofNat] using ratio_contains 7067363 (d := 500000) (by decide)
  have hcs := cosSinFixed_contains (mul_contains hω hL) hguards.2
  have hcoords := term_coordinates j L (by simp only [L, n, Nat.cast_add, Nat.cast_one])
  have hRe : Contains r (exponentialTerm j firstCenter).re := by
    rw [hcoords.1]
    exact mul_contains hAmp hcs.1
  have hIm : Contains i (exponentialTerm j firstCenter).im := by
    rw [hcoords.2]
    exact neg_contains (mul_contains hAmp hcs.2)
  have hSlope : Contains slope (-2*L) := by
    simpa only [Int.cast_neg, Int.cast_ofNat] using mul_contains (constant_contains (-2)) hL
  have hLog : (j:ℝ)+1 = (n:ℝ) := by simp only [n, Nat.cast_add, Nat.cast_one]
  rw [← hB]
  refine ⟨hRe,hIm,?_,?_⟩
  · simpa only [exponentScale, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hLog, L] using mul_contains hSlope hRe
  · simpa only [exponentScale, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, hLog, L] using mul_contains hSlope hIm

#print axioms etaBasis_contains

end DottieOriented.NativeSpectrum.MellinFixed
end
