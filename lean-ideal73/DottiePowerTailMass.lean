import DottieMomentMass
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! An exact power-weighted tail bound for the archived Gaussian coefficients.
It bounds any finite subset above the cutoff, including the far omitted set,
using the lattice count and ordinary integral comparison. -/

namespace QuarticModel

open Finset

private theorem weighted_le_of_prefix_le (a b f : ℕ → ℝ) (n : ℕ)
    (hf : Antitone f) (hf₀ : 0 ≤ f n)
    (hprefix : ∀ k ≤ n+1, ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, b i) :
    ∑ i ∈ range (n+1), f i * a i ≤ ∑ i ∈ range (n+1), f i * b i := by
  have ha := sum_range_by_parts f a (n+1)
  have hb := sum_range_by_parts f b (n+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at ha hb
  rw [ha,hb]
  refine sub_le_sub (mul_le_mul_of_nonneg_left (hprefix _ le_rfl) hf₀) ?_
  exact sum_le_sum fun i hi =>
    mul_le_mul_of_nonpos_left (hprefix _ (Nat.succ_le_succ (mem_range.mp hi).le))
      (sub_nonpos.mpr (hf (Nat.le_succ i)))

private theorem shifted_coeff_prefix_le {X : ℕ} (hX : 0 < X) (m : ℕ) :
    (∑ i ∈ range m, |(archivedLatticeCoeff (X+i+1) : ℝ)|) ≤
      (1+(X.sqrt : ℝ)⁻¹) * ((X : ℝ)+m) := by
  have hpre : (∑ i ∈ range m, |(archivedLatticeCoeff (X+i+1) : ℝ)|) ≤
      ((X+m : ℕ) : ℝ)+((X+m).sqrt : ℝ) := by
    have h := archived_coeff_prefix_abs_le_linear (X+m)
    rw [sum_range_add] at h
    have h₀ : 0 ≤ ∑ i ∈ range X, |(archivedLatticeCoeff (i+1) : ℝ)| :=
      sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hx : 0 < (X.sqrt : ℝ) := by
    have h₁ : (1 : ℕ) ≤ X := by omega
    have h₂ : (1 : ℕ) ≤ X.sqrt := Nat.le_sqrt'.mpr (by simpa only [one_pow] using h₁)
    exact_mod_cast (Nat.zero_lt_one.trans_le h₂)
  have hmono := Nat.sqrt_le_sqrt (Nat.le_add_right X m)
  have hcount : (X+m).sqrt * X.sqrt ≤ X+m := calc
    _ ≤ (X+m).sqrt * (X+m).sqrt := Nat.mul_le_mul_left _ hmono
    _ ≤ _ := by simpa only [pow_two] using Nat.sqrt_le' (X+m)
  have hs : ((X+m).sqrt : ℝ) ≤ ((X : ℝ)+m)/(X.sqrt : ℝ) :=
    (le_div_iff₀ hx).mpr (by exact_mod_cast hcount)
  calc
    _ ≤ ((X : ℝ)+m)+((X+m).sqrt : ℝ) := by simpa only [Nat.cast_add] using hpre
    _ ≤ ((X : ℝ)+m)+((X : ℝ)+m)/(X.sqrt : ℝ) := by gcongr
    _ = _ := by ring

private theorem shifted_power_range_le {X : ℕ} (hX : 0 < X) (m : ℕ) {p : ℝ}
    (hp : 1 < p) :
    (∑ i ∈ range m, |(archivedLatticeCoeff (X+i+1) : ℝ)| *
      ((X+i+1 : ℕ) : ℝ)^(-p)) ≤
      (1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-p)*(p/(p-1))) := by
  let C : ℝ := 1+(X.sqrt : ℝ)⁻¹
  let f (i : ℕ) : ℝ := ((X : ℝ)+(i+1 : ℕ))^(-p)
  let a (i : ℕ) : ℝ := |(archivedLatticeCoeff (X+i+1) : ℝ)|
  let b (i : ℕ) : ℝ := C + if i=0 then C*(X : ℝ) else 0
  have hC : 0 ≤ C := by positivity
  have hx : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hf : Antitone f := by
    intro i j hij
    have hh : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact Real.rpow_le_rpow_of_nonpos (show 0 < (X : ℝ)+(i+1 : ℕ) by positivity)
      (by push_cast; linarith) (by linarith)
  have hf₀ (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  have hb (k : ℕ) : (∑ i ∈ range (k+1), b i) = C*((X : ℝ)+(k+1 : ℕ)) := by
    simp [b, sum_add_distrib]
    ring
  have hprefix (k : ℕ) : ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, b i := by
    cases k with
    | zero => simp
    | succ k =>
      rw [hb k]
      exact shifted_coeff_prefix_le hX (k+1)
  have hpow (k : ℕ) :
      (∑ i ∈ range k, f i) ≤ (X : ℝ)^(1-p)/(p-1) := by
    have hanti : AntitoneOn (fun y : ℝ => y^(-p)) (Set.Icc (X : ℝ) ((X : ℝ)+k)) :=
      fun y hy z _ hyz => Real.rpow_le_rpow_of_nonpos (hx.trans_le hy.1) hyz (by linarith)
    have hsum := hanti.sum_le_integral
    have hk : (X : ℝ) ≤ (X : ℝ)+k := le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hzero : (0 : ℝ) ∉ Set.uIcc (X : ℝ) ((X : ℝ)+k) := by
      rw [Set.uIcc_of_le hk]
      exact fun hh => hx.not_ge hh.1
    rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩), show -p+1=1-p by ring] at hsum
    refine hsum.trans ?_
    have hpos : 0 < p-1 := by linarith
    let a := (X : ℝ)^(1-p)
    let b := ((X : ℝ)+k)^(1-p)
    have hb₀ : 0 ≤ b := Real.rpow_nonneg (by positivity) _
    change (b-a)/(1-p) ≤ a/(p-1)
    rw [show 1-p = -(p-1) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (sub_le_self a hb₀) hpos.le
  have hxweight : (X : ℝ)*f 0 ≤ (X : ℝ)^(1-p) := calc
    _ ≤ (X : ℝ)*(X : ℝ)^(-p) := by
      apply mul_le_mul_of_nonneg_left _ hx.le
      exact Real.rpow_le_rpow_of_nonpos hx
        (show (X : ℝ) ≤ (X : ℝ)+(0+1 : ℕ) from le_add_of_nonneg_right (Nat.cast_nonneg _))
        (by linarith)
    _ = _ := by rw [show 1-p=1+(-p) by ring, Real.rpow_add hx, Real.rpow_one]
  change ∑ i ∈ range m, a i * ((X+i+1 : ℕ) : ℝ)^(-p) ≤ _
  have he (i : ℕ) : ((X+i+1 : ℕ) : ℝ)^(-p) = f i := by simp [f, Nat.cast_add, add_assoc]
  simp_rw [he]
  cases m with
  | zero =>
    rw [sum_range_zero]
    exact mul_nonneg hC (by positivity)
  | succ n =>
    simp_rw [mul_comm (a _)]
    refine (weighted_le_of_prefix_le a b f n hf (hf₀ n) (fun k _ => hprefix k)).trans ?_
    have hsplit :
        (∑ i ∈ range (n+1), f i*b i) = C*((X : ℝ)*f 0+∑ i ∈ range (n+1), f i) := by
      simp only [b, mul_add, sum_add_distrib, ← sum_mul, mul_ite, mul_zero]
      simp
      ring
    rw [hsplit]
    refine (mul_le_mul_of_nonneg_left (add_le_add hxweight (hpow (n+1))) hC).trans_eq ?_
    change C * ((X : ℝ)^(1-p)+(X : ℝ)^(1-p)/(p-1)) = C * ((X : ℝ)^(1-p)*(p/(p-1)))
    apply congrArg (C * ·)
    have hn : p-1 ≠ 0 := by linarith
    field_simp [hn]
    ring

/-- Absolute Gaussian coefficient mass on any finite set beyond a positive
cutoff, with the sharp integral-comparison constant for a linear count. -/
theorem archived_power_tail_mass_le (S : Finset ℕ) {X : ℕ} (hX : 0 < X)
    (hS : ∀ n ∈ S, X < n) {p : ℝ} (hp : 1 < p) :
    (∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)| * (n : ℝ)^(-p)) ≤
      (1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-p)*(p/(p-1))) := by
  let m := S.sup id - X
  let e (i : ℕ) := X+i+1
  have hsubset : S ⊆ (range m).image e := by
    intro n hn
    have hsup : n ≤ S.sup id := le_sup (f := id) hn
    have hn' := hS n hn
    refine mem_image.mpr ⟨n-X-1, mem_range.mpr ?_, ?_⟩
    · dsimp only [m]
      omega
    · dsimp only [e]
      omega
  have hinj : Set.InjOn e ↑(range m) := by
    intro i _ j _ h
    dsimp only [e] at h
    omega
  refine (sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by positivity)).trans ?_
  rw [sum_image hinj]
  exact shifted_power_range_le hX m hp

#print axioms archived_power_tail_mass_le

end QuarticModel
