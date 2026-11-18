import SuperZeta.RootBounds
import SuperZeta.Dottie
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! Counting the positive characteristic levels and the multiplicities of the
unfolded roots of the unit-coupling cosine determinant. -/
namespace SuperZeta.QuartetRadius
noncomputable section
open Real Set

private theorem sinh_lt_mul_cosh {t : ℝ} (ht : 0 < t) : sinh t < t * cosh t := by
  let f (x : ℝ) := x * cosh x - sinh x
  have df (x : ℝ) : HasDerivAt f (x * sinh x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x) using 1
    simp
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (fun x _ => (df x).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ici, mem_Ioi] at hx
    rw [(df x).deriv]
    exact mul_pos hx (sinh_pos_iff.mpr hx)
  simpa [f, sub_pos] using hm (left_mem_Ici) ht.le ht

/-- The angular term and its derivative have opposite orientations, so both
terms in the derivative of the level function are strictly positive. -/
theorem level_derivative_positive {t : ℝ} (ht : 0 < t) : 0 < deriv level t := by
  have hs := sinh_pos_iff.mpr ht
  have ha : 0 < a t := div_pos ht hs
  have ha1 : a t < 1 := (div_lt_one hs).mpr (self_lt_sinh_iff.mpr ht)
  let v := (sinh t - t * cosh t) / (sinh t)^2
  have da : HasDerivAt a v t := by
    simpa [a, v] using (hasDerivAt_id t).div (hasDerivAt_sinh t) hs.ne'
  have hv : v < 0 := div_neg_of_neg_of_pos (sub_neg.mpr (sinh_lt_mul_cosh ht)) (sq_pos_of_pos hs)
  have hr : 0 < sqrt (1 - (-(a t))^2) := sqrt_pos.2 (by nlinarith [mul_pos ha (sub_pos.mpr ha1)])
  let w := -(1 / sqrt (1 - (-(a t))^2)) * -v
  have dθ : HasDerivAt θ w t :=
    (hasDerivAt_arccos (by linarith : -(a t) ≠ -1) (by linarith : -(a t) ≠ 1)).comp t da.neg
  have hw : w < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos (one_div_pos.mpr hr)) (neg_pos.mpr hv)
  have hsin : 0 < sin (θ t) := by
    rw [θ, sin_arccos]
    exact hr
  have hcos : cos (θ t) = -a t := cos_arccos (by linarith) (by linarith)
  have hscale : 1 + cosh t * cos (θ t) < 0 := by
    rw [hcos, a]
    have hh := (lt_div_iff₀ hs).mpr (show 1 * sinh t < cosh t * t by
      simpa [mul_comm] using sinh_lt_mul_cosh ht)
    linarith [show cosh t * (t / sinh t) = cosh t * t / sinh t by ring]
  have dl := ((dθ.add ((hasDerivAt_cosh t).mul ((hasDerivAt_sin (θ t)).comp t dθ))).const_mul 2).sub_const π
  simp only [Function.comp_apply] at dl
  change 0 < deriv (fun x => 2 * (θ x + cosh x * sin (θ x)) - π) t
  rw [dl.deriv]
  nlinarith only [mul_pos hs hsin, mul_pos_of_neg_of_neg hw hscale]

theorem level_strictMonoOn : StrictMonoOn level (Ioi 0) := by
  have hd (t : ℝ) (ht : t ∈ Ioi 0) := differentiableAt_of_deriv_ne_zero (level_derivative_positive ht).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ioi _) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
  simpa only [isOpen_Ioi.interior_eq] using fun t (ht : t ∈ Ioi 0) => level_derivative_positive ht

/-- At each positive integral index there is exactly one positive height. -/
theorem existsUnique_level (n : ℕ) (hn : 0 < n) :
    ∃! t : ℝ, 0 < t ∧ level t = 2 * π * n := by
  obtain ⟨t, ht, he⟩ := exists_level n hn
  exact ⟨t, ⟨ht, he⟩, fun y hy => level_strictMonoOn.injOn hy.1 ht (hy.2.trans he.symm)⟩

end
end SuperZeta.QuartetRadius

namespace SuperZeta.Quartet
open Complex

/-- At unit coupling the determinant in the original u-plane has only simple
zeros. This applies to every complex root. -/
theorem determinant_root_simple {u : ℂ} (hu : cos u ^ 2 - u ^ 2 = 0) :
    deriv (fun z : ℂ => cos z ^ 2 - z ^ 2) u ≠ 0 := by
  have du := ((Complex.hasDerivAt_cos u).pow 2).sub ((hasDerivAt_id u).pow 2)
  simp only [id_eq] at du
  rw [du.deriv]
  intro h
  have hzero : u ≠ 0 := by
    intro h0
    subst u
    norm_num at hu
  have hc : cos u ^ 2 = u ^ 2 := sub_eq_zero.mp hu
  have hcs : cos u * sin u = -u := by
    simp at h
    linear_combination -h / 2
  have hh := congrArg (fun z : ℂ => z^2) hcs
  simp only [mul_pow, neg_sq] at hh
  rw [hc] at hh
  have hs : sin u ^ 2 = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hzero)
    simpa only [mul_one] using hh
  have hid := Complex.sin_sq_add_cos_sq u
  rw [hs, hc] at hid
  exact (pow_ne_zero 2 hzero) (by linear_combination hid)

end SuperZeta.Quartet

namespace SuperZeta.RootBounds
open QuartetRadius Real Set
open scoped ComplexConjugate
noncomputable section

private def IsRoot (z : ℂ) := Complex.cos z ^ 2 - z ^ 2 = 0

private theorem signed_components {z : ℂ} (hz : IsRoot z) :
    ∃ b : ℝ, b^2=1 ∧ Real.cos z.re * Real.cosh z.im = b*z.re ∧
      -(Real.sin z.re * Real.sinh z.im) = b*z.im := by
  have factor : (Complex.cos z-z)*(Complex.cos z+z)=0 := by
    unfold IsRoot at hz
    linear_combination hz
  have component (b : ℝ) (h : Complex.cos z=(b:ℂ)*z) :
      Real.cos z.re * Real.cosh z.im = b*z.re ∧
      -(Real.sin z.re * Real.sinh z.im) = b*z.im := by
    rw [Complex.cos_eq] at h
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh] at h
    exact ⟨by simpa [Complex.mul_re,Complex.mul_im] using congrArg Complex.re h,
           by simpa [Complex.mul_re,Complex.mul_im] using congrArg Complex.im h⟩
  rcases mul_eq_zero.mp factor with h | h
  · exact ⟨1, by norm_num, component 1 (by simpa using sub_eq_zero.mp h)⟩
  · exact ⟨-1, by norm_num, component (-1) (by simpa using eq_neg_of_add_eq_zero_left h)⟩

/-- Every determinant zero strictly above the real axis in the closed right
half-plane has the level and the representative prescribed by the quartet. -/
theorem upper_right_root {z : ℂ} (hz : Complex.cos z^2-z^2=0)
    (hx : 0 ≤ z.re) (ht : 0 < z.im) :
    ∃ n : ℕ, 0 < n ∧ level z.im = 2*π*n ∧ z = u z.im := by
  obtain ⟨b, hb, hreal, himag⟩ := signed_components hz
  have hs := sinh_pos_iff.mpr ht
  have ha : 0 < a z.im := div_pos ht hs
  have ha1 : a z.im < 1 := (div_lt_one hs).mpr (self_lt_sinh_iff.mpr ht)
  have hcθ : cos (θ z.im) = -a z.im := cos_arccos (by linarith) (by linarith)
  have hsθ : 0 < sin (θ z.im) := by
    rw [θ, sin_arccos, sqrt_pos]
    nlinarith [mul_pos ha (sub_pos.mpr ha1)]
  have hsin : sin z.re = -b*a z.im := by
    unfold a
    field_simp [hs.ne']
    linarith
  have hsq : (sin z.re)^2=(cos (θ z.im))^2 := by rw [hsin, hcθ, mul_pow, neg_sq, hb]; ring
  have hsq' : (cos z.re)^2=(sin (θ z.im))^2 := by
    linarith only [sin_sq_add_cos_sq z.re, sin_sq_add_cos_sq (θ z.im), hsq]
  have hp : 0 < x z.im := mul_pos (cosh_pos _) hsθ
  have hx2 := congrArg (fun a : ℝ => a^2) hreal
  simp only [mul_pow, hb, one_mul, hsq'] at hx2
  have hcoord : z.re = x z.im := by
    have hx' : z.re ^ 2 = (x z.im)^2 := by simpa [x, mul_pow, mul_comm] using hx2.symm
    simpa [abs_of_nonneg hx, abs_of_pos hp] using (sq_eq_sq_iff_abs_eq_abs _ _).mp hx'
  have hcos : cos z.re = b * sin (θ z.im) := by
    apply mul_right_cancel₀ (cosh_pos z.im).ne'
    rw [hreal, hcoord, x]
    ring
  have hcross : cos (θ z.im + z.re)=0 := by
    rw [cos_add, hcos, hsin, hcθ]
    ring
  obtain ⟨k,hk⟩ := Real.cos_eq_zero_iff.mp hcross
  have hang : π/2 < θ z.im := by
    rw [← Real.arccos_zero]
    exact Real.arccos_lt_arccos (by linarith) (by linarith) (by norm_num)
  have hkn : 0 < k := by
    apply lt_of_not_ge
    intro hk0
    have hk' : (k:ℝ) ≤ 0 := by exact_mod_cast hk0
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hk' pi_pos.le]
  refine ⟨k.toNat, by omega, ?_, Complex.ext hcoord rfl⟩
  have ek : (k.toNat:ℝ) = (k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hkn.le
  change 2*(θ z.im+x z.im)-π = _
  rw [← hcoord, ek]
  linarith only [hk]

private lemma root_neg {z : ℂ} (h : IsRoot z) : IsRoot (-z) := by
  simpa [IsRoot] using h

private lemma root_conj {z : ℂ} (h : IsRoot z) : IsRoot (conj z) := by
  unfold IsRoot at *
  rw [Complex.cos_conj, ← map_pow, ← map_pow, ← map_sub, h, map_zero]

private lemma closed_quadrant {z : ℂ} (h : IsRoot z) :
    ∃ v : ℂ, 0 ≤ v.re ∧ 0 ≤ v.im ∧ IsRoot v ∧
      (z=v ∨ z= -v ∨ z=conj v ∨ z= -conj v) := by
  by_cases hx : 0 ≤ z.re <;> by_cases hy : 0 ≤ z.im
  · exact ⟨z,hx,hy,h,Or.inl rfl⟩
  · exact ⟨conj z, by simpa, by simp; linarith, root_conj h, by simp⟩
  · exact ⟨-conj z, by simp; linarith, by simpa, root_neg (root_conj h), by simp⟩
  · exact ⟨-z,by simp; linarith,by simp; linarith,root_neg h,by simp⟩

private lemma axis_root {d : ℝ} (hd : d ∈ Ioo 0 (π/2) ∧ d = cos d)
    {z : ℂ} (h : IsRoot z) (hx : 0 ≤ z.re) (hy : z.im=0) : z=(d:ℂ) := by
  have ez : z=(z.re:ℂ) := Complex.ext rfl (by simpa using hy)
  have he : cos z.re^2 = z.re^2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [← ez] using (sub_eq_zero.mp h)
  have hb := (sq_eq_sq_iff_abs_eq_abs _ _).mp he
  rw [abs_of_nonneg hx] at hb
  have h1 : z.re ≤ 1 := hb.symm.trans_le (abs_le.mpr ⟨neg_one_le_cos _,cos_le_one _⟩)
  have hc := cos_pos_of_le_one (x:=z.re) (by simpa [abs_of_nonneg hx] using h1)
  rw [abs_of_pos hc] at hb
  have hr : z.re ∈ Ioo 0 (π/2) := ⟨by linarith,by linarith [pi_gt_three]⟩
  obtain ⟨_,_,uniq⟩ := Dottie.existsUnique_dottie
  exact ez.trans (congrArg Complex.ofReal ((uniq _ ⟨hr,hb.symm⟩).trans (uniq d hd).symm))

private def flip : Unit ⊕ (ℕ ⊕ ℕ) → Unit ⊕ (ℕ ⊕ ℕ)
  | .inl k => .inl k
  | .inr (.inl n) => .inr (.inr n)
  | .inr (.inr n) => .inr (.inl n)

private theorem family_flip (d : ℝ) (t : ℕ → ℝ) (j) :
    family d t (flip j) = conj (family d t j) := by
  rcases j with k | n | n <;> simp [flip, family]

private lemma family_root {d : ℝ} (hd : d = cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ level (t n)=2*π*(n+1)) (j) :
    ∃ v : ℂ, IsRoot v ∧ v^2 = family d t j := by
  have hc (n : ℕ) : IsRoot (u (t n)) := by
    exact (Quartet.determinant_root_iff _).mpr ⟨_,characteristic_of_level (n:=n+1)
      (roots n).1 (by simpa using (roots n).2),original_coordinate (roots n).1⟩
  rcases j with k | n | n
  · refine ⟨(d:ℂ), ?_, by simp [family]⟩
    change Complex.cos (d:ℂ)^2 - (d:ℂ)^2=0
    rw [← Complex.ofReal_cos, ← hd, sub_self]
  · exact ⟨_,hc n,rfl⟩
  · exact ⟨_,root_conj (hc n), (map_pow _ _ _).symm⟩

/-- Squaring identifies the two signs. The remaining indices are exactly
Dottie's square and both conjugate branches, over all positive levels. -/
theorem determinant_root_iff_indexed_square {d : ℝ}
    (hd : d ∈ Ioo 0 (π/2) ∧ d = cos d) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ level (t n)=2*π*(n+1)) (z : ℂ) :
    Complex.cos z^2-z^2=0 ↔ ∃ j, z^2=family d t j := by
  constructor
  · intro h
    obtain ⟨v,hx,hy,hv,hz⟩ := closed_quadrant h
    have base : ∃ j, v^2 = family d t j := by
      rcases hy.eq_or_lt with h0 | hpos
      · exact ⟨.inl (), by rw [axis_root hd hv hx h0.symm]; simp [family]⟩
      · obtain ⟨n, hn, he, hcoord⟩ := upper_right_root hv hx hpos
        obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
        have ht : v.im=t k := level_strictMonoOn.injOn hpos (roots k).1
          (he.trans (by simpa using (roots k).2.symm))
        exact ⟨.inr (.inl k), by change v^2=(u (t k))^2; rw [← ht]; exact congrArg (·^2) hcoord⟩
    obtain ⟨j,hj⟩ := base
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨j,hj⟩
    · exact ⟨j, by simpa only [neg_sq] using hj⟩
    · exact ⟨flip j, by rw [family_flip, ← hj, map_pow]⟩
    · exact ⟨flip j, by rw [neg_sq, family_flip, ← hj, map_pow]⟩
  · rintro ⟨j,hj⟩
    obtain ⟨v,hv,he⟩ := family_root hd.2 roots j
    rcases ((Commute.all z v).sq_eq_sq_iff_eq_or_eq_neg).mp (hj.trans he.symm) with rfl | rfl
    · exact hv
    · exact root_neg hv

/-- Each squared zero receives one index. The sign of its imaginary part
distinguishes the conjugate branches, and the phase equation fixes the level. -/
theorem family_injective (d : ℝ) {t : ℕ → ℝ}
    (roots : ∀ n, 0<t n ∧ level (t n)=2*π*(n+1)) : Function.Injective (family d t) := by
  have hx (n : ℕ) : 0 < x (t n) := lt_of_lt_of_le (by positivity : (0:ℝ) < (n+1:ℕ))
    (x_lower (Nat.succ_pos n) (by simpa using (roots n).2))
  have hi (n : ℕ) : 0 < (u (t n)^2).im := by
    change 0 < (u (t n)^2).im
    simpa [u,pow_two,Complex.mul_im,two_mul] using
      add_pos (mul_pos (hx n) (roots n).1) (mul_pos (roots n).1 (hx n))
  have hb {n m : ℕ} (e : u (t n)^2 = u (t m)^2) : n=m := by
    rcases ((Commute.all _ _).sq_eq_sq_iff_eq_or_eq_neg).mp e with he | he
    · have ht := congrArg Complex.im he
      change t n = t m at ht
      have h := (roots n).2.symm.trans ((congrArg level ht).trans (roots m).2)
      have hn := mul_left_cancel₀ (by positivity : 2*π ≠ 0) h
      exact_mod_cast (add_right_cancel hn : (n:ℝ)=(m:ℝ))
    · have h := congrArg Complex.im he
      change t n = -t m at h
      linarith [(roots n).1,(roots m).1]
  rintro (k | n | n) (j | m | m) e
  all_goals simp only [family,Sum.elim_inl,Sum.elim_inr] at e
  · cases k; cases j; rfl
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi m]
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi m]
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi n]
  · exact congrArg (fun i : ℕ => Sum.inr (Sum.inl i)) (hb e)
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi n,hi m]
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi n]
  · have h := congrArg Complex.im e
    simp only [Complex.ofReal_im, Complex.conj_im] at h
    linarith [hi n,hi m]
  · exact congrArg (fun i : ℕ => Sum.inr (Sum.inr i)) (hb ((starRingEnd ℂ).injective e))

end
end SuperZeta.RootBounds
