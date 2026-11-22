import QuarticPoisson

open QuarticDualArithmetic

namespace QuarticFiniteFourier

abbrev DualIndex := {v : ℤ × ℤ // (D : ℤ) ∣ v.2 - r*v.1}

def shiftedIndex (p : ZMod D × ℤ × ℤ) : DualIndex :=
  ⟨((D : ℤ)*p.2.1-p.1.val, (D : ℤ)*p.2.2-r*p.1.val),
    ⟨p.2.2-r*p.2.1, by dsimp only; ring⟩⟩

private theorem shiftedIndex_injective : Function.Injective shiftedIndex := by
  intro p q hpq
  have hx := congrArg (fun z : DualIndex => z.val.1) hpq
  have hy := congrArg (fun z : DualIndex => z.val.2) hpq
  change (D:ℤ)*p.2.1-p.1.val = (D:ℤ)*q.2.1-q.1.val at hx
  change (D:ℤ)*p.2.2-r*p.1.val = (D:ℤ)*q.2.2-r*q.1.val at hy
  have he := congrArg (fun x : ℤ => (x : ZMod D)) hx
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, zero_sub, ZMod.natCast_zmod_val, neg_inj] at he
  rw [he] at hx hy
  have hD : (D:ℤ) ≠ 0 := by decide
  refine Prod.ext he (Prod.ext ?_ ?_)
  · exact mul_left_cancel₀ hD (sub_left_inj.mp hx)
  · exact mul_left_cancel₀ hD (sub_left_inj.mp hy)

private theorem shiftedIndex_surjective : Function.Surjective shiftedIndex := by
  intro p
  let j : ZMod D := -(p.val.1 : ZMod D)
  have h0 : ((p.val.1+(j.val:ℤ) : ℤ):ZMod D) = 0 := by
    simp only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val, j, add_neg_cancel]
  obtain ⟨x,hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hd : (D:ℤ) ∣ p.val.2+r*j.val := by
    have h := dvd_add p.property (dvd_mul_of_dvd_right
      (show (D:ℤ) ∣ p.val.1+j.val from ⟨x,hx⟩) r)
    convert h using 1
    ring
  obtain ⟨y,hy⟩ := hd
  refine ⟨(j,x,y), Subtype.ext (Prod.ext ?_ ?_)⟩
  · change (D:ℤ)*x-j.val = p.val.1
    linarith only [hx]
  · change (D:ℤ)*y-r*j.val = p.val.2
    linarith only [hy]

/-- The two shifted integer frequencies and their shared residue enumerate
the selected line exactly once. -/
noncomputable def shiftedDualEquiv : (ZMod D × ℤ × ℤ) ≃ DualIndex :=
  Equiv.ofBijective shiftedIndex ⟨shiftedIndex_injective, shiftedIndex_surjective⟩

def gaussianIndex (w : ℤ × ℤ) : DualIndex :=
  ⟨(a*w.1-b*w.2,b*w.1+a*w.2),
    (dual_lattice _ _).mpr ⟨w.1,w.2,rfl,rfl⟩⟩

private theorem gaussianIndex_bijective : Function.Bijective gaussianIndex := by
  constructor
  · intro p q hpq
    have hx := congrArg (fun z : DualIndex => z.val.1) hpq
    have hy := congrArg (fun z : DualIndex => z.val.2) hpq
    dsimp only [gaussianIndex] at hx hy
    apply Prod.ext
    · apply mul_left_cancel₀ (show (D:ℤ) ≠ 0 by decide)
      linear_combination a*hx+b*hy
    · apply mul_left_cancel₀ (show (D:ℤ) ≠ 0 by decide)
      linear_combination -b*hx+a*hy
  · intro p
    obtain ⟨x,y,hx,hy⟩ := (dual_lattice p.val.1 p.val.2).mp p.property
    exact ⟨(x,y),Subtype.ext (Prod.ext hx.symm hy.symm)⟩

noncomputable def gaussianDualEquiv : (ℤ × ℤ) ≃ DualIndex :=
  Equiv.ofBijective gaussianIndex gaussianIndex_bijective

theorem shifted_frequency_norm (p : ZMod D × ℤ × ℤ)
    (u v : ℤ) (h : shiftedDualEquiv p = gaussianDualEquiv (u,v)) :
    ((D : ℤ)*p.2.1-p.1.val)^2+((D : ℤ)*p.2.2-r*p.1.val)^2 =
      (D : ℤ)*(u^2+v^2) := by
  have hh := congrArg (fun z : DualIndex => z.val.1^2+z.val.2^2) h
  simpa only [shiftedDualEquiv, gaussianDualEquiv, Equiv.ofBijective_apply,
    gaussianIndex, shiftedIndex, dual_norm] using hh

theorem shifted_frequency_character (p : ZMod D × ℤ × ℤ)
    (u v : ℤ) (h : shiftedDualEquiv p = gaussianDualEquiv (u,v)) :
    quarticCharacter p.1 = (SuperZeta.FieldWeights.conductorReading u (-v) : ℂ) := by
  have hh := congrArg (fun z : DualIndex => (z.val.1 : ZMod D)) h
  simp only [shiftedDualEquiv, gaussianDualEquiv, Equiv.ofBijective_apply,
    shiftedIndex, gaussianIndex, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self, zero_mul, zero_sub, ZMod.natCast_zmod_val] at hh
  rw [← quarticCharacter_even p.1, hh, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub]
  change signValue (((a*u-b*v:ℤ):ZMod D)) = _
  simp only [signValue, ZMod.val_intCast, ← jacobiSym.mod_left (a*u-b*v) D, dual_character]

#print axioms shiftedDualEquiv
#print axioms gaussianDualEquiv
#print axioms shifted_frequency_norm
#print axioms shifted_frequency_character

end QuarticFiniteFourier
