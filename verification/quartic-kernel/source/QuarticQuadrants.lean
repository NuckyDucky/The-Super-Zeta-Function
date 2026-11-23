import QuarticLatticeTransform
import Mathlib.Tactic.FinCases

namespace QuarticFiniteFourier

abbrev NonzeroPair := {p : ℤ × ℤ // p ≠ (0,0)}

private def quadrant (k : Fin 4) (a b : ℤ) : ℤ × ℤ :=
  if k.val = 0 then (a,b)
  else if k.val = 1 then (-b,a)
  else if k.val = 2 then (-a,-b)
  else (b,-a)

private def quadrantMap (p : Fin 4 × ℕ × ℕ) : NonzeroPair :=
  ⟨quadrant p.1 ((p.2.1:ℤ)+1) p.2.2, by
    dsimp [quadrant]
    split_ifs <;> intro h
    all_goals first
      | have h₁ := congrArg Prod.fst h; dsimp at h₁; omega
      | have h₁ := congrArg Prod.snd h; dsimp at h₁; omega⟩

private theorem quadrantMap_injective : Function.Injective quadrantMap := by
  rintro ⟨k,a,b⟩ ⟨j,c,d⟩ h
  have hx := congrArg (fun p : NonzeroPair => p.val.1) h
  have hy := congrArg (fun p : NonzeroPair => p.val.2) h
  clear h
  fin_cases k <;> fin_cases j <;> simp [quadrantMap, quadrant] at hx hy ⊢ <;> omega

private theorem quadrantMap_surjective : Function.Surjective quadrantMap := by
  rintro ⟨⟨x,y⟩,h⟩
  have hn : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Prod.ext hc.1 hc.2)
  have cases' : (0 < x ∧ 0 ≤ y) ∨ (x ≤ 0 ∧ 0 < y) ∨ (x < 0 ∧ y ≤ 0) ∨
      (0 ≤ x ∧ y < 0) := by omega
  rcases cases' with ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩ | ⟨hx,hy⟩
  · refine ⟨(0,(x-1).toNat,y.toNat), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
      simp [quadrantMap, quadrant] <;> omega
  · refine ⟨(1,(y-1).toNat,(-x).toNat), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
      simp [quadrantMap, quadrant] <;> omega
  · refine ⟨(2,(-x-1).toNat,(-y).toNat), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
      simp [quadrantMap, quadrant] <;> omega
  · refine ⟨(3,(-y-1).toNat,x.toNat), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
      simp [quadrantMap, quadrant, show (3:Fin 4).val=3 by decide] <;> omega

noncomputable def quadrantEquiv : (Fin 4 × ℕ × ℕ) ≃ NonzeroPair :=
  Equiv.ofBijective quadrantMap ⟨quadrantMap_injective, quadrantMap_surjective⟩

theorem reading_rotation (a b : ℤ) :
    SuperZeta.FieldWeights.conductorReading (-b) a =
      SuperZeta.FieldWeights.conductorReading a b := by
  have h := quartic_rotation (a : ZMod D) (b : ZMod D)
  rw [← Int.cast_neg, sign_at_integer_point, sign_at_integer_point] at h
  unfold SuperZeta.FieldWeights.conductorReading
  simp only [jacobiSym.legendreSym.to_jacobiSym]
  norm_cast at h
  simpa only [mul_comm a (32:ℤ), mul_comm a (109:ℤ), mul_comm a (516876951:ℤ),
    mul_comm b (32:ℤ), mul_comm b (109:ℤ), mul_comm b (516876951:ℤ)] using h

private noncomputable def latticeTerm (A : ℝ) (p : ℤ × ℤ) : ℂ :=
  (SuperZeta.FieldWeights.conductorReading p.1 p.2 : ℂ) *
    Complex.exp (-Real.pi*(A:ℂ)*((p.1:ℂ)^2+(p.2:ℂ)^2))

private theorem latticeTerm_rotation (A : ℝ) (a b : ℤ) :
    latticeTerm A (-b,a) = latticeTerm A (a,b) := by
  simp only [latticeTerm, reading_rotation, Int.cast_neg, neg_sq]
  rw [add_comm ((b:ℂ)^2)]

noncomputable def quarterTerm (A : ℝ) (p : ℕ × ℕ) : ℂ :=
  latticeTerm A ((p.1:ℤ)+1, p.2)

private theorem on_quadrant (A : ℝ) (k : Fin 4) (p : ℕ × ℕ) :
    latticeTerm A (quadrantEquiv (k,p)).val = quarterTerm A p := by
  change latticeTerm A (quadrant k ((p.1:ℤ)+1) p.2) = _
  let x : ℤ := (p.1:ℤ)+1
  let y : ℤ := p.2
  have h1 := latticeTerm_rotation A x y
  have h2 := latticeTerm_rotation A (-y) x
  have h3 := latticeTerm_rotation A (-x) (-y)
  fin_cases k
  · rfl
  · exact h1
  · exact h2.trans h1
  · simpa only [quarterTerm, x, y, neg_neg] using h3.trans (h2.trans h1)

theorem gaussianLattice_four_quarters (A : ℝ)
    (hs : Summable (fun p : ℕ × ℕ => ‖quarterTerm A p‖)) :
    gaussianLattice A = 4 * ∑' p : ℕ×ℕ, quarterTerm A p := by
  have hz : latticeTerm A (0,0) = 0 := by
    norm_num [latticeTerm, SuperZeta.FieldWeights.conductorReading]
  have ho : Function.support (latticeTerm A) ⊆ {p : ℤ × ℤ | p ≠ (0,0)} := by
    intro p hp he
    exact hp (he ▸ hz)
  have hfin : Summable (fun p : Fin 4 × ℕ × ℕ => quarterTerm A p.2) := by
    simpa using summable_mul_of_summable_norm (f := fun _ : Fin 4 => (1:ℂ))
      Summable.of_finite hs
  change (∑' p : ℤ × ℤ, latticeTerm A p) = _
  rw [← tsum_subtype_eq_of_support_subset ho]
  calc
    _ = ∑' p : Fin 4 × ℕ × ℕ, latticeTerm A (quadrantEquiv p).val :=
      (quadrantEquiv.tsum_eq (fun p : NonzeroPair => latticeTerm A p.val)).symm
    _ = ∑' p : Fin 4 × ℕ × ℕ, quarterTerm A p.2 := tsum_congr
      (fun p => on_quadrant A p.1 p.2)
    _ = _ := by
      rw [hfin.tsum_prod' (fun _ => hs.of_norm), tsum_fintype]
      simp [nsmul_eq_mul]

#print axioms quadrantEquiv
#print axioms reading_rotation
#print axioms gaussianLattice_four_quarters

end QuarticFiniteFourier
