import SuperZeta.SignWords
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.List.Induction
import Mathlib.Data.Real.Pi.Bounds

/-! Derivatives with respect to the starting cap.  The signs are read in
chronological order and the logarithmic lift is fixed throughout. -/
noncomputable section
namespace SuperZeta.CapJets

open Complex SignWords

abbrev lift : ℂ := Real.pi * I

private theorem word_diff (w : List Sign) : Differentiable ℂ (eval lift w) := by
  induction w with
  | nil => exact differentiable_id
  | cons s w ih =>
    change Differentiable ℂ (fun z => eval lift w (exp (s.rate lift * z)))
    fun_prop

private theorem append_exp (w : List Sign) (s : Sign) :
    eval lift (w ++ [s]) = fun z => exp (s.rate lift * eval lift w z) := by
  funext z
  rw [eval_append]
  rfl

private theorem appended_cap (w : List Sign) (s : Sign) :
    exp (s.rate lift * eval lift w 1) = -1 := by
  rw [← congrFun (append_exp w s) 1]
  cases w with
  | nil => exact cap_at_pi_I s []
  | cons t w => exact cap_at_pi_I t (w ++ [s])

/-- For a prefix with derivatives p and q, an appended stage of rate a
has first derivative −a p and second derivative −a q − (a p)². -/
theorem derivs_append (w : List Sign) (s : Sign) :
    let f := eval lift w
    let g := eval lift (w ++ [s])
    let a := s.rate lift
    deriv g 1 = -a * deriv f 1 ∧
      deriv (deriv g) 1 = -(a * deriv (deriv f) 1) - (a * deriv f 1)^2 := by
  dsimp only
  let f := eval lift w
  let a := s.rate lift
  have hf : Differentiable ℂ f := word_diff w
  have hd : Differentiable ℂ (deriv f) :=
    differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)
  have h (x : ℂ) := (((hf x).hasDerivAt.const_mul a).cexp)
  have hfun : deriv (eval lift (w ++ [s])) =
      fun x => exp (a*f x) * (a * deriv f x) := by
    rw [append_exp]
    exact funext fun x => (h x).deriv
  have hc : exp (a * f 1) = -1 := appended_cap w s
  have h2 := ((h 1).mul ((hd 1).hasDerivAt.const_mul a)).deriv
  rw [hfun]
  change exp (a * f 1) * (a * deriv f 1) = -a * deriv f 1 ∧
    deriv (fun x => exp (a*f x) * (a * deriv f x)) 1 =
      -(a * deriv (deriv f) 1) - (a * deriv f 1)^2
  constructor
  · rw [hc]; ring
  · rw [h2, hc]; ring

/-- First derivative with normalized second derivative, updated in chronological order. -/
def stepJet (v : ℂ × ℂ) (s : Sign) : ℂ × ℂ :=
  let p := -s.rate lift * v.1
  (p, v.2-p)

def jet (w : List Sign) : ℂ × ℂ := w.foldl stepJet (1,0)

/-- The finite recursion computes the two derivatives of the actual signed
word, with the second stored as W″/W′. The product statement uses no division. -/
theorem jet_correct (w : List Sign) :
    deriv (eval lift w) 1 = (jet w).1 ∧
    deriv (deriv (eval lift w)) 1 = (jet w).1 * (jet w).2 := by
  induction w using List.reverseRecOn with
  | nil =>
    change deriv (fun z : ℂ => z) 1 = 1 ∧ deriv (deriv (fun z : ℂ => z)) 1 = 1*0
    simp
  | append_singleton w s ih =>
    obtain ⟨hf, hs⟩ := derivs_append w s
    simp only [jet, List.foldl_append, List.foldl_cons, List.foldl_nil, stepJet] at *
    rw [hf, hs, ih.1, ih.2]
    constructor <;> ring

private theorem rate_ne_zero (s : Sign) : s.rate lift ≠ 0 := by
  have h : lift ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
  cases s <;> simp [Sign.rate, h]

theorem first_ne_zero (w : List Sign) : (jet w).1 ≠ 0 := by
  induction w using List.reverseRecOn with
  | nil => exact one_ne_zero
  | append_singleton w s ih =>
    simpa only [jet, List.foldl_append, List.foldl_cons, List.foldl_nil, stepJet] using
      mul_ne_zero (neg_ne_zero.mpr (rate_ne_zero s)) ih

theorem jet_ratio (w : List Sign) :
    deriv (deriv (eval lift w)) 1 / deriv (eval lift w) 1 = (jet w).2 := by
  rw [(jet_correct w).1, (jet_correct w).2]
  field_simp [first_ne_zero w]

/-- Here a,b,c,d are the four signed complex rates in chronological order. -/
theorem four_stage_formula (s t u v : Sign) :
    let a := s.rate lift
    let b := t.rate lift
    let c := u.rate lift
    let d := v.rate lift
    jet [s,t,u,v] = (a*b*c*d, a-a*b+a*b*c-a*b*c*d) := by
  dsimp [jet, stepJet]
  apply Prod.ext <;> dsimp <;> ring

/-- All six balanced sign words of length four, with the mark at the first letter. -/
def balanced : List (List Sign) :=
  [[.plus,.plus,.minus,.minus],[.plus,.minus,.minus,.plus],
   [.minus,.minus,.plus,.plus],[.minus,.plus,.plus,.minus],
   [.plus,.minus,.plus,.minus],[.minus,.plus,.minus,.plus]]

private def chart (r t u v : ℝ) : List ℂ :=
  [⟨r,u⟩, ⟨t,-v⟩, ⟨r,-u⟩, ⟨t,v⟩, ⟨t,u⟩, ⟨t,-u⟩]

private theorem chart_distinct {r t u v : ℝ} (hr : r ≠ t) (h₁ : 0 < v) (h₂ : v < u) :
    (chart r t u v).Nodup := by
  have huu : u ≠ -u := by linarith
  have hvv : -v ≠ v := by linarith
  have hvu : v ≠ -u := by linarith
  have hnu : -v ≠ u := by linarith
  simp [chart, List.nodup_cons, Complex.mk.injEq, hr, Ne.symm hr, h₂.ne,
    Ne.symm h₂.ne, huu, Ne.symm huu, hvv, hvu, Ne.symm hvu, hnu, Ne.symm hnu]

/-- Both coordinates of the normalized second derivatives, including their
orientation, in the same known basis used by the cap nudge. -/
theorem balanced_chart :
    balanced.map (fun w => (jet w).2) =
      chart (-Real.pi^4+Real.pi^2) (-Real.pi^4-Real.pi^2)
        (Real.pi^3+Real.pi) (Real.pi^3-Real.pi) := by
  simp only [balanced, chart, List.map_cons, List.map_nil, four_stage_formula,
    List.cons.injEq, true_and, and_true]
  simp [Complex.ext_iff, Sign.rate, lift, Complex.mul_re, Complex.mul_im]
  ring_nf
  simp

/-- The first cap derivatives are identical at all six words. -/
theorem balanced_first :
    ∀ w ∈ balanced, deriv (eval lift w) 1 = ((Real.pi ^ 4 : ℝ) : ℂ) := by
  intro w hw
  simp [balanced] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [(jet_correct _).1, four_stage_formula] <;>
    simp [Complex.ext_iff, lift, Sign.rate, Complex.mul_re, Complex.mul_im, pow_succ]

/-- The normalized second derivatives are pairwise distinct. -/
theorem balanced_second_ratio :
    (balanced.map (fun w => deriv (deriv (eval lift w)) 1 / deriv (eval lift w) 1)).Nodup := by
  simp_rw [jet_ratio]
  rw [balanced_chart]
  apply chart_distinct
  · have h : 0 < Real.pi^2 := by positivity
    linarith
  · nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi-2), mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr Real.pi_gt_three.le)]
  · linarith [Real.pi_pos]

/-- In particular the unnormalized second derivatives alone distinguish the six. -/
theorem balanced_second :
    (balanced.map (fun w => deriv (deriv (eval lift w)) 1)).Nodup := by
  have h := balanced_second_ratio
  have eq : balanced.map (fun w => deriv (deriv (eval lift w)) 1 / deriv (eval lift w) 1) =
      (balanced.map (fun w => deriv (deriv (eval lift w)) 1)).map
        (fun z => z / ((Real.pi ^ 4 : ℝ) : ℂ)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro w hw
    simp [Function.comp_apply, balanced_first w hw]
  rw [eq] at h
  exact List.Nodup.of_map _ h

end SuperZeta.CapJets
