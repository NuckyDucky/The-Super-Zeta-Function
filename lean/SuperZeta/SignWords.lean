import SuperZeta.Oriented.OrderedStages

/-! Forward words in the signed exponential stages. Concatenation records time.
Two words give the same entire map at a fixed nonzero complex lift exactly
when they have the same letters in the same positions. -/
noncomputable section
namespace SuperZeta.SignWords

open Complex SuperZeta.SpireDisk

inductive Sign | plus | minus deriving DecidableEq, Repr

def Sign.rate (L : ℂ) : Sign → ℂ
  | .plus => L
  | .minus => -L

def Sign.flip : Sign → Sign
  | .plus => .minus
  | .minus => .plus

/-- Signs are in chronological order, with the first letter acting first. -/
def eval (L : ℂ) (word : List Sign) : ℂ → ℂ := run (word.map (Sign.rate L))

theorem run_append (u v : List ℂ) (z : ℂ) :
    run (u ++ v) z = run v (run u z) := by
  induction u generalizing z with
  | nil => rfl
  | cons a u ih => exact ih (stage a z)

theorem eval_append (L : ℂ) (u v : List Sign) (z : ℂ) :
    eval L (u ++ v) z = eval L v (eval L u z) := by
  simp only [eval, List.map_append, run_append]

theorem pair_two_updates (L : ℂ) (p : ℂ × ℂ) :
    Reciprocal.step L (Reciprocal.step L p) =
      (eval L [.minus,.plus] p.1, eval L [.plus,.minus] p.2) := by
  rfl

theorem complement (L : ℂ) (w : List Sign) :
    eval L (w.map Sign.flip) = eval (-L) w := by
  have h : Sign.rate L ∘ Sign.flip = Sign.rate (-L) := by
    funext s; cases s <;> simp [Sign.rate, Sign.flip]
  simp [eval, List.map_map, h]

open scoped ComplexConjugate in
theorem conjugate_eval (L : ℂ) (w : List Sign) (z : ℂ) :
    conj (eval L w z) = eval (conj L) w (conj z) := by
  induction w generalizing z with
  | nil => rfl
  | cons s w ih =>
    change conj (eval L w (stage (s.rate L) z)) =
      eval (conj L) w (stage (s.rate (conj L)) (conj z))
    rw [ih]
    cases s <;> simp [Sign.rate, stage, ← Complex.exp_conj]

/-- Starting the same cycle after the block u intertwines the rooted returns. -/
theorem rotate_blocks (L : ℂ) (u v : List Sign) :
    Function.Semiconj (eval L u) (eval L (u ++ v)) (eval L (v ++ u)) := by
  intro z
  simp only [eval_append]

abbrev NonzeroRate := {a : ℂ // a ≠ 0}

/-- Outer-first form used to remove the last chronological stage in the proof. -/
private def outer : List NonzeroRate → ℂ → ℂ
  | [], z => z
  | a :: w, z => exp (a.val * outer w z)

private theorem outer_eq_run (w : List NonzeroRate) (z : ℂ) :
    outer w z = run (w.reverse.map Subtype.val) z := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [outer, List.reverse_cons, List.map_append, run_append, run, stage, ih]

private theorem outer_diff (w : List NonzeroRate) : Differentiable ℂ (outer w) := by
  induction w with
  | nil => exact differentiable_id
  | cons a w ih => exact (ih.const_mul a.val).cexp

private theorem nonzero_logarithm {v : ℂ} (hv : v ≠ 0) :
    ∃ t : ℂ, t ≠ 0 ∧ exp t = v := by
  by_cases h : v = 1
  · subst v
    exact ⟨_, two_pi_I_ne_zero, exp_eq_one_iff.mpr ⟨1, by simp⟩⟩
  · refine ⟨log v, ?_, exp_log hv⟩
    intro ht
    exact h (by rw [← exp_log hv, ht, exp_zero])

private theorem outer_hits (w : List NonzeroRate) {v : ℂ} (hv : v ≠ 0) :
    ∃ z, outer w z = v := by
  induction w generalizing v with
  | nil => exact ⟨v, rfl⟩
  | cons a w ih =>
    obtain ⟨t, ht, he⟩ := nonzero_logarithm hv
    obtain ⟨z, hz⟩ := ih (div_ne_zero ht a.property)
    exact ⟨z, by simp only [outer, hz, mul_comm a.val, div_mul_cancel₀ _ a.property, he]⟩

private theorem exponent_constant {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ}
    (he : ∀ z, exp (f z) = c) (z : ℂ) : f z = f 0 := by
  apply is_const_of_deriv_eq_zero hf _ z 0
  intro x
  have h := ((hf x).hasDerivAt.cexp).deriv
  rw [show (fun t => exp (f t)) = fun _ => c from funext he, deriv_const] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (exp_ne_zero _)

/-- Two scaled word maps which differ by a constant have difference zero.
Every word hits every nonzero value, and a nonempty word omits zero. -/
private theorem offset_zero (w v : List NonzeroRate) (a b : NonzeroRate) (k : ℂ)
    (h : ∀ z, a.val * outer w z - b.val * outer v z = k) : k = 0 := by
  by_contra hk
  cases v with
  | cons d v =>
    obtain ⟨z, hz⟩ := outer_hits w (div_ne_zero hk a.property)
    have he := h z
    rw [hz, mul_comm a.val, div_mul_cancel₀ _ a.property] at he
    change k - b.val * exp (d.val * outer v z) = k at he
    exact (mul_ne_zero b.property (exp_ne_zero (d.val * outer v z))) (by linear_combination -he)
  | nil =>
    cases w with
    | nil => exact hk (by simpa [outer] using (h 0).symm)
    | cons d w =>
      have he := h (-k / b.val)
      simp only [outer, mul_comm b.val, div_mul_cancel₀ _ b.property] at he
      exact (mul_ne_zero a.property (exp_ne_zero _)) (by linear_combination he)

/-- Even an overall scalar cannot identify two different nonzero-rate words. -/
private theorem outer_rigid (w v : List NonzeroRate) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ z, outer w z = c * outer v z) : w = v ∧ c = 1 := by
  induction w generalizing v c with
  | nil =>
    cases v with
    | nil => exact ⟨rfl, by simpa [outer] using (h 1).symm⟩
    | cons b v => exact False.elim ((mul_ne_zero hc (exp_ne_zero _)) (h 0).symm)
  | cons a w ih =>
    cases v with
    | nil => exact False.elim ((exp_ne_zero (a.val * outer w 0)) (by simpa [outer] using h 0))
    | cons b v =>
      let f := fun z => a.val * outer w z - b.val * outer v z
      have hd : Differentiable ℂ f :=
        ((outer_diff w).const_mul a.val).sub ((outer_diff v).const_mul b.val)
      have he (z) : exp (f z) = c := by
        change exp (a.val * outer w z - b.val * outer v z) = c
        rw [exp_sub, div_eq_iff (exp_ne_zero _)]
        exact h z
      have hk : f 0 = 0 := offset_zero w v a b _ (exponent_constant hd he)
      have hab (z) : a.val * outer w z = b.val * outer v z :=
        sub_eq_zero.mp ((exponent_constant hd he z).trans hk)
      have hr (z) : outer w z = (b.val/a.val) * outer v z := by
        apply mul_left_cancel₀ a.property
        rw [hab, ← mul_assoc, mul_comm a.val, div_mul_cancel₀ _ a.property]
      obtain ⟨hw, hrates⟩ := ih v (b.val/a.val) (div_ne_zero b.property a.property) hr
      have hba : b.val = a.val := by simpa using (div_eq_iff a.property).mp hrates
      have hc1 := he 0
      rw [hk, exp_zero] at hc1
      exact ⟨by rw [hw, (Subtype.ext hba).symm], hc1.symm⟩

/-- The original chronological run faithfully represents words in nonzero complex rates. -/
theorem nonzero_rates_injective :
    Function.Injective (fun w : List NonzeroRate => run (w.map Subtype.val)) := by
  intro u v h
  have he (z) : outer u.reverse z = 1 * outer v.reverse z := by
    simpa [outer_eq_run] using congrFun h z
  have hrev := (outer_rigid u.reverse v.reverse 1 one_ne_zero he).1
  simpa using congrArg List.reverse hrev

/-- At each nonzero complex lift every rooted sign word gives a different entire function. -/
theorem eval_injective {L : ℂ} (hL : L ≠ 0) : Function.Injective (eval L) := by
  let weight : Sign → NonzeroRate := fun s => ⟨s.rate L, by cases s <;> simp [Sign.rate, hL]⟩
  have distinct : L ≠ -L := by intro h; apply hL; linear_combination h / 2
  have hinj : Function.Injective weight := by
    intro a b eq; have h := congrArg Subtype.val eq
    cases a <;> cases b <;> simp_all [weight, Sign.rate]
  intro u v eq
  apply (List.map_injective_iff.mpr hinj)
  apply nonzero_rates_injective
  simpa [weight, eval, List.map_map, Function.comp_def] using eq

/-- With one specified starting value two different words can agree. -/
theorem first_stage_at_zero (L : ℂ) :
    eval L [.plus] 0 = eval L [.minus] 0 := by simp [eval, Sign.rate, run, stage]

/-- Even at the cap 1 the two signs can coincide for some complex lifts. -/
theorem first_stage_at_pi_I :
    eval (Real.pi * I) [.plus] 1 = -1 ∧ eval (Real.pi * I) [.minus] 1 = -1 := by
  simp [eval, Sign.rate, run, stage, exp_neg, Complex.exp_pi_mul_I]

/-- Every nonempty word at lift πi and cap 1 has endpoint −1. The first
stage reaches −1 and both choices of the following stage fix it. -/
theorem cap_at_pi_I (s : Sign) (rest : List Sign) :
    eval (Real.pi * I) (s :: rest) 1 = -1 := by
  have fixed (w : List Sign) : eval (Real.pi * I) w (-1) = -1 := by
    induction w with
    | nil => rfl
    | cons t tail ih =>
      change eval _ tail (stage (t.rate _) (-1)) = -1
      have ht : stage (t.rate (Real.pi * I)) (-1) = -1 := by
        cases t <;> simp [Sign.rate, stage, exp_neg, Complex.exp_pi_mul_I]
      rw [ht, ih]
  change eval _ rest (stage (s.rate _) 1) = -1
  have hs : stage (s.rate (Real.pi * I)) 1 = -1 := by
    cases s <;> simp [Sign.rate, stage, exp_neg, Complex.exp_pi_mul_I]
  rw [hs, fixed]

/-- At a positive real lift the value at the cap also determines its word. -/
private def realRate (L : ℝ) : Sign → ℝ
  | .plus => L
  | .minus => -L

/-- The head is the last stage applied. This ordering is convenient for decoding. -/
private def capOutside (L : ℝ) : List Sign → ℝ
  | [] => 1
  | s :: w => Real.exp (realRate L s * capOutside L w)

private theorem cap_pos (L : ℝ) (w : List Sign) : 0 < capOutside L w := by
  cases w with
  | nil => exact zero_lt_one
  | cons s w => exact Real.exp_pos _

/-- Decode the last sign and its predecessor. The cap itself closes the reading. -/
def readReal (L x : ℝ) : Option (Sign × ℝ) :=
  if x = 1 then none else some (if 1 < x then .plus else .minus, |Real.log x| / L)

private theorem read_step {L x : ℝ} (hL : 0 < L) (hx : 0 < x) (s : Sign) :
    readReal L (Real.exp (realRate L s * x)) = some (s, x) := by
  have hp := mul_pos hL hx
  cases s with
  | plus =>
    have h := Real.one_lt_exp_iff.mpr hp
    simp only [readReal, realRate, if_neg h.ne', if_pos h, Real.log_exp, abs_of_pos hp]
    rw [mul_comm L x, mul_div_cancel_right₀ _ hL.ne']
  | minus =>
    have h := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hp)
    simp only [readReal, realRate, neg_mul, if_neg h.ne, if_neg (not_lt.mpr h.le),
      Real.log_exp, abs_neg, abs_of_pos hp]
    rw [mul_comm L x, mul_div_cancel_right₀ _ hL.ne']

private theorem cap_joins (L : ℝ) (w : List Sign) :
    eval (L : ℂ) w.reverse 1 = (capOutside L w : ℂ) := by
  induction w with
  | nil => simp [eval, run, capOutside]
  | cons s w ih =>
    rw [List.reverse_cons, eval_append, ih]
    cases s <;> simp [eval, Sign.rate, run, stage, capOutside, realRate, Complex.ofReal_exp]

/-- At most `fuel` signed stages may be removed from the endpoint. A successful
decoding returns the letters in chronological order. -/
def decodeReal (L : ℝ) : ℕ → ℝ → Option (List Sign)
  | 0, x => if x = 1 then some [] else none
  | n + 1, x =>
    match readReal L x with
    | none => some []
    | some (s, y) => (decodeReal L n y).map (fun w => w ++ [s])

private theorem decode_outside {L : ℝ} (hL : 0 < L) (w : List Sign) (n : ℕ)
    (hn : w.length ≤ n) : decodeReal L n (capOutside L w) = some w.reverse := by
  induction n generalizing w with
  | zero =>
    cases w with
    | nil => simp [decodeReal, capOutside]
    | cons s w => simp at hn
  | succ n ih =>
    cases w with
    | nil => simp [decodeReal, capOutside, readReal]
    | cons s w =>
      have hw : w.length ≤ n := Nat.le_of_succ_le_succ hn
      simp only [capOutside, decodeReal, read_step hL (cap_pos L w), ih w hw,
        Option.map_some, List.reverse_cons]
      rfl

/-- Repeated signed logarithms recover the chronological word from the real
part of its actual complex cap evaluation, given any upper bound on length. -/
theorem decodeReal_eval {L : ℝ} (hL : 0 < L) (w : List Sign) (n : ℕ)
    (hn : w.length ≤ n) : decodeReal L n (eval (L : ℂ) w 1).re = some w := by
  have he := cap_joins L w.reverse
  rw [List.reverse_reverse] at he
  rw [he]
  simpa using decode_outside hL w.reverse n (by simpa using hn)

private theorem cap_injective {L : ℝ} (hL : 0 < L) : Function.Injective (capOutside L) := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons t v =>
      have hh := congrArg (readReal L) h
      simp only [capOutside, read_step hL (cap_pos L v)] at hh
      simp [readReal] at hh
  | cons s u ih =>
    intro v h
    have hh := congrArg (readReal L) h
    cases v with
    | nil =>
      simp only [capOutside, read_step hL (cap_pos L u)] at hh
      simp [readReal] at hh
    | cons t v =>
      simp only [capOutside, read_step hL (cap_pos L u), read_step hL (cap_pos L v),
        Option.some.injEq, Prod.mk.injEq] at hh
      rw [hh.1, ih hh.2]

theorem real_cap_injective {L : ℝ} (hL : 0 < L) :
    Function.Injective (fun w : List Sign => eval (L : ℂ) w 1) := by
  intro u v h
  have he : (capOutside L u.reverse : ℂ) = (capOutside L v.reverse : ℂ) := by
    simpa only [← cap_joins, List.reverse_reverse] using h
  have hr := cap_injective hL (Complex.ofReal_injective he)
  simpa using congrArg List.reverse hr

/-- Execute each phrase from the endpoint of the preceding phrase. -/
def evalPhrases (L : ℂ) : List (List Sign) → ℂ → ℂ
  | [], z => z
  | u :: rest, z => evalPhrases L rest (eval L u z)

/-- Regrouping a run preserves its ordered sequence of individual stages. -/
theorem evalPhrases_flatten (L : ℂ) (phrases : List (List Sign)) (z : ℂ) :
    evalPhrases L phrases z = eval L phrases.flatten z := by
  induction phrases generalizing z with
  | nil => rfl
  | cons u rest ih =>
    rw [evalPhrases, List.flatten_cons, eval_append, ih]

/-- Two executions at the common cap and positive real lift give the same
endpoint if and only if the letters in chronological order are identical.
The input lists permit arbitrary phrase breaks and empty phrases. -/
theorem rooted_phrase_order_iff {L : ℝ} (hL : 0 < L) (u v : List (List Sign)) :
    evalPhrases (L : ℂ) u 1 = evalPhrases (L : ℂ) v 1 ↔ u.flatten = v.flatten := by
  rw [evalPhrases_flatten, evalPhrases_flatten]
  exact (real_cap_injective hL).eq_iff

/-- At a nonzero complex lift the same classification holds for equality
of the entire maps, with the starting value allowed to vary. -/
theorem phrase_map_order_iff {L : ℂ} (hL : L ≠ 0) (u v : List (List Sign)) :
    evalPhrases L u = evalPhrases L v ↔ u.flatten = v.flatten := by
  rw [funext (evalPhrases_flatten L u), funext (evalPhrases_flatten L v)]
  exact (eval_injective hL).eq_iff

/-- The words ++--, --++, and -+-+ all have two letters of each kind.
Starting at the same cap, their three endpoint values are pairwise distinct. -/
theorem three_balanced_rooted_words {L : ℝ} (hL : 0 < L) :
    let words : List (List Sign) :=
      [[.plus, .plus, .minus, .minus], [.minus, .minus, .plus, .plus],
       [.minus, .plus, .minus, .plus]]
    words.map (fun w => (w.count .plus, w.count .minus)) = [(2, 2), (2, 2), (2, 2)] ∧
      (words.map (fun w => eval (L : ℂ) w 1)).Nodup := by
  dsimp only
  constructor
  · decide
  · apply List.Nodup.map (real_cap_injective hL)
    decide

/-- Derivative of the actual run up through the last letter in w. -/
def prefixDerivative (w : List NonzeroRate) (z : ℂ) : ℂ := deriv (run (w.map Subtype.val)) z

private theorem prefix_nonzero (w : List NonzeroRate) (z : ℂ) : prefixDerivative w z ≠ 0 := by
  have hprod : (w.map Subtype.val).prod ≠ 0 := by
    induction w with
    | nil => simp
    | cons a w ih => simpa using mul_ne_zero a.property ih
  rw [prefixDerivative, (DottieOriented.run_derivative_from_lifts _ z).deriv]
  exact mul_ne_zero hprod (exp_ne_zero _)

theorem adjacent_ratio (w : List NonzeroRate) (a : NonzeroRate) (z : ℂ) :
    prefixDerivative (w ++ [a]) z / prefixDerivative w z =
      a.val * stage a.val (run (w.map Subtype.val) z) := by
  let rates := w.map Subtype.val
  have hr := DottieOriented.run_derivative_from_lifts rates z
  have hs : HasDerivAt (stage a.val) (a.val * stage a.val (run rates z)) (run rates z) := by
    change HasDerivAt (fun x => exp (a.val * x)) _ _
    simpa only [stage, id_eq, mul_one, mul_comm (exp _) a.val] using
      ((hasDerivAt_id (run rates z)).const_mul a.val).cexp
  have hc := (hs.comp z hr).deriv
  apply (div_eq_iff (prefix_nonzero w z)).2
  have eq : run ((w ++ [a]).map Subtype.val) = stage a.val ∘ run rates := by
    funext x; simp [rates, run_append, run]
  simpa only [prefixDerivative, eq, hr.deriv, rates] using hc

/-- Recover the output and the signed rate of the second stage from the
three successive prefix derivatives along the same alternating orbit. -/
theorem invert_adjacent_alternating (w : List NonzeroRate) (a : NonzeroRate) (z : ℂ) :
    let b : NonzeroRate := ⟨-a.val, neg_ne_zero.mpr a.property⟩
    let w₁ := w ++ [a]
    let w₂ := w₁ ++ [b]
    let d₁ := prefixDerivative w₁ z / prefixDerivative w z
    let d₂ := prefixDerivative w₂ z / prefixDerivative w₁ z
    run (w₂.map Subtype.val) z = exp (-d₁) ∧ d₂ * exp d₁ = -a.val := by
  dsimp only
  rw [adjacent_ratio, adjacent_ratio]
  simp only [List.map_append, List.map_cons, List.map_nil, run_append, run]
  simp only [stage, neg_mul, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, and_self]


/-- Take the same two lengths at consecutive starting phases. Each short
    window has length w.length + 1. With 159 interior rates these are the
    160- and 161-stage measurements around the Dottie cycle. -/
theorem invert_sliding_windows (b : NonzeroRate) (w : List NonzeroRate)
    (a : NonzeroRate) (z : ℂ) :
    let c : NonzeroRate := ⟨-a.val, neg_ne_zero.mpr a.property⟩
    let start₂ := stage b.val z
    let u := b :: w
    let v := w ++ [a]
    let d₁ := prefixDerivative (u ++ [a]) z / prefixDerivative u z
    let d₂ := prefixDerivative (v ++ [c]) start₂ / prefixDerivative v start₂
    run ((v ++ [c]).map Subtype.val) start₂ = exp (-d₁) ∧
      d₂ * exp d₁ = -a.val := by
  have h := invert_adjacent_alternating (b :: w) a z
  dsimp only at h ⊢
  simp only [adjacent_ratio, List.map_append, List.map_cons, List.map_nil, run_append, run] at h ⊢
  exact h

end SuperZeta.SignWords
