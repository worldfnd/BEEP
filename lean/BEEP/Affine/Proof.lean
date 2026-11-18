-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request, as part of
-- `BEEP/AffineMain.lean`, the formalization of what is now Theorem 5.3 (`t:affine_main_0`) of
-- `paper/main.typ` (then Theorem 30 of `typst/deep+.typ`). AI-revised (claude-opus-5-5 and
-- claude-fable-5-2), 2026-11-16: the paper's new numbers and paths, in the comments only.
-- AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: that file is now the three
-- files `BEEP/Affine/Defs.lean` (the definitions that the statement of the theorem uses),
-- `BEEP/Affine/Theorem.lean` (the statements) and `BEEP/Affine/Proof.lean` (this one: the lemmas,
-- the other definitions and the proofs). The lemmas, definitions and proofs are moved here
-- without change, except that the four theorems that `BEEP/Affine/Theorem.lean` states are called
-- `x_proof` here (`affine_main_proof` for `affine_main`, and so on). The namespace `BEEP` is now
-- `BEEP.Affine`, and the comments are adapted to the three files.]
-- [AI-revised (claude-fable-5-2), 2026-11-17, later, at the author's remark: `hits` takes a pair
-- `b = (b₁, b₂)` (see `BEEP/Affine/Defs.lean`), so the proof writes `hits z (B z)` where it had
-- `hits B z`; `card_hits_le_maxHits` and `fold_challenge_le_proof` are stated for every `b`.]

-- A line starting with `--` is a comment, which Lean ignores. In this file each comment explains
-- the line, or the few lines, directly below it. The reading guide after the module documentation
-- explains every tactic used in the file; the one of `BEEP/Affine/Defs.lean` explains the notation.

-- Load the definitions of `BEEP/Affine/Defs.lean`, and with them Mathlib, Lean's library of
-- formalized mathematics. Every name used below and defined neither in this file nor in
-- `BEEP/Affine/Defs.lean` (`Finset`, `Polynomial`, `degreeLT`, `card_le_card`, ...) comes from
-- Mathlib.
import BEEP.Affine.Defs

/-!
# BEEP with affine challenges: the proof of Theorem 5.3

The proof of Theorem 5.3 of the BEEP paper (`paper/main.typ`, Section 5, label
`t:affine_main_0`): the lemma on which it rests, Lemma 5.5 (label `l:few_bad_points_on_line_0`,
"A parameterized line contains few pretenders, for the affine fold"), the definitions that only
the proof uses, and the proofs of the statements of `BEEP/Affine/Theorem.lean`. The objects of
the statements are defined in `BEEP/Affine/Defs.lean`.

There is no need to read this file to know what is proved: for that, read `BEEP/Affine/Defs.lean`
and `BEEP/Affine/Theorem.lean`. This file is for following the proof. It declares definitions and
theorems only (no notation and no instance), so it cannot change how a statement of
`BEEP/Affine/Theorem.lean` is read.

## Results of this file

* `BEEP.Affine.mem_polysLT`: a polynomial lies in `polysLT F k` exactly when it has degree less
  than `k`.
* `BEEP.Affine.Setup.affine_line_pairs` (the second case of the proof of Lemma 5.5): a
  parameterized line `α ↦ λ₁(α) F₁ + λ₂(α) F₂` with `(F₁, F₂)` in the set `C_λ^{≡2}` contains at
  most `(n - s + 2)(n - s + 1)/2` pretenders.
* `BEEP.Affine.Setup.affine_line` (Lemma 5.5): a parameterized line with coefficients in `F(X)`
  contains at most `N = max(q, (n - s + 2)(n - s + 1)/2)` pretenders.
* `BEEP.Affine.Setup.affine_main_gen_nat` and `BEEP.Affine.Setup.affine_main_gen`: Theorem 5.3
  for given answers `B`, in the counting form and with a probability.
* `BEEP.Affine.Setup.isPretender_ceil_iff`: with `s = ⌈(1 - δ) n⌉`, the pretenders of
  `BEEP/Affine/Defs.lean` are those of Definition 5.1, with agreement sets of size at least
  `(1 - δ) n`.
* `BEEP.Affine.Setup.affine_main_nat_proof`, `affine_main_proof`, `fold_challenge_le_proof` and
  `affine_main_delta_proof`: the proofs of the theorems `affine_main_nat`, `affine_main`,
  `fold_challenge_le` and `affine_main_delta` of `BEEP/Affine/Theorem.lean`, which states them
  again and explains them.

## Dictionary paper ↔ Lean, for the objects of the proof

The dictionary of `BEEP/Affine/Defs.lean` has the objects of the statement.

| paper (Section 5 of `paper/main.typ`) | Lean |
|---|---|
| Definition 5.4, a parameterized line `θ(α) = F_θ + α G_θ` | `D θ(α) = P + α Q`, with `F_θ = P/D`, `G_θ = Q/D` |
| `A_θ^pret` of Lemma 5.5 | `R.lineHits u₁ u₂ s D P Q` |
| `U((α_i, v_i)_{i ∈ [3]})` | `defect α₁ v₁ α₂ v₂ α₃ v₃` |
| `P` (pretender points), `T_z` | `R.pretPts u₁ u₂ s`, `R.consTriples u₁ u₂ s B z` |
| `N = max(|F|, (δn + 2)(δn + 1)/2)` | `max (Fintype.card F) ((n - s + 2) * (n - s + 1) / 2)` (exact division) |
-/

/-!
## Reading guide for newcomers to Lean: the proofs

The reading guide of `BEEP/Affine/Defs.lean` explains the notation (types, statements, arguments,
structures, finite sets, polynomials, numbers). This one explains how to read a proof; it
follows the one of `2-deep-fold-lemma/lean/DeepFold/Lemma1.lean`, with a few more tactics.

**Working with proofs.**
* from `h : P ∧ Q` we get `h.1 : P` and `h.2 : Q` (so `h.2.1` is the first part of `h.2`);
* from `h : P ↔ Q` we get `h.mp : P → Q` and `h.mpr : Q → P`;
* `⟨a, b⟩` is a proof of `P ∧ Q` made of `a : P` and `b : Q`, or a proof of `∃ x, P x` made of
  a witness `a` and a proof `b : P a`;
* `¬ P` is by definition `P → False`: a proof of `¬ P` turns a proof of `P` into a
  contradiction;
* `h.trans h'` chains `h : a ≤ b` and `h' : b ≤ c` into `a ≤ c` (also for `=`), and
  `h.symm : b = a` flips `h : a = b`;
* `rfl` proves `a = a`, and more generally `a = b` when both sides are equal by definition.

**Tactic proofs.** After `:= by` comes a list of *tactics*. Lean keeps track of the current
*goal* (what remains to be proved) and of the hypotheses available. In the editor the goal is
displayed after the symbol `⊢`, which is also how tactics refer to it (`at h ⊢` means "in `h`
and in the goal"). Two tactics on one line are separated by `;`. The tactics used here:
* `intro x h`: to prove `∀ x, P x → Q x`, take an arbitrary `x` and assume `h : P x`; `rintro`
  does the same and also splits pairs, as in `rintro ⟨i, j⟩`;
* `exact e`: the term `e` proves the goal;
* `apply e`: the goal follows from `e`, whose hypotheses become the new goals;
* `refine e`: like `exact`, but `e` may contain holes `?_`, which become new goals;
* `have h : P := ...`: prove an auxiliary fact `P` and call it `h` (`have := ...` calls it
  `this`);
* `set x := e with hx`: introduce the abbreviation `x` for `e`, replace `e` by `x` everywhere,
  and record `hx : x = e`;
* `unfold f`: replace `f` by its definition; `change P`: restate the goal as `P`, which must be
  equal to it by definition; `show P by tac`: a proof of `P` by the tactic `tac`, with the
  statement `P` written out;
* `constructor`: split a goal `P ∧ Q` (or `P ↔ Q`) into its two parts;
* `obtain ⟨a, b⟩ := h`: split `h : P ∧ Q` (or `h : ∃ x, P x`) into its two parts; a `-` in
  place of a name discards that part, and `rfl` substitutes an equation;
* `rcases h with h₁ | h₂`: argue by cases on `h : P ∨ Q`;
* `by_contra h`: argue by contradiction, with `h` the negation of the goal;
* `by_cases h : P`: split into the case `h : P` and the case `h : ¬ P`;
* `choose! S hS using h`: from `h : ∀ a ∈ A, ∃ S, P a S`, make a function `S` with
  `hS : ∀ a ∈ A, P a (S a)` (the axiom of choice);
* `·`: work on the first of the remaining goals (each `·` handles one goal);
* `rw [e₁, e₂]`: rewrite the goal with the equations (or equivalences) `e₁`, then `e₂`, from
  left to right (`← e` rewrites from right to left); `rw [...] at h` rewrites `h` instead.
  Afterwards `rw` closes the goal if it has become of the form `a = a`;
* `simp only [e₁, ...]`: simplify with exactly the listed facts; a definition in the list is
  unfolded; `simpa only [...] using h` simplifies the goal and `h` and closes the goal with `h`;
* `calc`: a chain `a = b := proof`, `_ ≤ c := proof`, ..., in which `_` stands for the right-hand
  side of the previous line;
* `h ▸ e`: rewrite the statement of `e` with the equation `h`.
Tactics that finish a goal by themselves:
* `omega`: linear arithmetic over `ℕ` and `ℤ`, including truncated subtraction (it treats a
  product of two unknowns as one unknown);
* `linarith`: linear arithmetic over ordered fields such as `ℝ`; `nlinarith`: the same, after
  multiplying hypotheses together;
* `positivity`: goals of the form `0 ≤ e` or `0 < e`;
* `ring`: identities in commutative rings (here `F`, `F[X]`, `ℕ` and `ℝ`);
* `linear_combination e`: an equation that is `e` (a combination of hypotheses with polynomial
  coefficients) up to `ring`;
* `field_simp`: clears denominators in fields; `norm_num`: numerical facts;
* `push_cast`: moves casts `↑` inwards, as in `↑(a * b) = ↑a * ↑b`; `exact_mod_cast h`: `h`, up
  to casts;
* `gcongr`: proves `f a ≤ f b` from `a ≤ b` when `f` is monotone.

**Mathlib lemmas.** Names such as `card_le_card` or `mem_filter` are lemmas of Mathlib. The
comments say what they state; their exact statements show up when hovering over them in the
editor, or with the command `#check card_le_card`.

**Reading interactively.** In VS Code with the Lean 4 extension, placing the cursor after a
tactic shows the hypotheses and the goal at that point in the "Lean Infoview" panel. This is the
best way to follow a proof: the comments describe the goal in words, the Infoview shows it
exactly.

**Plan.** The first section has facts on the polynomials of bounded degree (`mem_polysLT` and
three more), on the challenges (`eval_chal`, `chal_injective`, `eq_of_eval_chal_eq`), and the
arithmetic at the end of the proof of Lemma 5.5 (`pair_count_arith`). The section `Lemma33`
proves Lemma 5.5: `affine_line_pairs` is its second case, and `affine_line` is the lemma. The
section `TheU` has the polynomial `U` of the proof of Theorem 5.3 (`defect`) and its first two
properties. The section `Counting` follows the proof of Theorem 5.3: a chosen pretender for each
DEEP-MCA-bad challenge (`pt`); the bound on `|T_z|` (`card_collinear_le`, `card_goodTriples`,
`card_goodTriples_le`); the double count over the pretender points (`card_pretPts`,
`sum_card_consTriples`); the theorem for given answers (`affine_main_gen_nat`,
`affine_main_gen`); and the theorem with the maximal `A_z` (`affine_main_nat_proof`,
`affine_main_proof`, `fold_challenge_le_proof`). The last section, `WithDelta`, proves the
theorem with `δ` (`affine_main_delta_proof`).
-/

-- `open Finset Polynomial` lets us write `univ`, `card_le_card`, `C`, `X`, `eval_add`, ... instead
-- of `Finset.univ`, `Finset.card_le_card`, `Polynomial.C`, `Polynomial.X`, ..., and gives the
-- notation `F[X]`.
open Finset Polynomial

-- Switch off a warning (a "linter") that complains when a theorem does not use every `variable` of
-- its section. It has no effect on the mathematics.
set_option linter.unusedSectionVars false

-- From here to the end of the file, definitions may use non-constructive ingredients (the axiom
-- of choice in `pt`, real numbers in `affine_main_proof`), so Lean does not try to compile them
-- into executable code.
noncomputable section

-- All names defined below get the prefix `BEEP.Affine.` (e.g. `BEEP.Affine.Setup.affine_line`),
-- like those of `BEEP/Affine/Defs.lean`. The namespace is closed by `end BEEP.Affine` at the end
-- of the file.
namespace BEEP.Affine

-- Classical logic: every statement `P` may be treated as decidable (true or false). Lean needs
-- this to form `U.filter P` and `if P then _ else _` when no algorithm deciding `P` is provided.
open Classical

-- Standing assumptions, added as arguments to every definition and theorem below that uses them.
-- `F` is a finite field: a type with a field structure (`Field F`) and finitely many elements
-- (`Fintype F`, which provides `univ : Finset F` and the number `Fintype.card F`, our `q`).
variable {F : Type*} [Field F] [Fintype F]
-- `ι` is the finite set of positions of a word, and `n = Fintype.card ι`.
variable {ι : Type*} [Fintype ι]

/-! ### Polynomials of degree less than `k`, and challenges: the facts that the proof uses -/

/-- A polynomial lies in `polysLT F k` exactly when it has degree less than `k`. -/
theorem mem_polysLT {k : ℕ} {p : F[X]} : p ∈ polysLT F k ↔ p ∈ degreeLT F k := by
  -- Prove the two directions separately (`constructor` splits `↔` into `→` and `←`).
  constructor
  · -- `→`: an element of the image is the image of some `v` (`mem_image`); substitute it (`rfl`).
    intro hp
    obtain ⟨v, -, rfl⟩ := mem_image.mp hp
    -- An element of the subtype `degreeLT F k` carries the proof that it lies there (`.2`).
    exact ((degreeLTEquiv F k).symm v).2
  · -- `←`: `p` is the image of its own coefficient vector `degreeLTEquiv F k ⟨p, hp⟩`.
    intro hp
    refine mem_image.mpr ⟨degreeLTEquiv F k ⟨p, hp⟩, mem_univ _, ?_⟩
    -- `symm_apply_apply`: the inverse bijection undoes the bijection. The goal becomes `p = p`.
    rw [LinearEquiv.symm_apply_apply]

/-- If `X · p` has degree less than `k + 1`, then `p` has degree less than `k`. -/
theorem mem_degreeLT_of_X_mul {p : F[X]} {k : ℕ} (hp : X * p ∈ degreeLT F (k + 1)) :
    p ∈ degreeLT F k := by
  -- `mem_degreeLT`: `p ∈ degreeLT F k ↔ degree p < k`, and `degree_lt_iff_coeff_zero`:
  -- `degree p < k ↔ ∀ i ≥ k, p.coeff i = 0`. Now the goal is `∀ i ≥ k, p.coeff i = 0`.
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp ⊢
  intro i hi
  -- `coeff_X_mul`: `(X · p).coeff (i + 1) = p.coeff i`, read from right to left.
  rw [← coeff_X_mul]
  -- `i + 1 ≥ k + 1`, so the coefficient vanishes by `hp`.
  exact hp (i + 1) (by omega)

/-- A polynomial of degree less than `k + 1` has `natDegree ≤ k`. -/
theorem natDegree_le_of_mem_degreeLT {p : F[X]} {k : ℕ} (hp : p ∈ degreeLT F (k + 1)) :
    p.natDegree ≤ k := by
  -- `natDegree_le_iff_coeff_eq_zero`: `natDegree p ≤ k ↔ ∀ i > k, p.coeff i = 0`.
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  -- As in the previous theorem, `hp` says that the coefficients of index `≥ k + 1` vanish.
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
  -- `i > k` is `i ≥ k + 1` in `ℕ`.
  exact hp i hi

/-- A nonzero polynomial `U` vanishes at no more than `natDegree U` points of `F`. -/
theorem card_eval_eq_zero_le {U : F[X]} (hU : U ≠ 0) :
    (univ.filter fun y : F => U.eval y = 0).card ≤ U.natDegree := by
  -- `card_le_degree_of_subset_roots`: a finite set of roots of `U` has at most `natDegree U`
  -- elements. It asks that every element `y` of our set be in the multiset of roots `U.roots`.
  apply card_le_degree_of_subset_roots
  intro y hy
  -- `hy` says that `y` is in the filter, that is, `U.eval y = 0` (`mem_val`, `mem_filter`) ...
  rw [mem_val, mem_filter] at hy
  -- ... and `mem_roots`: for `U ≠ 0`, `y` is a root of `U` iff `U.eval y = 0`.
  exact (mem_roots hU).mpr hy.2

/-- The value of a challenge at `y`. -/
theorem eval_chal (α : F × F) (y : F) : (chal α).eval y = α.2 * y + α.1 := by
  -- Evaluation is a ring homomorphism (`eval_add`, `eval_mul`), `C a` evaluates to `a` (`eval_C`)
  -- and `X` to `y` (`eval_X`).
  simp only [chal, eval_add, eval_mul, eval_C, eval_X]

/-- A challenge has degree at most one. -/
-- Mathlib's `natDegree_linear_le`: `natDegree (C a * X + C b) ≤ 1`.
theorem natDegree_chal_le (α : F × F) : (chal α).natDegree ≤ 1 := natDegree_linear_le

/-- Distinct pairs give distinct challenges. -/
theorem chal_injective : Function.Injective (chal : F × F → F[X]) := by
  -- Let `chal α = chal β` (`h`). Compare the coefficients of `X⁰` and `X¹`.
  intro α β h
  have h0 : (chal α).coeff 0 = (chal β).coeff 0 := by rw [h]
  have h1 : (chal α).coeff 1 = (chal β).coeff 1 := by rw [h]
  -- `simp` computes these coefficients: `h0 : α.1 = β.1` and `h1 : α.2 = β.2`.
  simp [chal] at h0 h1
  -- Pairs with equal components are equal (`Prod.ext`).
  exact Prod.ext h0 h1

/-- Two challenges that agree at two distinct points are equal (a nonzero polynomial of degree at
most one has at most one root). -/
theorem eq_of_eval_chal_eq {α β : F × F} {y₁ y₂ : F} (hy : y₁ ≠ y₂)
    (h₁ : (chal α).eval y₁ = (chal β).eval y₁) (h₂ : (chal α).eval y₂ = (chal β).eval y₂) :
    α = β := by
  -- Now `h₁ : α.2 y₁ + α.1 = β.2 y₁ + β.1` and `h₂` the same at `y₂`.
  simp only [eval_chal] at h₁ h₂
  -- `τ = τ'`: subtracting, `(α.2 - β.2)(y₁ - y₂) = 0`, and `y₁ - y₂ ≠ 0`.
  have hτ : α.2 = β.2 := by
    have h : (α.2 - β.2) * (y₁ - y₂) = 0 := by linear_combination h₁ - h₂
    -- `mul_eq_zero`: a product vanishes iff a factor does; `resolve_right` discards the second
    -- factor, which is nonzero (`sub_ne_zero : a - b ≠ 0 ↔ a ≠ b`).
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hy))
  -- `σ = σ'`: from `h₁` and `τ = τ'`.
  have hσ : α.1 = β.1 := by linear_combination h₁ - y₁ * hτ
  exact Prod.ext hσ hτ

/-- The arithmetic at the end of the proof of Lemma 5.5: if `a · r (r - 1) ≤ d (d - 1)` with
`r = max 2 (d - e)`, then `a ≤ (e + 2)(e + 1)/2`. -/
-- In the lemma, `a` is the number of pretenders on the line, `d = |D|` and `e = n - s` (`δ n` in the
-- paper). The paper splits into `|D| ≤ δ n + 2` and `|D| > δ n + 2`, and so do we.
theorem pair_count_arith {a d e : ℕ}
    (h : a * (max 2 (d - e) * (max 2 (d - e) - 1)) ≤ d * (d - 1)) :
    a ≤ (e + 2) * (e + 1) / 2 := by
  -- `Nat.le_div_iff_mul_le`: `a ≤ y / 2 ↔ a · 2 ≤ y`. The goal becomes `a · 2 ≤ (e + 2)(e + 1)`.
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  -- Either `d ≤ e + 2` or `d > e + 2`.
  rcases le_or_gt d (e + 2) with hd | hd
  · -- First case. Here `r ≥ 2`, so `r (r - 1) ≥ 2`, ...
    have h2 : 2 ≤ max 2 (d - e) := le_max_left _ _
    have hr : 2 ≤ max 2 (d - e) * (max 2 (d - e) - 1) :=
      calc 2 = 2 * (2 - 1) := by norm_num
        -- (`Nat.mul_le_mul` multiplies two inequalities, and `Nat.sub_le_sub_right` subtracts `1`)
        _ ≤ max 2 (d - e) * (max 2 (d - e) - 1) := Nat.mul_le_mul h2 (Nat.sub_le_sub_right h2 1)
    -- ... and `d (d - 1) ≤ (e + 2)(e + 1)`, since `d ≤ e + 2`.
    have hdd : d * (d - 1) ≤ (e + 2) * (e + 1) :=
      calc d * (d - 1) ≤ (e + 2) * (e + 2 - 1) := Nat.mul_le_mul hd (Nat.sub_le_sub_right hd 1)
        _ = (e + 2) * (e + 1) := by rw [show e + 2 - 1 = e + 1 by omega]
    -- So `2a ≤ a r (r - 1) ≤ d (d - 1) ≤ (e + 2)(e + 1)`.
    calc a * 2 ≤ a * (max 2 (d - e) * (max 2 (d - e) - 1)) := Nat.mul_le_mul_left a hr
      _ ≤ d * (d - 1) := h
      _ ≤ (e + 2) * (e + 1) := hdd
  · -- Second case. Write `d = e + j + 2` with `j ≥ 1`; then `r = d - e = j + 2`.
    obtain ⟨j, rfl⟩ : ∃ j, d = e + j + 2 := ⟨d - e - 2, by omega⟩
    have hr : max 2 (e + j + 2 - e) = j + 2 := by
      rw [show e + j + 2 - e = j + 2 by omega]
      exact max_eq_right (by omega)
    -- Now `h : a (j + 2)(j + 1) ≤ (e + j + 2)(e + j + 1)`.
    rw [hr, show j + 2 - 1 = j + 1 by omega, show e + j + 2 - 1 = e + j + 1 by omega] at h
    -- The identity behind the paper's "both fractions decrease when |D| grows":
    -- `2 (e + j + 2)(e + j + 1) + j e ((e + 3) j + 3e + 5) = (e + 2)(e + 1)(j + 2)(j + 1)`.
    have key : 2 * ((e + j + 2) * (e + j + 1)) + j * e * ((e + 3) * j + 3 * e + 5) =
        (e + 2) * (e + 1) * ((j + 2) * (j + 1)) := by ring
    have hpos : 0 < (j + 2) * (j + 1) := by positivity
    -- Hence `2a (j + 2)(j + 1) ≤ 2 (e + j + 2)(e + j + 1) ≤ (e + 2)(e + 1)(j + 2)(j + 1)`, ...
    have hmain : a * 2 * ((j + 2) * (j + 1)) ≤ (e + 2) * (e + 1) * ((j + 2) * (j + 1)) :=
      calc a * 2 * ((j + 2) * (j + 1)) = 2 * (a * ((j + 2) * (j + 1))) := by ring
        _ ≤ 2 * ((e + j + 2) * (e + j + 1)) := Nat.mul_le_mul_left 2 h
        _ ≤ 2 * ((e + j + 2) * (e + j + 1)) + j * e * ((e + 3) * j + 3 * e + 5) :=
            Nat.le_add_right _ _
        _ = (e + 2) * (e + 1) * ((j + 2) * (j + 1)) := key
    -- ... and we cancel the positive factor `(j + 2)(j + 1)` (`Nat.le_of_mul_le_mul_right`).
    exact Nat.le_of_mul_le_mul_right hmain hpos

namespace Setup

-- `R` is the data of Section 5.1. Every definition and theorem below that mentions `R` takes it as
-- its first explicit argument, written with a dot: `R.affineFold`, `R.IsPretender`, ...
variable (R : Setup F ι)

-- The values of the weights at a point `y`.
theorem eval_lam₁ (α : F × F) (y : F) : (R.lam₁ α).eval y = R.a₁ + R.d₁ * (chal α).eval y := by
  simp only [lam₁, eval_add, eval_mul, eval_C]

theorem eval_lam₂ (α : F × F) (y : F) : (R.lam₂ α).eval y = R.a₂ + R.d₂ * (chal α).eval y := by
  simp only [lam₂, eval_add, eval_mul, eval_C]

/-! ### Lemma 5.5: a parameterized line contains few pretenders -/

section Lemma33

-- The two words and the agreement threshold, as in the section `Defs` of `Defs.lean`.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- The step behind "linearly dependent" in the proof of Lemma 5.5: if two challenges give fold
equations `λ₁(α)(x) ε₁ + λ₂(α)(x) ε₂ = 0` at one position, with `(ε₁, ε₂) ≠ (0, 0)`, then the two
challenges take the same value at `x`. Here `A = α(x)` and `B = α'(x)`, and in the lemma
`(ε₁, ε₂) = (u₁(i) - F₁(x_i), u₂(i) - F₂(x_i))`. -/
theorem eq_of_two_folds {A B ε₁ ε₂ : F} (hε : ¬ (ε₁ = 0 ∧ ε₂ = 0))
    (hA : (R.a₁ + R.d₁ * A) * ε₁ + (R.a₂ + R.d₂ * A) * ε₂ = 0)
    (hB : (R.a₁ + R.d₁ * B) * ε₁ + (R.a₂ + R.d₂ * B) * ε₂ = 0) : A = B := by
  -- Suppose `A ≠ B`. Then `(B - A)(a₁ d₂ - a₂ d₁) ≠ 0`, the determinant of the 2×2 system.
  by_contra hAB
  have hk : (B - A) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hAB)) (sub_ne_zero.mpr R.det_ne)
  -- We show `ε₁ = 0 ∧ ε₂ = 0`, contradicting `hε`.
  apply hε
  constructor
  · -- Eliminating `ε₂` from the two equations: the determinant times `ε₁` is `0`, ...
    have h : (B - A) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) * ε₁ = 0 := by
      linear_combination (R.a₂ + R.d₂ * B) * hA - (R.a₂ + R.d₂ * A) * hB
    -- ... so `ε₁ = 0`.
    exact (mul_eq_zero.mp h).resolve_left hk
  · -- Eliminating `ε₁`: the determinant times `ε₂` is `0`, so `ε₂ = 0`.
    have h : (B - A) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) * ε₂ = 0 := by
      linear_combination (R.a₁ + R.d₁ * A) * hB - (R.a₁ + R.d₁ * B) * hA
    exact (mul_eq_zero.mp h).resolve_left hk

/-- **Lemma 5.5, second case.** If `(F₁, F₂) ∈ C_λ^{≡2}`, then at most `(n - s + 2)(n - s + 1)/2`
challenges `α` make `λ₁(α) F₁ + λ₂(α) F₂` an `α`-pretender. -/
-- (In the paper, `(δ n + 2)(δ n + 1)/2`.)
theorem affine_line_pairs {F₁ F₂ : F[X]} (hF : R.Pairs F₁ F₂) :
    (univ.filter fun α : F × F =>
        R.IsPretender u₁ u₂ s α (R.lam₁ α * F₁ + R.lam₂ α * F₂)).card ≤
      (Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2 := by
  -- Idea (the paper's proof): each counted `α` has an agreement set `S α`, and `T α = S α ∩ D`
  -- has at least `max 2 (|D| - (n - s))` elements, where `D` is the set of positions where
  -- `(u₁, u₂)` differs from `(F₁, F₂)`. Two distinct `α` share at most one position of `D`, so
  -- the sets of ordered pairs of distinct positions of the `T α` are pairwise disjoint subsets of
  -- the ordered pairs of `D`. Counting these pairs gives the bound.
  -- `A`: the challenges counted in the statement (the goal becomes `#A ≤ ...`).
  set A := univ.filter fun α : F × F =>
    R.IsPretender u₁ u₂ s α (R.lam₁ α * F₁ + R.lam₂ α * F₂) with hA
  -- `D`: the positions `i` where `(u₁(i), u₂(i)) ≠ (F₁(x_i), F₂(x_i))`.
  set D : Finset ι := univ.filter fun i =>
    ¬ (u₁ i = F₁.eval (R.x i) ∧ u₂ i = F₂.eval (R.x i)) with hD
  -- For each `α ∈ A`, the definition of pretender gives a set `S` of size at least `s`, on which
  -- the line and the fold agree, and over which there is no CA up to one position.
  have hex : ∀ α ∈ A, ∃ S : Finset ι, s ≤ S.card ∧
      (∀ i ∈ S, (R.lam₁ α * F₁ + R.lam₂ α * F₂).eval (R.x i) = R.affineFold u₁ u₂ α i) ∧
        ¬ R.CAUpToOne u₁ u₂ S :=
    -- (`(mem_filter.mp hα).2` is the pretender property, and its `.2` is the part `∃ S, ...`.)
    fun α hα => (mem_filter.mp hα).2.2
  -- Choose such a set `S α` for every `α ∈ A` (the paper's `S_α`).
  choose! S hS using hex
  -- `T α = S α ∩ D`, written as a filter.
  set T : F × F → Finset ι := fun α => (S α).filter fun i => i ∈ D with hT
  -- (1) `|T α| ≥ 2`: otherwise `(F₁, F₂)` would give CA over `S α` up to one position.
  have hT2 : ∀ α ∈ A, 2 ≤ (T α).card := by
    intro α hα
    -- Suppose `|T α| < 2`, that is, `|T α| ≤ 1`.
    by_contra hlt
    -- We contradict `¬ CAUpToOne (S α)` by exhibiting CA: the pair `(F₁, F₂)` and the set
    -- `S' = S α \ D` (the positions of `S α` outside `D`).
    apply (hS α hα).2.2
    refine ⟨F₁, F₂, hF, (S α).filter fun i => i ∉ D, filter_subset _ _, ?_, ?_⟩
    · -- `|S α| ≤ |S'| + 1`: `S α` splits into `T α` and `S'` (`card_filter_add_card_filter_not`),
      -- and `|T α| ≤ 1`.
      have hsplit := card_filter_add_card_filter_not (s := S α) (fun i => i ∈ D)
      simp only [hT] at hlt
      omega
    · -- On `S'`, `(u₁, u₂)` agrees with `(F₁, F₂)`, by the definition of `D`.
      intro i hi
      have hiD := (mem_filter.mp hi).2
      simp only [hD, mem_filter, mem_univ, true_and, not_not] at hiD
      exact hiD
  -- (2) `|T α| ≥ |D| - (n - s)`: the part of `S α` outside `D` has at most `n - |D|` elements.
  have hTd : ∀ α ∈ A, D.card - (Fintype.card ι - s) ≤ (T α).card := by
    intro α hα
    -- `s ≤ |S α|`, and `|S α| = |T α| + |S α \ D|`.
    have hs := (hS α hα).1
    have hsplit := card_filter_add_card_filter_not (s := S α) (fun i => i ∈ D)
    -- `|S α \ D| ≤ |Dᶜ| = n - |D|` (`card_compl`).
    have hout : ((S α).filter fun i => i ∉ D).card ≤ Fintype.card ι - D.card := by
      rw [← card_compl]
      exact card_le_card fun i hi => mem_compl.mpr (mem_filter.mp hi).2
    -- `|S α| ≤ n` and `|D| ≤ n` (`card_le_univ`).
    have hSn : (S α).card ≤ Fintype.card ι := card_le_univ _
    have hDn : D.card ≤ Fintype.card ι := card_le_univ _
    -- Unfold `T` and conclude by arithmetic.
    simp only [hT]
    omega
  -- (3) Two challenges of `A` that share a position of `D` take the same value at its point.
  have hcommon : ∀ α ∈ A, ∀ β ∈ A, ∀ i, i ∈ T α → i ∈ T β →
      (chal α).eval (R.x i) = (chal β).eval (R.x i) := by
    intro α hα β hβ i hiα hiβ
    -- `i ∈ S α`, `i ∈ S β` and `i ∈ D`.
    simp only [hT, mem_filter] at hiα hiβ
    have hiD := hiα.2
    simp only [hD, mem_filter, mem_univ, true_and] at hiD
    -- `i ∈ D`: the vector `(ε₁, ε₂) = (u₁(i) - F₁(x_i), u₂(i) - F₂(x_i))` is nonzero.
    have hε : ¬ (u₁ i - F₁.eval (R.x i) = 0 ∧ u₂ i - F₂.eval (R.x i) = 0) := by
      simpa only [sub_eq_zero] using hiD
    -- The agreement of the line with the fold at `i`, for `α` and for `β`, ...
    have eα := (hS α hα).2.1 i hiα.1
    have eβ := (hS β hβ).2.1 i hiβ.1
    -- ... with everything evaluated at `x_i`:
    -- `λ₁(α)(x_i) F₁(x_i) + λ₂(α)(x_i) F₂(x_i) = λ₁(α)(x_i) u₁(i) + λ₂(α)(x_i) u₂(i)`.
    simp only [affineFold, eval_add, eval_mul, eval_lam₁, eval_lam₂] at eα eβ
    -- These are the two equations of `eq_of_two_folds`, after moving everything to one side.
    exact R.eq_of_two_folds hε (by linear_combination -eα) (by linear_combination -eβ)
  -- (3') So two distinct challenges of `A` share at most one position of `D`: two shared
  -- positions `i ≠ j` would give two points `x_i ≠ x_j` where the challenges agree.
  have hone : ∀ α ∈ A, ∀ β ∈ A, α ≠ β → ∀ i j, i ∈ T α → i ∈ T β → j ∈ T α → j ∈ T β →
      i = j := by
    intro α hα β hβ hαβ i j hiα hiβ hjα hjβ
    by_contra hij
    -- `R.x_inj.ne hij : x_i ≠ x_j`, since the evaluation points are distinct.
    exact hαβ (eq_of_eval_chal_eq (R.x_inj.ne hij) (hcommon α hα β hβ i hiα hiβ)
      (hcommon α hα β hβ j hjα hjβ))
  -- (4) Hence the sets `(T α).offDiag` of ordered pairs of distinct positions are pairwise
  -- disjoint (`PairwiseDisjoint`, as in Claim 1 of `Lemma1.lean`).
  have hdisj : (A : Set (F × F)).PairwiseDisjoint fun α => (T α).offDiag := by
    -- Let `α, β ∈ A` with `α ≠ β`; the goal is `Disjoint (T α).offDiag (T β).offDiag`, which
    -- `disjoint_left` turns into: no pair lies in both.
    intro α hα β hβ hαβ
    rw [Function.onFun, disjoint_left]
    -- A common pair `(i, j)` would have `i ≠ j` (`mem_offDiag`) with `i, j ∈ T α ∩ T β`.
    rintro ⟨i, j⟩ hp hp'
    rw [mem_offDiag] at hp hp'
    exact hp.2.2 (hone α hα β hβ hαβ i j hp.1 hp'.1 hp.2.1 hp'.2.1)
  -- ... and they all lie in `D.offDiag`, so the sum of their sizes is at most `|D.offDiag|`.
  have hsum : ∑ α ∈ A, (T α).offDiag.card ≤ D.offDiag.card := by
    -- The sum is the size of the (disjoint) union (`card_biUnion`), which lies in `D.offDiag`.
    rw [← card_biUnion hdisj]
    apply card_le_card
    intro p hp
    obtain ⟨α, -, hp⟩ := mem_biUnion.mp hp
    rw [mem_offDiag] at hp ⊢
    simp only [hT, mem_filter] at hp
    exact ⟨hp.1.2, hp.2.1.2, hp.2.2⟩
  -- (5) The count. Let `r = max 2 (|D| - (n - s))`, so `|T α| ≥ r` for every `α ∈ A`.
  set r := max 2 (D.card - (Fintype.card ι - s)) with hr
  -- Each `T α` has at least `r (r - 1)` ordered pairs (`offDiag_card`, `Nat.mul_sub_one`).
  have hterm : ∀ α ∈ A, r * (r - 1) ≤ (T α).offDiag.card := by
    intro α hα
    have hk : r ≤ (T α).card := max_le (hT2 α hα) (hTd α hα)
    rw [offDiag_card, ← Nat.mul_sub_one]
    exact Nat.mul_le_mul hk (Nat.sub_le_sub_right hk 1)
  -- So `|A| r (r - 1) ≤ ∑_{α ∈ A} |(T α).offDiag| ≤ |D.offDiag| = |D| (|D| - 1)`.
  have htotal : A.card * (r * (r - 1)) ≤ D.card * (D.card - 1) := by
    calc A.card * (r * (r - 1)) = ∑ α ∈ A, r * (r - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ α ∈ A, (T α).offDiag.card := sum_le_sum hterm
      _ ≤ D.offDiag.card := hsum
      _ = D.card * (D.card - 1) := by rw [offDiag_card, Nat.mul_sub_one]
  -- The arithmetic of `pair_count_arith` finishes the proof.
  exact pair_count_arith htotal

/-- The challenges `α` for which some `α`-pretender `c` lies on the parameterized line
`θ(α) = P/D + α · Q/D`, written as `D c = P + α Q` so as to stay with polynomials. -/
-- This is the paper's `A_θ^pret`, for the line `θ(α) = F_θ + α G_θ` of Definition 5.4 with
-- `F_θ = P/D` and `G_θ = Q/D`. Every pair of rational functions has this form, with a common
-- denominator `D ≠ 0`, and for `D ≠ 0` the polynomial `c` with `D c = P + α Q` is unique.
def lineHits (D P Q : F[X]) : Finset (F × F) :=
  univ.filter fun α => ∃ c, R.IsPretender u₁ u₂ s α c ∧ D * c = P + chal α * Q

/-- **Lemma 5.5.** A parameterized line contains at most `max(q, (n - s + 2)(n - s + 1)/2)`
pretenders: for `D ≠ 0`, at most that many challenges `α` have an `α`-pretender `c` with
`D c = P + α Q`. -/
-- (In the paper, `max(|F|, (δ n + 2)(δ n + 1)/2)`.)
theorem affine_line {D : F[X]} (hD : D ≠ 0) (P Q : F[X]) :
    (R.lineHits u₁ u₂ s D P Q).card ≤
      max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) := by
  -- The determinant `a₁ d₂ - a₂ d₁` is nonzero, so `C(det⁻¹) · (C a₁ C d₂ - C a₂ C d₁) = 1`.
  have hdet : R.a₁ * R.d₂ - R.a₂ * R.d₁ ≠ 0 := sub_ne_zero.mpr R.det_ne
  have hk : C (R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ * (C R.a₁ * C R.d₂ - C R.a₂ * C R.d₁) = 1 := by
    -- `C` is a ring homomorphism (`map_sub`, `map_mul`, `C_mul`), `det⁻¹ · det = 1`
    -- (`inv_mul_cancel₀`), and `C 1 = 1` (`C_1`).
    rw [show C R.a₁ * C R.d₂ - C R.a₂ * C R.d₁ = C (R.a₁ * R.d₂ - R.a₂ * R.d₁) by
      simp only [map_sub, map_mul], ← C_mul, inv_mul_cancel₀ hdet, C_1]
  -- The paper distinguishes whether the line is `α ↦ λ₁(α) F₁ + λ₂(α) F₂` with
  -- `(F₁, F₂) ∈ C_λ^{≡2}`. In polynomial terms: whether `P = D f` and `Q = D g` with `f ∈ C⁺` and
  -- `g ∈ C`, so that the line is `θ(α) = f + α g`.
  by_cases hpoly : ∃ f ∈ degreeLT F (R.ℓ + 1), ∃ g ∈ degreeLT F R.ℓ, P = D * f ∧ Q = D * g
  · -- Second case of the paper: the line is `θ(α) = f + α g`. Substitute `P = D f`, `Q = D g`.
    obtain ⟨f, hf, g, hg, rfl, rfl⟩ := hpoly
    -- `g ∈ C ⊆ C⁺` (`degreeLT_mono`).
    have hg' : g ∈ degreeLT F (R.ℓ + 1) := degreeLT_mono (Nat.le_succ _) hg
    -- The pair `(F₁, F₂)` of the paper, solution of `a₁ F₁ + a₂ F₂ = f`, `d₁ F₁ + d₂ F₂ = g`:
    -- `F₁ = det⁻¹ (d₂ f - a₂ g)` and `F₂ = det⁻¹ (a₁ g - d₁ f)`.
    set F₁ := C (R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ * (C R.d₂ * f - C R.a₂ * g) with hF₁
    set F₂ := C (R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ * (C R.a₁ * g - C R.d₁ * f) with hF₂
    -- `(F₁, F₂) ∈ C_λ^{≡2}`.
    have hpairs : R.Pairs F₁ F₂ := by
      refine ⟨?_, ?_, ?_⟩
      · -- `F₁ ∈ C⁺`: write the products by constants as scalar multiples (`smul_eq_C_mul`, from
        -- right to left), and use that `C⁺` is a subspace (closed under `•` and `-`).
        rw [hF₁, ← smul_eq_C_mul, ← smul_eq_C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _
          (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg'))
      · -- `F₂ ∈ C⁺`, in the same way.
        rw [hF₂, ← smul_eq_C_mul, ← smul_eq_C_mul, ← smul_eq_C_mul]
        exact Submodule.smul_mem _ _
          (Submodule.sub_mem _ (Submodule.smul_mem _ _ hg') (Submodule.smul_mem _ _ hf))
      · -- `d₁ F₁ + d₂ F₂ = g ∈ C`: the identity is `g` times `hk`, up to `ring`.
        have hsum : C R.d₁ * F₁ + C R.d₂ * F₂ = g := by
          rw [hF₁, hF₂]
          linear_combination g * hk
        rw [hsum]
        exact hg
    -- The line is `α ↦ λ₁(α) F₁ + λ₂(α) F₂`: `λ₁(α) F₁ + λ₂(α) F₂ = f + α g` for every `α`.
    have hline : ∀ α : F × F, R.lam₁ α * F₁ + R.lam₂ α * F₂ = f + chal α * g := by
      intro α
      rw [hF₁, hF₂]
      simp only [lam₁, lam₂]
      linear_combination (f + chal α * g) * hk
    -- So the counted challenges are among those of `affine_line_pairs`, whose bound is the second
    -- term of the maximum (`le_max_of_le_right`).
    refine le_max_of_le_right ((card_le_card ?_).trans (R.affine_line_pairs u₁ u₂ s hpairs))
    intro α hα
    -- `α` comes with a pretender `c` such that `D c = D f + α (D g)`.
    obtain ⟨c, hc, hDc⟩ := (mem_filter.mp hα).2
    -- Cancelling `D ≠ 0` (`mul_left_cancel₀`): `c = f + α g`.
    have hceq : c = f + chal α * g := mul_left_cancel₀ hD (by rw [hDc]; ring)
    -- So `c = λ₁(α) F₁ + λ₂(α) F₂`, and `α` is counted by `affine_line_pairs`.
    simp only [mem_filter, mem_univ, true_and]
    rw [hline α, ← hceq]
    exact hc
  · -- First case of the paper: then at most `q` challenges `α` have `θ(α) ∈ C⁺` at all, and the
    -- bound is the first term of the maximum (`le_max_of_le_left`).
    refine le_max_of_le_left ?_
    -- Suppose that more than `q` challenges are counted (`not_le : ¬ a ≤ b ↔ b < a`). We show that
    -- the line is of the form of the second case, contradicting `hpoly`.
    by_contra hlt
    rw [not_le] at hlt
    -- Every counted `α` has some `c ∈ C⁺` with `D c = P + α Q`.
    have hVc : ∀ α ∈ R.lineHits u₁ u₂ s D P Q,
        ∃ c ∈ degreeLT F (R.ℓ + 1), D * c = P + chal α * Q := by
      intro α hα
      obtain ⟨c, hc, hDc⟩ := (mem_filter.mp hα).2
      exact ⟨c, hc.1, hDc⟩
    -- More than `q` challenges: by the pigeonhole principle
    -- (`exists_ne_map_eq_of_card_lt_of_maps_to`), two distinct ones `α ≠ α'` have the same `σ`
    -- (the map `Prod.fst`), and two distinct ones `β ≠ β'` have the same `τ` (`Prod.snd`).
    have hcard : (univ : Finset F).card < (R.lineHits u₁ u₂ s D P Q).card := by
      rwa [card_univ]
    obtain ⟨α, hα, α', hα', hne, hσ⟩ :=
      exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := Prod.fst) (by intro x _; simp)
    obtain ⟨β, hβ, β', hβ', hne', hτ⟩ :=
      exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := Prod.snd) (by intro x _; simp)
    -- Their codewords: `D c = P + α Q`, `D c' = P + α' Q`, `D e = P + β Q`, `D e' = P + β' Q`.
    obtain ⟨c, hc, hDc⟩ := hVc α hα
    obtain ⟨c', hc', hDc'⟩ := hVc α' hα'
    obtain ⟨e, he, hDe⟩ := hVc β hβ
    obtain ⟨e', he', hDe'⟩ := hVc β' hβ'
    -- Since `α ≠ α'` have the same `σ`, their `τ` differ; since `β ≠ β'` have the same `τ`, their
    -- `σ` differ.
    have hτne : α.2 - α'.2 ≠ 0 := sub_ne_zero.mpr fun h => hne (Prod.ext hσ h)
    have hσne : β.1 - β'.1 ≠ 0 := sub_ne_zero.mpr fun h => hne' (Prod.ext h hτ)
    -- `gX = (τ - τ')⁻¹ (c - c') ∈ C⁺` satisfies `D gX = X Q`, since `α - α' = (τ - τ') X`.
    set gX := C (α.2 - α'.2)⁻¹ * (c - c') with hgX
    have hDgX : D * gX = X * Q := by
      have hdiff : chal α - chal α' = C (α.2 - α'.2) * X := by
        simp only [chal, hσ, map_sub]
        ring
      have hinv : C (α.2 - α'.2)⁻¹ * C (α.2 - α'.2) = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hτne, C_1]
      calc D * gX = C (α.2 - α'.2)⁻¹ * (D * c - D * c') := by rw [hgX]; ring
        _ = C (α.2 - α'.2)⁻¹ * ((chal α - chal α') * Q) := by rw [hDc, hDc']; ring
        _ = C (α.2 - α'.2)⁻¹ * C (α.2 - α'.2) * (X * Q) := by rw [hdiff]; ring
        _ = X * Q := by rw [hinv, one_mul]
    -- `g = (σ - σ')⁻¹ (e - e') ∈ C⁺` satisfies `D g = Q`, since `β - β' = σ - σ'` is a constant.
    set g := C (β.1 - β'.1)⁻¹ * (e - e') with hg
    have hDg : D * g = Q := by
      have hdiff : chal β - chal β' = C (β.1 - β'.1) := by
        simp only [chal, hτ, map_sub]
        ring
      have hinv : C (β.1 - β'.1)⁻¹ * C (β.1 - β'.1) = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hσne, C_1]
      calc D * g = C (β.1 - β'.1)⁻¹ * (D * e - D * e') := by rw [hg]; ring
        _ = C (β.1 - β'.1)⁻¹ * ((chal β - chal β') * Q) := by rw [hDe, hDe']; ring
        _ = C (β.1 - β'.1)⁻¹ * C (β.1 - β'.1) * Q := by rw [hdiff]; ring
        _ = Q := by rw [hinv, one_mul]
    -- Then `D (X g) = X Q = D gX`, and cancelling `D`: `X g = gX`. (This is the paper's "`F_θ`,
    -- `G_θ` and `X G_θ` are polynomials of degree at most `ℓ`".)
    have hXg : X * g = gX := mul_left_cancel₀ hD (by rw [hDgX, ← hDg]; ring)
    -- `gX ∈ C⁺`, as a multiple of `c - c'`; so `X g ∈ C⁺`, and hence `g ∈ C`
    -- (`mem_degreeLT_of_X_mul`); in particular `g ∈ C⁺`.
    have hgXC : gX ∈ degreeLT F (R.ℓ + 1) := by
      rw [hgX, ← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hc hc')
    have hXgC : X * g ∈ degreeLT F (R.ℓ + 1) := by rw [hXg]; exact hgXC
    have hgC : g ∈ degreeLT F R.ℓ := mem_degreeLT_of_X_mul hXgC
    have hgC' : g ∈ degreeLT F (R.ℓ + 1) := degreeLT_mono (Nat.le_succ _) hgC
    -- `f = e - β g ∈ C⁺`, since `β g = τ_β (X g) + σ_β g` is a combination of `X g, g ∈ C⁺`.
    have hfC : e - chal β * g ∈ degreeLT F (R.ℓ + 1) := by
      have hsplit : chal β * g = β.2 • (X * g) + β.1 • g := by
        simp only [chal, smul_eq_C_mul]
        ring
      rw [hsplit]
      exact Submodule.sub_mem _ he
        (Submodule.add_mem _ (Submodule.smul_mem _ _ hXgC) (Submodule.smul_mem _ _ hgC'))
    -- So `P = D f` and `Q = D g` with `f ∈ C⁺` and `g ∈ C`, contradicting `hpoly`.
    apply hpoly
    refine ⟨e - chal β * g, hfC, g, hgC, ?_, hDg.symm⟩
    -- `D (e - β g) = D e - β (D g) = (P + β Q) - β Q = P`.
    rw [mul_sub, hDe, ← hDg]
    ring

end Lemma33

end Setup

/-! ### The polynomial `U` of the proof of Theorem 5.3 -/

section TheU

/-- The polynomial `U((α₁, v₁), (α₂, v₂), (α₃, v₃)) = (α₃ - α₁)(v₂ - v₁) - (α₂ - α₁)(v₃ - v₁)` of
the proof of Theorem 5.3, where the challenges are multiplied as polynomials. -/
def defect (α₁ : F × F) (v₁ : F[X]) (α₂ : F × F) (v₂ : F[X]) (α₃ : F × F) (v₃ : F[X]) : F[X] :=
  (chal α₃ - chal α₁) * (v₂ - v₁) - (chal α₂ - chal α₁) * (v₃ - v₁)

/-- For `v₁, v₂, v₃ ∈ RS_{k+1}`, `U` has degree at most `k + 1` (in the paper, `ℓ + 1`). -/
theorem natDegree_defect_le {k : ℕ} {α₁ α₂ α₃ : F × F} {v₁ v₂ v₃ : F[X]}
    (h₁ : v₁ ∈ degreeLT F (k + 1)) (h₂ : v₂ ∈ degreeLT F (k + 1)) (h₃ : v₃ ∈ degreeLT F (k + 1)) :
    (defect α₁ v₁ α₂ v₂ α₃ v₃).natDegree ≤ k + 1 := by
  -- The difference of two challenges has degree at most one (`natDegree_sub_le`: the degree of a
  -- difference is at most the larger degree).
  have hA : ∀ α β : F × F, (chal α - chal β).natDegree ≤ 1 := fun α β =>
    (natDegree_sub_le _ _).trans (max_le (natDegree_chal_le α) (natDegree_chal_le β))
  -- `v₂ - v₁` and `v₃ - v₁` lie in `RS_{k+1}` (a subspace), so they have degree at most `k`.
  have h21 : (v₂ - v₁).natDegree ≤ k := natDegree_le_of_mem_degreeLT (Submodule.sub_mem _ h₂ h₁)
  have h31 : (v₃ - v₁).natDegree ≤ k := natDegree_le_of_mem_degreeLT (Submodule.sub_mem _ h₃ h₁)
  -- Each of the two products has degree at most `1 + k` (`natDegree_mul_le`: degrees add at
  -- most), and so does their difference.
  unfold defect
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have := hA α₃ α₁
    exact natDegree_mul_le.trans (by omega)
  · have := hA α₂ α₁
    exact natDegree_mul_le.trans (by omega)

/-- **The first step of the proof of Theorem 5.3, one direction.** If `U = 0`, then `(α₃, v₃)` lies
on the parameterized line through `(α₁, v₁)` and `(α₂, v₂)`: with `D = α₂ - α₁`,
`P = D v₁ - α₁ (v₂ - v₁)` and `Q = v₂ - v₁`, we have `D v₃ = P + α₃ Q`. -/
theorem onLine_of_defect_eq_zero {α₁ α₂ α₃ : F × F} {v₁ v₂ v₃ : F[X]}
    (h : defect α₁ v₁ α₂ v₂ α₃ v₃ = 0) :
    (chal α₂ - chal α₁) * v₃ =
      ((chal α₂ - chal α₁) * v₁ - chal α₁ * (v₂ - v₁)) + chal α₃ * (v₂ - v₁) := by
  -- The difference of the two sides is `-U`.
  unfold defect at h
  linear_combination (-1 : F[X]) * h

/-- **The first step of the proof of Theorem 5.3, other direction** (not used below). Three tuples
on one parameterized line `D v = P + α Q` (with `D ≠ 0`) have `U = 0`. -/
theorem defect_eq_zero_of_onLine {D P Q : F[X]} (hD : D ≠ 0) {α₁ α₂ α₃ : F × F}
    {v₁ v₂ v₃ : F[X]} (h₁ : D * v₁ = P + chal α₁ * Q) (h₂ : D * v₂ = P + chal α₂ * Q)
    (h₃ : D * v₃ = P + chal α₃ * Q) : defect α₁ v₁ α₂ v₂ α₃ v₃ = 0 := by
  -- `D U = (α₃ - α₁)(α₂ - α₁) Q - (α₂ - α₁)(α₃ - α₁) Q = 0` ...
  have h : D * defect α₁ v₁ α₂ v₂ α₃ v₃ = 0 := by
    unfold defect
    linear_combination (chal α₃ - chal α₁) * (h₂ - h₁) - (chal α₂ - chal α₁) * (h₃ - h₁)
  -- ... and `D ≠ 0`, so `U = 0` (`F[X]` has no zero divisors).
  exact (mul_eq_zero.mp h).resolve_left hD

end TheU

namespace Setup

variable (R : Setup F ι)

/-- **The second step of the proof of Theorem 5.3.** If three tuples are consistent with the same
`(z, b₁, b₂)`, then `φ_z(U) = 0`: `U(z_j) = 0` for every `j`. -/
theorem eval_defect_eq_zero {m : ℕ} {z : Fin m → F} {b : (Fin m → F) × (Fin m → F)}
    {α₁ α₂ α₃ : F × F} {v₁ v₂ v₃ : F[X]} (h₁ : R.Consistent z b α₁ v₁)
    (h₂ : R.Consistent z b α₂ v₂) (h₃ : R.Consistent z b α₃ v₃) (j : Fin m) :
    (defect α₁ v₁ α₂ v₂ α₃ v₃).eval (z j) = 0 := by
  -- The three consistency equations at `z_j`, with the weights evaluated (`eval_lam₁`, ...):
  -- `v_i(z_j) = (a₁ + d₁ α_i(z_j)) b₁(j) + (a₂ + d₂ α_i(z_j)) b₂(j)`.
  have e₁ := h₁ j
  have e₂ := h₂ j
  have e₃ := h₃ j
  simp only [eval_lam₁, eval_lam₂] at e₁ e₂ e₃
  -- Evaluation is multiplicative (`eval_mul`) and additive (`eval_sub`): this is the property of
  -- the zero evader that the paper uses.
  simp only [defect, eval_sub, eval_mul]
  -- Substitute the three values `v_i(z_j)`; what remains is a polynomial identity.
  rw [e₁, e₂, e₃]
  ring

/-! ### The proof of Theorem 5.3 -/

section Counting

-- The words, the threshold, the number `m` of samples, and a choice `B` of the vectors `b₁, b₂`
-- for every `z ∈ F^m`: `B z = (b₁, b₂)`. We call `b₁, b₂` the answers, since in a protocol they
-- are the prover's answers to the samples `z`; here `B` is any function. Theorem 5.3 is about
-- `|A_z|`, the largest `|A_{z, b₁, b₂}|` (`maxHits` of `Defs.lean`), and it follows from the case
-- of a `B` that attains this maximum at every `z` (`exists_worst_answers` below).
variable (u₁ u₂ : ι → F) (s : ℕ) {m : ℕ} (B : (Fin m → F) → (Fin m → F) × (Fin m → F))

/-- A chosen consistent pretender at the challenge `α` (junk if there is none): the paper's
`c_α` in the proof of Lemma 3.10, used in the third step of the proof of Theorem 5.3. -/
def pt (z : Fin m → F) (α : F × F) : F[X] :=
  -- `if h : P then x else y` is `x` if `P` holds and `y` otherwise; in the first branch `h` is a
  -- proof of `P`. From `h : ∃ c, ...` the axiom of choice gives a witness, `h.choose`.
  if h : ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z (B z) α c then h.choose else 0

/-- At a DEEP-MCA-bad challenge, the chosen point is a consistent pretender. -/
theorem pt_spec {z : Fin m → F} {α : F × F} (hα : α ∈ R.hits u₁ u₂ s z (B z)) :
    R.IsPretender u₁ u₂ s α (R.pt u₁ u₂ s B z α) ∧
      R.Consistent z (B z) α (R.pt u₁ u₂ s B z α) := by
  -- `α ∈ hits` unfolds to `DeepBad`, whose second part is the `∃ c, ...` that we need.
  have h : ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z (B z) α c := (mem_filter.mp hα).2.2
  -- Unfold `pt` and take the first branch of the `if` (`dif_pos h`): the point is `h.choose`.
  rw [pt, dif_pos h]
  -- `h.choose_spec` says that `h.choose` has the property required in `h`.
  exact h.choose_spec

/-- **The third step of the proof of Theorem 5.3, Lemma 5.5 part.** For two DEEP-MCA-bad challenges
`a ≠ b`, at most `N - 2` further ones have their chosen point on the parameterized line through the
chosen points at `a` and `b` (that is, `U = 0`), where `N = max(q, (n - s + 2)(n - s + 1)/2)`. -/
theorem card_collinear_le {z : Fin m → F} {a b : F × F} (ha : a ∈ R.hits u₁ u₂ s z (B z))
    (hb : b ∈ R.hits u₁ u₂ s z (B z)) (hab : a ≠ b) :
    ((((R.hits u₁ u₂ s z (B z)).erase a).erase b).filter fun c =>
        defect a (R.pt u₁ u₂ s B z a) b (R.pt u₁ u₂ s B z b) c (R.pt u₁ u₂ s B z c) = 0).card +
        2 ≤
      max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) := by
  -- Idea: `a`, `b` and these challenges are counted by Lemma 5.5 for the line through the chosen
  -- points at `a` and `b`. Abbreviations: `p` for the choice of points, `Col` for the set counted.
  set p := R.pt u₁ u₂ s B z with hp
  set Col := (((R.hits u₁ u₂ s z (B z)).erase a).erase b).filter fun c =>
    defect a (p a) b (p b) c (p c) = 0 with hCol
  -- The chosen points at `a` and `b` are consistent pretenders.
  have hpa := R.pt_spec u₁ u₂ s B ha
  have hpb := R.pt_spec u₁ u₂ s B hb
  -- The line through `(a, p a)` and `(b, p b)`: `D = b - a`, which is nonzero since `a ≠ b`.
  have hD : chal b - chal a ≠ 0 := sub_ne_zero.mpr (chal_injective.ne (Ne.symm hab))
  -- The main step: `{a} ∪ {b} ∪ Col` lies in `A_θ^pret` for this line (`lineHits`).
  have hsub : insert a (insert b Col) ⊆ R.lineHits u₁ u₂ s (chal b - chal a)
      ((chal b - chal a) * p a - chal a * (p b - p a)) (p b - p a) := by
    -- Let `α` be in `{a} ∪ {b} ∪ Col`; we exhibit a pretender on the line at `α`.
    intro α hα
    simp only [lineHits, mem_filter, mem_univ, true_and]
    rcases mem_insert.mp hα with h | hα
    · -- `α = a`: the point `p a` is a pretender and lies on the line (an identity: `ring`).
      rw [h]
      exact ⟨p a, hpa.1, by ring⟩
    rcases mem_insert.mp hα with h | hα
    · -- `α = b`: the same with `p b`.
      rw [h]
      exact ⟨p b, hpb.1, by ring⟩
    · -- `α ∈ Col`: `α` is DEEP-MCA-bad, and `U = 0` puts `p α` on the line
      -- (`onLine_of_defect_eq_zero`).
      rw [hCol, mem_filter] at hα
      have hαH : α ∈ R.hits u₁ u₂ s z (B z) := mem_of_mem_erase (mem_of_mem_erase hα.1)
      exact ⟨p α, (R.pt_spec u₁ u₂ s B hαH).1, onLine_of_defect_eq_zero hα.2⟩
  -- `b ∉ Col` and `a ∉ {b} ∪ Col`, since `Col ⊆ (H \ {a}) \ {b}` (`notMem_erase`).
  have hbC : b ∉ Col := fun h => by
    rw [hCol, mem_filter] at h
    exact (notMem_erase b _) h.1
  have haC : a ∉ insert b Col := by
    rw [mem_insert, not_or]
    refine ⟨hab, fun h => ?_⟩
    rw [hCol, mem_filter] at h
    exact (notMem_erase a _) (mem_of_mem_erase h.1)
  -- `#({a} ∪ {b} ∪ Col) ≤ #A_θ^pret ≤ N`, by Lemma 5.5 (`affine_line`).
  have := (card_le_card hsub).trans (R.affine_line u₁ u₂ s hD _ _)
  -- As `a` and `b` are new elements, `#({a} ∪ {b} ∪ Col) = #Col + 1 + 1`.
  rw [card_insert_of_notMem haC, card_insert_of_notMem hbC] at this
  omega

/-- Ordered triples of distinct DEEP-MCA-bad challenges whose chosen points have `U ≠ 0`. -/
def goodTriples (z : Fin m → F) : Finset ((F × F) × (F × F) × (F × F)) :=
  (R.hits u₁ u₂ s z (B z) ×ˢ R.hits u₁ u₂ s z (B z) ×ˢ R.hits u₁ u₂ s z (B z)).filter fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      defect t.1 (R.pt u₁ u₂ s B z t.1) t.2.1 (R.pt u₁ u₂ s B z t.2.1) t.2.2
        (R.pt u₁ u₂ s B z t.2.2) ≠ 0

/-- **The third step of the proof of Theorem 5.3.** With `h = |A_{z,b₁,b₂}|` DEEP-MCA-bad challenges
there are at least `h (h - 1) (h - N)` ordered triples of distinct ones whose chosen points have
`U ≠ 0`. -/
-- (This is the paper's `|A_z| (|A_z| - 1) (|A_z| - N) ≤ |T_z|`, the analogue of Lemma 3.10; the
-- triples are mapped into `T_z` by `card_goodTriples_le` below. The proof is that of Claim 3 of
-- `Lemma1.lean`.)
theorem card_goodTriples (z : Fin m → F) :
    (R.hits u₁ u₂ s z (B z)).card * ((R.hits u₁ u₂ s z (B z)).card - 1) *
        ((R.hits u₁ u₂ s z (B z)).card -
          max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)) ≤
      (R.goodTriples u₁ u₂ s B z).card := by
  -- The abbreviations `H`, `p`, `N` and `h`.
  set H := R.hits u₁ u₂ s z (B z) with hH
  set p := R.pt u₁ u₂ s B z with hp
  set N := max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)
    with hN
  set h := H.card with hh
  -- `N ≥ q ≥ 2` (a field has at least two elements: `Fintype.one_lt_card`).
  have hN2 : 2 ≤ N := by
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    have h2 : Fintype.card F ≤ N := le_max_left _ _
    omega
  -- for a fixed ordered pair `a ≠ b`, at least `h - N` third challenges give a good triple
  have inner : ∀ a ∈ H, ∀ b ∈ H.erase a, h - N ≤ (H.filter fun c =>
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ defect a (p a) b (p b) c (p c) ≠ 0).card := by
    intro a ha b hb
    -- From `b ∈ H \ {a}`: `a ≠ b` (`ne_of_mem_erase`, flipped) and `b ∈ H`.
    have hab : a ≠ b := (ne_of_mem_erase hb).symm
    have hbH : b ∈ H := mem_of_mem_erase hb
    -- `#(H \ {a, b}) = h - 2`.
    have hYcard : ((H.erase a).erase b).card = h - 2 := by
      rw [card_erase_of_mem hb, card_erase_of_mem ha, ← hh]
      omega
    -- The `c` with `U = 0`: `#(...) + 2 ≤ N` (previous theorem), with the abbreviations.
    have hcol := R.card_collinear_le u₁ u₂ s B ha hbH hab
    rw [← hH, ← hp, ← hN] at hcol
    -- `H \ {a, b}` splits into the `c` with `U = 0` and the others.
    have hsplit := card_filter_add_card_filter_not (s := (H.erase a).erase b)
      (fun c => defect a (p a) b (p b) c (p c) = 0)
    -- The others belong to the set counted in the goal.
    have hsubset : (((H.erase a).erase b).filter fun c => ¬ defect a (p a) b (p b) c (p c) = 0) ⊆
        H.filter fun c => a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ defect a (p a) b (p b) c (p c) ≠ 0 := by
      intro c hc
      rw [mem_filter] at hc ⊢
      -- `hc1 : c ≠ b ∧ c ≠ a ∧ c ∈ H` (`mem_erase`, twice).
      have hc1 := hc.1
      rw [mem_erase, mem_erase] at hc1
      exact ⟨hc1.2.2, hab, Ne.symm hc1.2.1, Ne.symm hc1.1, hc.2⟩
    have := card_le_card hsubset
    -- Arithmetic: `#(others) = (h - 2) - #(U = 0) ≥ (h - 2) - (N - 2) = h - N`.
    omega
  -- Summing over `b`: for `a ∈ H`, `(h - 1)(h - N) ≤ ∑_{b ∈ H} #{c | (a, b, c) is good}`.
  have step : ∀ a ∈ H, (h - 1) * (h - N) ≤ ∑ b ∈ H, (H.filter fun c =>
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ defect a (p a) b (p b) c (p c) ≠ 0).card := by
    intro a ha
    -- `(h - 1)(h - N) = ∑_{b ∈ H \ {a}} (h - N)`, since `#(H \ {a}) = h - 1`
    calc (h - 1) * (h - N) = ∑ b ∈ H.erase a, (h - N) := by
          rw [sum_const, card_erase_of_mem ha, smul_eq_mul]
      -- `≤ ∑_{b ∈ H \ {a}} #{...}`, term by term by `inner`
      _ ≤ ∑ b ∈ H.erase a, (H.filter fun c =>
            a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ defect a (p a) b (p b) c (p c) ≠ 0).card :=
          sum_le_sum (inner a ha)
      -- `≤ ∑_{b ∈ H} #{...}`: a sum of natural numbers can only grow with the index set
      _ ≤ _ := sum_le_sum_of_subset (erase_subset a H)
  -- `#goodTriples = ∑_{a ∈ H} ∑_{b ∈ H} #{c ∈ H | (a, b, c) is good}` (`card_filter`,
  -- `sum_product`).
  have hcount : (R.goodTriples u₁ u₂ s B z).card = ∑ a ∈ H, ∑ b ∈ H, (H.filter fun c =>
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ defect a (p a) b (p b) c (p c) ≠ 0).card := by
    simp only [goodTriples, card_filter, sum_product, hH, hp]
  -- `h (h - 1)(h - N) = ∑_{a ∈ H} (h - 1)(h - N) ≤ ∑_a ∑_b #{...} = #goodTriples`.
  calc h * (h - 1) * (h - N) = ∑ a ∈ H, (h - 1) * (h - N) := by
        rw [sum_const, smul_eq_mul, mul_assoc]
    _ ≤ _ := sum_le_sum step
    _ = _ := hcount.symm

/-! #### Double counting over triples of pretender points -/

/-- The set `P` of the proof of Theorem 5.3: the pairs `(α, c)` with `c` an `α`-pretender. -/
def pretPts : Finset ((F × F) × F[X]) :=
  ((univ : Finset (F × F)) ×ˢ polysLT F (R.ℓ + 1)).filter fun p => R.IsPretender u₁ u₂ s p.1 p.2

/-- `|P| ≤ q² L`: for each of the `q²` challenges, the pretenders are codewords of `C⁺` that agree
with the affine fold on at least `s` positions, and there are at most `L` of them. -/
theorem card_pretPts (L : ℕ) (hL : R.ListDecodable s L) :
    (R.pretPts u₁ u₂ s).card ≤ Fintype.card F ^ 2 * L := by
  -- Sort the points by their challenge `α = p.1` (`card_eq_sum_card_fiberwise`).
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ α ∈ (univ : Finset (F × F)), ((R.pretPts u₁ u₂ s).filter fun p => p.1 = α).card
      ≤ ∑ α ∈ (univ : Finset (F × F)), L := by
        -- Term by term: `p ↦ p.2` sends the fiber over `α` injectively into the set of
        -- polynomials of degree `≤ ℓ` that agree with the fold on at least `s` positions, which
        -- has at most `L` elements (`hL` for the word `affineFold u₁ u₂ α`).
        refine sum_le_sum fun α _ =>
          (card_le_card_of_injOn Prod.snd ?_ ?_).trans (hL (R.affineFold u₁ u₂ α))
        · -- It lands in that set: a pretender at `α` agrees with the fold on its set `S`, of
          -- size at least `s`, so on at least `s` positions.
          intro p hp
          simp only [pretPts, coe_filter, mem_filter, mem_product, mem_univ, true_and,
            Set.mem_setOf_eq] at hp ⊢
          obtain ⟨⟨hpoly, -, S, hS, hagree, -⟩, hα⟩ := hp
          refine ⟨hpoly, hS.trans (card_le_card fun i hi => ?_)⟩
          rw [mem_filter]
          exact ⟨mem_univ _, hα ▸ hagree i hi⟩
        · -- It is injective: `p.2 = p'.2` and `p.1 = α = p'.1` give `p = p'`.
          intro p hp p' hp' h
          simp only [pretPts, coe_filter, mem_filter, mem_product, mem_univ, true_and,
            Set.mem_setOf_eq] at hp hp'
          exact Prod.ext (hp.2.trans hp'.2.symm) h
    -- `∑_{α ∈ F × F} L = q² L` (`Fintype.card_prod`: `#(F × F) = q · q`).
    _ = Fintype.card F ^ 2 * L := by
        rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul, sq]

/-- Ordered triples of pretender points with distinct challenges and `U ≠ 0`. -/
def triples : Finset (((F × F) × F[X]) × ((F × F) × F[X]) × ((F × F) × F[X])) :=
  (R.pretPts u₁ u₂ s ×ˢ R.pretPts u₁ u₂ s ×ˢ R.pretPts u₁ u₂ s).filter fun t =>
    t.1.1 ≠ t.2.1.1 ∧ t.1.1 ≠ t.2.2.1 ∧ t.2.1.1 ≠ t.2.2.1 ∧
      defect t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2 ≠ 0

-- There are at most `|P|³` such triples.
theorem card_triples_le : (R.triples u₁ u₂ s).card ≤ (R.pretPts u₁ u₂ s).card ^ 3 := by
  -- A filter has at most as many elements as the set it filters (`card_filter_le`), ...
  calc (R.triples u₁ u₂ s).card
      ≤ (R.pretPts u₁ u₂ s ×ˢ R.pretPts u₁ u₂ s ×ˢ R.pretPts u₁ u₂ s).card :=
        card_filter_le _ _
    -- ... and `#(P × P × P) = #P ^ 3` (`card_product` twice, then `ring`).
    _ = (R.pretPts u₁ u₂ s).card ^ 3 := by rw [card_product, card_product]; ring

/-- The set `T_z` of the proof of Theorem 5.3: the triples of `triples` whose three points are
consistent with `(z, B z)`. -/
def consTriples (z : Fin m → F) :
    Finset (((F × F) × F[X]) × ((F × F) × F[X]) × ((F × F) × F[X])) :=
  (R.triples u₁ u₂ s).filter fun t => R.Consistent z (B z) t.1.1 t.1.2 ∧
    R.Consistent z (B z) t.2.1.1 t.2.1.2 ∧ R.Consistent z (B z) t.2.2.1 t.2.2.2

/-- **The last step of the proof of Theorem 5.3.** A triple with `U ≠ 0` belongs to `T_z` for at
most `(ℓ + 1)^m` of the `z ∈ F^m`, since every `z_j` must be a root of `U`, a nonzero polynomial
of degree at most `ℓ + 1`. Hence `∑_z |T_z| ≤ #triples · (ℓ + 1)^m`. -/
theorem sum_card_consTriples :
    ∑ z : Fin m → F, (R.consTriples u₁ u₂ s B z).card ≤
      (R.triples u₁ u₂ s).card * (R.ℓ + 1) ^ m := by
  -- Write `#consTriples(z)` as `∑_{t ∈ triples} [t is consistent with z]` (`card_filter`), and
  -- exchange the two sums (`sum_comm`).
  simp only [consTriples, card_filter]
  rw [sum_comm]
  calc ∑ t ∈ R.triples u₁ u₂ s, ∑ z : Fin m → F,
        (if R.Consistent z (B z) t.1.1 t.1.2 ∧ R.Consistent z (B z) t.2.1.1 t.2.1.2 ∧
          R.Consistent z (B z) t.2.2.1 t.2.2.2 then 1 else 0)
      ≤ ∑ t ∈ R.triples u₁ u₂ s, (R.ℓ + 1) ^ m := by
        -- Term by term: fix a triple `t ∈ triples` (`ht`).
        refine sum_le_sum fun t ht => ?_
        -- Back from indicators to a size: the goal is `#{z | t is consistent with z} ≤ (ℓ+1)^m`.
        rw [← card_filter]
        -- Unfold `t ∈ triples`: its three points are pretenders (`h₁ h₂ h₃`, whose first parts
        -- say that the polynomials lie in `C⁺`) and `U ≠ 0` (`hdef`).
        simp only [triples, pretPts, mem_filter, mem_product, mem_univ, true_and] at ht
        obtain ⟨⟨⟨-, h₁⟩, ⟨-, h₂⟩, ⟨-, h₃⟩⟩, -, -, -, hdef⟩ := ht
        -- `K`: the roots of `U` in `F`.
        set K := univ.filter fun y : F =>
          (defect t.1.1 t.1.2 t.2.1.1 t.2.1.2 t.2.2.1 t.2.2.2).eval y = 0 with hK
        -- `#K ≤ natDegree U ≤ ℓ + 1` (`card_eval_eq_zero_le`, `natDegree_defect_le`).
        have hKcard : K.card ≤ R.ℓ + 1 :=
          (card_eval_eq_zero_le hdef).trans (natDegree_defect_le h₁.1 h₂.1 h₃.1)
        -- Every consistent `z` has all its coordinates in `K`, so it lies in `K^m`
        -- (`Fintype.piFinset fun _ => K`).
        calc (univ.filter fun z : Fin m → F => R.Consistent z (B z) t.1.1 t.1.2 ∧
              R.Consistent z (B z) t.2.1.1 t.2.1.2 ∧ R.Consistent z (B z) t.2.2.1 t.2.2.2).card
            ≤ (Fintype.piFinset fun _ : Fin m => K).card := by
              refine card_le_card fun z hz => ?_
              simp only [mem_filter, mem_univ, true_and] at hz
              rw [Fintype.mem_piFinset]
              intro j
              simp only [hK, mem_filter, mem_univ, true_and]
              -- `U(z_j) = 0` by the second step of the proof (`eval_defect_eq_zero`).
              exact R.eval_defect_eq_zero hz.1 hz.2.1 hz.2.2 j
          -- `#(K^m) = #K ^ m` ...
          _ = K.card ^ m := Fintype.card_piFinset_const K m
          -- ... `≤ (ℓ + 1)^m`.
          _ ≤ (R.ℓ + 1) ^ m := Nat.pow_le_pow_left hKcard m
    -- `∑_{t ∈ triples} (ℓ + 1)^m = #triples · (ℓ + 1)^m`.
    _ = (R.triples u₁ u₂ s).card * (R.ℓ + 1) ^ m := by rw [sum_const, smul_eq_mul]

/-- The good triples of a fixed `z` inject into `T_z`: `(a, b, c) ↦ ((a, c_a), (b, c_b), (c, c_c))`
with the chosen points. -/
theorem card_goodTriples_le (z : Fin m → F) :
    (R.goodTriples u₁ u₂ s B z).card ≤ (R.consTriples u₁ u₂ s B z).card := by
  set p := R.pt u₁ u₂ s B z with hp
  -- The map is injective and lands in `consTriples` (`card_le_card_of_injOn`, two goals `?_`).
  refine card_le_card_of_injOn (fun t => ((t.1, p t.1), (t.2.1, p t.2.1), (t.2.2, p t.2.2)))
    ?_ ?_
  · -- It lands in `consTriples`. Let `t = (a, b, c)` be good: `a, b, c` are DEEP-MCA-bad
    -- (`h₁ h₂ h₃`), distinct (`hne₁ hne₂ hne₃`), and `U ≠ 0` (`hdef`).
    intro t ht
    simp only [goodTriples, coe_filter, mem_product, Set.mem_setOf_eq] at ht
    obtain ⟨⟨h₁, h₂, h₃⟩, hne₁, hne₂, hne₃, hdef⟩ := ht
    -- The three chosen points are consistent pretenders.
    have s₁ := R.pt_spec u₁ u₂ s B h₁
    have s₂ := R.pt_spec u₁ u₂ s B h₂
    have s₃ := R.pt_spec u₁ u₂ s B h₃
    -- Unfold what membership in `consTriples` requires ...
    simp only [consTriples, triples, pretPts, coe_filter, mem_filter, mem_product, mem_univ,
      true_and, Set.mem_setOf_eq]
    -- ... and supply it: each polynomial is in `polysLT` (`mem_polysLT`, from the first part of
    -- the pretender property) and is a pretender, the challenges are distinct, `U ≠ 0`, and the
    -- points are consistent.
    exact ⟨⟨⟨⟨mem_polysLT.mpr s₁.1.1, s₁.1⟩, ⟨mem_polysLT.mpr s₂.1.1, s₂.1⟩,
      ⟨mem_polysLT.mpr s₃.1.1, s₃.1⟩⟩, hne₁, hne₂, hne₃, hdef⟩, s₁.2, s₂.2, s₃.2⟩
  · -- It is injective: equal images have equal challenges (`Prod.mk.injEq`).
    intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.2.1.1 h.2.2.1)

/-! #### Theorem 5.3 for given answers -/

/-- The function `f(h) = h (h - 1) (h - N)` is monotone (as in `Lemma1.lean`). -/
theorem cubic_mono {t h N : ℕ} (hth : t ≤ h) : t * (t - 1) * (t - N) ≤ h * (h - 1) * (h - N) :=
  -- Multiply the three inequalities `t ≤ h`, `t - 1 ≤ h - 1` and `t - N ≤ h - N`.
  Nat.mul_le_mul (Nat.mul_le_mul hth (Nat.sub_le_sub_right hth 1)) (Nat.sub_le_sub_right hth N)

/-- **Theorem 5.3 for given answers, counting form.** Let `N = max(q, (n - s + 2)(n - s + 1)/2)`. If
`C⁺` is list decodable with list size `L` at agreement `s`, then for every `t` and every choice of
answers `B`, the number `K` of `z ∈ F^m` with at least `t` DEEP-MCA-bad challenges satisfies
`t (t - 1) (t - N) K ≤ (q² L)³ (ℓ + 1)^m`. For `t ≤ N` the left-hand side is `0`. -/
theorem affine_main_gen_nat (L t : ℕ) (hL : R.ListDecodable s L) :
    t * (t - 1) *
        (t - max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)) *
        (univ.filter fun z : Fin m → F => t ≤ (R.hits u₁ u₂ s z (B z)).card).card ≤
      (Fintype.card F ^ 2 * L) ^ 3 * (R.ℓ + 1) ^ m := by
  -- The proof of Theorem 5.3: a `z` with at least `t` DEEP-MCA-bad challenges has
  -- `|T_z| ≥ f(t)`, and `∑_z |T_z| ≤ (q² L)³ (ℓ + 1)^m`. Abbreviations `N` and `Zt` (the `z` with
  -- at least `t` DEEP-MCA-bad challenges).
  set N := max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)
    with hN
  set Zt := (univ : Finset (Fin m → F)).filter fun z =>
    t ≤ (R.hits u₁ u₂ s z (B z)).card with hZt
  -- For `z ∈ Zt`: `f(t) ≤ |T_z|`.
  have hz : ∀ z ∈ Zt, t * (t - 1) * (t - N) ≤ (R.consTriples u₁ u₂ s B z).card := by
    intro z hz
    simp only [hZt, mem_filter, mem_univ, true_and] at hz
    -- `f(t) ≤ f(|A_z|)` (`cubic_mono`) `≤ #goodTriples` (third step) `≤ |T_z|` (injection).
    calc t * (t - 1) * (t - N)
        ≤ (R.hits u₁ u₂ s z (B z)).card * ((R.hits u₁ u₂ s z (B z)).card - 1) *
            ((R.hits u₁ u₂ s z (B z)).card - N) := cubic_mono hz
      _ ≤ (R.goodTriples u₁ u₂ s B z).card := R.card_goodTriples u₁ u₂ s B z
      _ ≤ (R.consTriples u₁ u₂ s B z).card := R.card_goodTriples_le u₁ u₂ s B z
  -- Sum over `Zt` and bound the total by the double count.
  calc t * (t - 1) * (t - N) * Zt.card = ∑ z ∈ Zt, t * (t - 1) * (t - N) := by
        rw [sum_const, smul_eq_mul]; ring
    _ ≤ ∑ z ∈ Zt, (R.consTriples u₁ u₂ s B z).card := sum_le_sum hz
    -- sum over all `z ∈ F^m` instead of `Zt`
    _ ≤ ∑ z : Fin m → F, (R.consTriples u₁ u₂ s B z).card :=
        sum_le_sum_of_subset (filter_subset _ _)
    -- the last step of the proof (`sum_card_consTriples`)
    _ ≤ (R.triples u₁ u₂ s).card * (R.ℓ + 1) ^ m := R.sum_card_consTriples u₁ u₂ s B
    -- `#triples ≤ |P|³ ≤ (q² L)³` (`card_triples_le`, `card_pretPts`)
    _ ≤ (Fintype.card F ^ 2 * L) ^ 3 * (R.ℓ + 1) ^ m :=
        Nat.mul_le_mul_right _ ((R.card_triples_le u₁ u₂ s).trans
          (Nat.pow_le_pow_left (R.card_pretPts u₁ u₂ s L hL) 3))

/-- **Theorem 5.3 for given answers.** For every integer `t ≥ N + 1` and every choice of answers
`B`, for `z` uniform in `F^m`,
`Pr[z has at least t DEEP-MCA-bad challenges] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`. The
probability is written as the number of such `z` divided by `q^m`, and the denominator
`t (t - 1) (t - N)` is computed in `ℝ` (it is positive). -/
theorem affine_main_gen (L t : ℕ) (hL : R.ListDecodable s L)
    (ht : max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) + 1 ≤
      t) :
    ((univ.filter fun z : Fin m → F => t ≤ (R.hits u₁ u₂ s z (B z)).card).card : ℝ) /
        (Fintype.card F : ℝ) ^ m ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * (((R.ℓ : ℝ) + 1) / Fintype.card F) ^ m /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) -
          ((max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) :
            ℕ) : ℝ))) := by
  -- The counting form: `h : f(t) K ≤ (q² L)³ (ℓ + 1)^m` in `ℕ`.
  have h := R.affine_main_gen_nat u₁ u₂ s B L t hL
  -- `N`, and `K`: the number of `z` with at least `t` DEEP-MCA-bad challenges.
  set N := max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)
    with hN
  set K : ℕ := (univ.filter fun z : Fin m → F => t ≤ (R.hits u₁ u₂ s z (B z)).card).card with hK
  -- `q > 0` and `q^m > 0`.
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hW : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := pow_pos hq m
  -- `N ≥ q ≥ 2`, so `t ≥ N + 1 ≥ 3`, and no subtraction in `f(t)` is truncated.
  have hN2 : 2 ≤ N := by
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    have h2 : Fintype.card F ≤ N := le_max_left _ _
    omega
  have h1t : 1 ≤ t := by omega
  have hNt : N ≤ t := by omega
  -- In `ℝ`: `1 < t` and `N < t`, so `t (t - 1) (t - N) > 0`.
  have h1 : (1 : ℝ) < t := Nat.one_lt_cast.mpr (by omega)
  have h2 : (N : ℝ) < t := Nat.cast_lt.mpr (by omega)
  have hD : (0 : ℝ) < (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N) :=
    mul_pos (mul_pos (by linarith) (sub_pos.mpr h1)) (sub_pos.mpr h2)
  -- `h` in `ℝ` (`Nat.cast_le`), with the casts moved inwards and the subtractions of `ℕ` replaced
  -- by subtractions in `ℝ` (`Nat.cast_sub`, valid as `1 ≤ t` and `N ≤ t`).
  have h' : (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N) * K ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * ((R.ℓ : ℝ) + 1) ^ m := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub h1t, Nat.cast_sub hNt] at this
    exact this
  -- `div_le_div_iff₀ : a / b ≤ c / d ↔ a d ≤ c b` for `b, d > 0`, and then
  -- `((ℓ + 1)/q)^m = (ℓ + 1)^m / q^m` (`div_pow`).
  rw [div_le_div_iff₀ hW hD, div_pow]
  -- Reorder (`ring`), apply `h'`, and cancel `q^m` (`field_simp`).
  calc (K : ℝ) * ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N))
      = (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N) * K := by ring
    _ ≤ ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * ((R.ℓ : ℝ) + 1) ^ m := h'
    _ = ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 *
          (((R.ℓ : ℝ) + 1) ^ m / (Fintype.card F : ℝ) ^ m) * (Fintype.card F : ℝ) ^ m := by
        field_simp

/-! #### Theorem 5.3, with the vectors `b₁, b₂` that maximize `|A_{z,b₁,b₂}|` -/

-- `|A_{z, b₁, b₂}| ≤ |A_z|` for every `b = (b₁, b₂)`: `|A_z|` is the largest of these numbers.
theorem card_hits_le_maxHits (z : Fin m → F) (b : (Fin m → F) × (Fin m → F)) :
    (R.hits u₁ u₂ s z b).card ≤ R.maxHits u₁ u₂ s z :=
  -- `le_sup : b ∈ U → f b ≤ U.sup f`.
  le_sup (f := fun b : (Fin m → F) × (Fin m → F) => (R.hits u₁ u₂ s z b).card)
    (mem_univ b)

-- The maximum is attained: some `b = (b₁, b₂)` has exactly `|A_z|` DEEP-MCA-bad challenges at `z`
-- (the paper's `b₁*, b₂*`).
theorem exists_eq_maxHits (z : Fin m → F) :
    ∃ b : (Fin m → F) × (Fin m → F),
      (R.hits u₁ u₂ s z b).card = R.maxHits u₁ u₂ s z := by
  -- `exists_mem_eq_sup : U.Nonempty → ∃ i ∈ U, U.sup f = f i`, with `U = univ` (nonempty).
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup (univ : Finset ((Fin m → F) × (Fin m → F)))
    univ_nonempty fun b => (R.hits u₁ u₂ s z b).card
  exact ⟨b, hb.symm⟩

-- A choice of such a pair for every `z`: a function `B'` such that `B' z` attains `|A_z|`. (In the
-- paper, `b₁*, b₂*` depend on `z` in the same way.)
theorem exists_worst_answers :
    ∃ B' : (Fin m → F) → (Fin m → F) × (Fin m → F),
      ∀ z, (R.hits u₁ u₂ s z (B' z)).card = R.maxHits u₁ u₂ s z := by
  -- The axiom of choice (`Classical.axiom_of_choice`) applied to `exists_eq_maxHits`.
  obtain ⟨b, hb⟩ := Classical.axiom_of_choice (R.exists_eq_maxHits u₁ u₂ s (m := m))
  exact ⟨b, hb⟩

/-- **Proof of `affine_main_nat`** (Theorem 5.3, counting form). `BEEP/Affine/Theorem.lean` states
this theorem again, under the name `affine_main_nat`, and explains it. -/
theorem affine_main_nat_proof (L t : ℕ) (hL : R.ListDecodable s L) :
    t * (t - 1) *
        (t - max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)) *
        (univ.filter fun z : Fin m → F => t ≤ R.maxHits u₁ u₂ s z).card ≤
      (Fintype.card F ^ 2 * L) ^ 3 * (R.ℓ + 1) ^ m := by
  -- A worst-case choice `B'`, with `hB' : ∀ z, |A_{z, B' z}| = |A_z|`.
  obtain ⟨B', hB'⟩ := R.exists_worst_answers u₁ u₂ s (m := m)
  -- Replace `|A_z|` by `|A_{z, B' z}|` in the goal (`hB'` from right to left).
  simp only [← hB']
  -- This is `affine_main_gen_nat` for the choice `B'`.
  exact R.affine_main_gen_nat u₁ u₂ s B' L t hL

/-- **Proof of `affine_main`** (Theorem 5.3 with the integer agreement threshold `s`).
`BEEP/Affine/Theorem.lean` states this theorem again, under the name `affine_main`, and explains it.
-/
theorem affine_main_proof (L t : ℕ) (hL : R.ListDecodable s L)
    (ht : max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) + 1 ≤
      t) :
    ((univ.filter fun z : Fin m → F => t ≤ R.maxHits u₁ u₂ s z).card : ℝ) /
        (Fintype.card F : ℝ) ^ m ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * (((R.ℓ : ℝ) + 1) / Fintype.card F) ^ m /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) -
          ((max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) :
            ℕ) : ℝ))) := by
  -- A worst-case choice `B'`, as in `affine_main_nat`.
  obtain ⟨B', hB'⟩ := R.exists_worst_answers u₁ u₂ s (m := m)
  simp only [← hB']
  -- This is `affine_main_gen` for the choice `B'`.
  exact R.affine_main_gen u₁ u₂ s B' L t hL ht

/-- **Proof of `fold_challenge_le`** (how Theorem 5.3 is used: the fold challenge).
`BEEP/Affine/Theorem.lean` states this theorem again, under the name `fold_challenge_le`, and
explains it. -/
theorem fold_challenge_le_proof (z : Fin m → F) (b : (Fin m → F) × (Fin m → F)) (t : ℕ)
    (hz : R.maxHits u₁ u₂ s z < t) :
    ((univ.filter fun α : F × F => R.DeepBad u₁ u₂ s z b α).card : ℝ) /
        (Fintype.card (F × F) : ℝ) ≤ ((t : ℝ) - 1) / (Fintype.card F : ℝ) ^ 2 := by
  -- In `ℕ`: `|A_{z, b}| ≤ |A_z| < t`, so `|A_{z, b}| + 1 ≤ t`.
  have h : (R.hits u₁ u₂ s z b).card + 1 ≤ t := by
    have := R.card_hits_le_maxHits u₁ u₂ s z b
    omega
  -- The same in `ℝ`.
  have h' : ((R.hits u₁ u₂ s z b).card : ℝ) + 1 ≤ t := by exact_mod_cast h
  -- `#(F × F) = q · q = q²`.
  rw [Fintype.card_prod, Nat.cast_mul, ← sq]
  -- The filter is `A_{z, b}` by definition (`hits`), ...
  change ((R.hits u₁ u₂ s z b).card : ℝ) / _ ≤ _
  -- ... both sides are divided by `q² ≥ 0` (`gcongr`), and `|A_{z, b}| ≤ t - 1` (`linarith`).
  gcongr
  linarith

end Counting

/-! ### Theorem 5.3 with the proximity parameter `δ` -/

section WithDelta

-- In this section `u₁ u₂` are the words and `m` is the number of samples.
variable (u₁ u₂ : ι → F) {m : ℕ}

/-- For `k ≤ n`, a codeword of `RS_k` has a single polynomial of degree `< k`: evaluation at the
`n` distinct points is injective on the polynomials of degree `< k`. -/
theorem eval_injOn {k : ℕ} (hk : k ≤ Fintype.card ι) :
    Set.InjOn (fun p : F[X] => fun i => p.eval (R.x i)) (polysLT F k : Set F[X]) := by
  -- Let `p, q` of degree `< k` have the same values at all the points.
  intro p hp q hq hpq
  have hp' := mem_degreeLT.mp (mem_polysLT.mp hp)
  have hq' := mem_degreeLT.mp (mem_polysLT.mp hq)
  -- `eq_of_degrees_lt_of_eval_index_eq`: two polynomials of degree `< n` that agree at `n`
  -- distinct points are equal (here the points `x_i`, `i ∈ univ`, distinct by `R.x_inj`).
  refine eq_of_degrees_lt_of_eval_index_eq (v := R.x) univ R.x_inj.injOn ?_ ?_ ?_
  · -- `degree p < k ≤ n = #univ`.
    rw [card_univ]
    exact hp'.trans_le (Nat.cast_le.mpr hk)
  · rw [card_univ]
    exact hq'.trans_le (Nat.cast_le.mpr hk)
  · -- The values agree, by `hpq` at each position `i`.
    intro i _
    exact congrFun hpq i

/-- For `k ≤ n`, counting the codewords of `RS_k` with a property is counting their polynomials. -/
theorem card_close_rsWords {k : ℕ} (hk : k ≤ Fintype.card ι) (P : (ι → F) → Prop) :
    ((R.rsWords k).filter P).card =
      ((polysLT F k).filter fun p => P fun i => p.eval (R.x i)).card := by
  -- The filter of an image is the image of a filter (`filter_image`), and an image under a map
  -- that is injective on the set has the same size (`card_image_of_injOn`).
  rw [rsWords, filter_image, card_image_of_injOn]
  -- The map is injective on the filter, since it is injective on all of `polysLT F k`.
  exact Set.InjOn.mono (coe_subset.mpr (filter_subset _ _)) (R.eval_injOn hk)

/-- With `s = ⌈(1 - δ) n⌉`, the pretenders of `IsPretender` are those of Definition 5.1, with
agreement sets of size at least `(1 - δ) n`. -/
theorem isPretender_ceil_iff (δ : ℝ) (α : F × F) (c : F[X]) :
    R.IsPretender u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ α c ↔
      c ∈ degreeLT F (R.ℓ + 1) ∧ ∃ S : Finset ι, (1 - δ) * Fintype.card ι ≤ S.card ∧
        (∀ i ∈ S, c.eval (R.x i) = R.affineFold u₁ u₂ α i) ∧ ¬ R.CAUpToOne u₁ u₂ S := by
  -- `Nat.ceil_le : ⌈y⌉₊ ≤ k ↔ y ≤ k`.
  simp only [IsPretender, Nat.ceil_le]

/-- The list decodability of Theorem 5.3, "`C⁺` is `(δ, L)`-list decodable": if every word has at
most `L` codewords of `C⁺` at relative Hamming distance at most `δ` (at most `δ n` positions where
they differ), then `C⁺` is list decodable with list size `L` at agreement `⌈(1 - δ) n⌉`. -/
theorem listDecodable_of_delta {δ : ℝ} {L : ℕ} (hn : R.ℓ + 1 ≤ Fintype.card ι)
    (hL : ∀ w : ι → F, ((R.rsWords (R.ℓ + 1)).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L) :
    R.ListDecodable ⌈(1 - δ) * Fintype.card ι⌉₊ L := by
  intro w
  -- Count the close codewords through their polynomials (`card_close_rsWords`).
  have h := hL w
  rw [R.card_close_rsWords hn] at h
  -- A polynomial that agrees with `w` on at least `⌈(1 - δ) n⌉` positions differs from `w` on at
  -- most `δ n` positions, so the set to bound lies in the set of `h`.
  refine le_trans (card_le_card fun p hp => ?_) h
  simp only [mem_filter, ne_eq] at hp ⊢
  refine ⟨hp.1, ?_⟩
  -- The positions split into those where `p(x_i) = w(i)` and the others.
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun i => p.eval (R.x i) = w i)
  rw [card_univ] at hsplit
  -- `(1 - δ) n ≤ #agree` (`Nat.ceil_le`), and `#agree + #differ = n` in `ℝ`.
  have hagree : (1 - δ) * Fintype.card ι ≤
      ((univ.filter fun i => p.eval (R.x i) = w i).card : ℝ) := Nat.ceil_le.mp hp.2
  have hsplit' : ((univ.filter fun i => p.eval (R.x i) = w i).card : ℝ) +
      ((univ.filter fun i => ¬ p.eval (R.x i) = w i).card : ℝ) = Fintype.card ι := by
    exact_mod_cast hsplit
  -- So `#differ = n - #agree ≤ n - (1 - δ) n = δ n`.
  linarith

/-- **Proof of `affine_main_delta`** (Theorem 5.3, as stated in the paper).
`BEEP/Affine/Theorem.lean` states this theorem again, under the name `affine_main_delta`, and
explains it. -/
theorem affine_main_delta_proof {δ : ℝ} (hδ : 0 ≤ δ) (L t : ℕ) (hn : R.ℓ + 1 ≤ Fintype.card ι)
    (hL : ∀ w : ι → F, ((R.rsWords (R.ℓ + 1)).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (ht : max (Fintype.card F : ℝ)
        ((δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2) + 1 ≤ t) :
    ((univ.filter fun z : Fin m → F =>
        t ≤ R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z).card : ℝ) /
        (Fintype.card F : ℝ) ^ m ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * (((R.ℓ : ℝ) + 1) / Fintype.card F) ^ m /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - max (Fintype.card F : ℝ)
          ((δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2))) := by
  -- Idea: `affine_main` with `s = ⌈(1 - δ) n⌉`, whose `N` (with `n - s ≤ δ n`) is at most the `N`
  -- of the paper; a smaller `N` gives a larger denominator, hence a smaller bound.
  -- Abbreviations: `s`, the integer threshold `N` of `affine_main`, and the real `N` of the paper.
  set s := ⌈(1 - δ) * Fintype.card ι⌉₊ with hs
  set N := max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)
    with hN
  set Nr := max (Fintype.card F : ℝ) ((δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2)
    with hNr
  -- `n - s ≤ δ n`: if `s ≤ n`, because `s ≥ (1 - δ) n` (`Nat.le_ceil`); otherwise `n - s = 0`.
  have he : ((Fintype.card ι - s : ℕ) : ℝ) ≤ δ * Fintype.card ι := by
    rcases le_or_gt s (Fintype.card ι) with h | h
    · rw [Nat.cast_sub h]
      have : (1 - δ) * Fintype.card ι ≤ (s : ℝ) := Nat.le_ceil _
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      positivity
  -- Hence `N ≤ Nr`: the first terms are equal, and the natural division is at most the real one
  -- (`Nat.cast_div_le`), which grows with `n - s`.
  have hNle : (N : ℝ) ≤ Nr := by
    rw [hN, Nat.cast_max]
    apply max_le_max le_rfl
    calc (((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2 : ℕ) : ℝ)
        ≤ (((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) : ℕ) : ℝ) / 2 := Nat.cast_div_le
      _ = (((Fintype.card ι - s : ℕ) : ℝ) + 2) * (((Fintype.card ι - s : ℕ) : ℝ) + 1) / 2 := by
          push_cast; ring
      _ ≤ (δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2 := by gcongr
  -- So `t ≥ Nr + 1 ≥ N + 1`, in `ℕ`.
  have htN : N + 1 ≤ t := by
    have : (N : ℝ) + 1 ≤ t := by linarith
    exact_mod_cast this
  -- `affine_main` with `s` and `L` (list decodability by `listDecodable_of_delta`).
  have hmain := R.affine_main_proof u₁ u₂ s (m := m) L t (R.listDecodable_of_delta hn hL) htN
  refine hmain.trans ?_
  -- It remains to compare the denominators: `t (t - 1) (t - Nr) ≤ t (t - 1) (t - N)`, both
  -- positive (`div_le_div_of_nonneg_left`), with the same nonnegative numerator.
  have hq1 : (1 : ℝ) < Fintype.card F := Nat.one_lt_cast.mpr Fintype.one_lt_card
  have hNr1 : (Fintype.card F : ℝ) ≤ Nr := le_max_left _ _
  have hpos : 0 < (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - Nr) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_le_div_of_nonneg_left (by positivity) hpos
  -- `t - Nr ≤ t - N`, multiplied by `t (t - 1) ≥ 0`.
  exact mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)

end WithDelta

end Setup

end BEEP.Affine
