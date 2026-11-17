-- [AI-drafted (claude-fable-5-2), 2026-11-16, at the author's request: this whole file. It formalizes Theorem 3.4 (`t:main_thm`) of
-- `paper/main.typ`, together with Lemmas 3.7 to 3.10, on which its proof rests, and it is
-- commented in the style of `BEEP/AffineMain.lean`. Please review the statements against the
-- paper; the dictionary is at the end of the module documentation.]

-- A line starting with `--` is a comment, which Lean ignores. In this file each comment explains
-- the line, or the few lines, directly below it. The reading guide after the module documentation
-- explains the notation and every tactic used in the file.

-- Load Mathlib, Lean's library of formalized mathematics (fields, vector spaces, linear maps,
-- finite sets, sums, real numbers, ...). Every name used below and not defined in this file
-- (`Finset`, `card_le_card`, `map_smul`, ...) comes from Mathlib.
import Mathlib

/-!
# BEEP: Theorem 3.4 of the BEEP paper

A formalization of Theorem 3.4 of the BEEP paper (`paper/main.typ`, Section 3, "Better
Elimination of Pretenders", label `t:main_thm`, "For most `z ∈ Z`, there are few DEEP-MCA-bad
elements `α ∈ F`"), together with the four lemmas of its proof: Lemma 3.7 (label
`l:few_bad_points_on_line`, "A parameterized line contains few pretenders"), Lemma 3.8
(`l:colinear`, "Colinearity of codewords"), Lemma 3.9 (`l:colinear_zero`) and Lemma 3.10
(`l:third_moment_bound`). The numbers of theorems, lemmas and definitions are those of the PDF
compiled from `paper/main.typ` on November 16, 2026, which numbers them within sections; the
labels do not change when the numbers do.

## Setting (Sections 2.2, 2.3 and 3.1 of the paper)

* `F` is a finite field with `q = |F|` elements.
* The positions of a word form a finite type `ι` with `n = |ι|` elements, and a word is a
  function `ι → F`.
* The linear code `C ⊂ F^n` of dimension `ℓ` is given by its injective linear encoding map
  `Enc_C : F^ℓ → F^n` (Section 2.2), here `R.enc` (`R` collects the data that the paper fixes,
  see `Setup`). A codeword is represented by its message: `c : Fin R.ℓ → F` stands for the
  codeword `Enc_C(c)`, whose entries are `R.enc c i`. The paper does the same when it applies the
  zero evader to a codeword (`φ_z(Enc_C(w)) := φ_z(w)`, Section 3.1).
* Words are folded with the weights `λ₁(α) = a₁ + α d₁` and `λ₂(α) = a₂ + α d₂`, where
  `a₁ d₂ ≠ a₂ d₁`. The fold of `u₁, u₂` with the challenge `α ∈ F` is the word
  `λ₁(α) u₁ + λ₂(α) u₂`.
* The zero evader is a family of linear maps `φ_z : F^ℓ → F^m`, indexed by a finite nonempty type
  `Z` (Definition 2.3), here `R.φ z`. A number `ε ≥ 0` is an error bound of the evader if every
  nonzero `v ∈ F^ℓ` has `Pr_z[φ_z(v) = 0] ≤ ε` (`R.IsErrorBound ε`).
* The paper measures agreement with the proximity parameter `δ` (agreement sets of size at least
  `(1 - δ) n`). As in `BEEP/AffineMain.lean`, we use instead an integer agreement threshold `s`
  (agreement sets of size at least `s`), so that `δ n` becomes `n - s`. The last section of the
  file states the theorem with `δ` again, with `s = ⌈(1 - δ) n⌉`. For this `s` and `0 ≤ δ ≤ 1`,
  `n - s = ⌊δ n⌋` (and `n - s ≤ ⌊δ n⌋ ≤ δ n` for every `δ ≥ 0`), so the integer form is slightly
  stronger when `δ n` is not an integer.

## Main results

* `BEEP.Main.Setup.few_pretenders_on_line` (Lemma 3.7): a parameterized line `α ↦ c₁ + α c₂`
  contains at most `n - s + 1` pretenders.
* `BEEP.Main.defect_eq_zero_iff` (Lemma 3.8): for `α₁ ≠ α₂`, three tuples `(α_i, v_i)` lie on one
  parameterized line if and only if `U((α_i, v_i)) = 0`.
* `BEEP.Main.Setup.evader_defect_eq_zero` (Lemma 3.9): if three tuples are consistent with the
  same `(z, b₁, b₂)`, then `φ_z(U) = 0`.
* `BEEP.Main.Setup.third_moment_bound` (Lemma 3.10):
  `|A| (|A| - 1) (|A| - (n - s) - 1) ≤ |T_z|`, where `A` is the set of DEEP-MCA-bad elements at
  `z` for the answers `(b₁, b₂) = B z`, and `T_z` is defined with the same answers.
* `BEEP.Main.Setup.main_thm_nat` (Theorem 3.4, counting form): for every `t`,
  `t (t - 1) (t - (n - s) - 1) · #{z ∈ Z | |A_z| ≥ t} ≤ (q L)³ M`, where `M` bounds the number of
  `z` with `φ_z(v) = 0` for every nonzero `v`, and `|A_z|` is the largest number of DEEP-MCA-bad
  elements at `z` over all answers `b₁, b₂` (`maxHits`). The subtractions are those of `ℕ`, so
  for `t ≤ n - s + 1` the left-hand side is `0` and the statement says nothing.
* `BEEP.Main.Setup.main_thm` (Theorem 3.4): for every integer `t ≥ n - s + 2`, for `z` uniform in
  `Z`, `Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - (n - s) - 1))`.
* `BEEP.Main.Setup.main_thm_delta` (Theorem 3.4 as stated in the paper): the same with the
  proximity parameter `δ` and the relative Hamming distance in the list decodability of `C`: for
  every integer `t ≥ δ n + 2`, `Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - δ n - 1))`.
  `BEEP.Main.Setup.main_thm_delta_real` is the same for a real threshold `t`.
* `BEEP.Main.Setup.main_thm_delta_floor`: the same with `⌊δ n⌋` in place of `δ n`, for every
  integer `t ≥ ⌊δ n⌋ + 2`. When `δ n` is not an integer this is slightly stronger: it covers the
  threshold `t = ⌊δ n⌋ + 2`, which `main_thm_delta` does not, and its bound is smaller.
* `BEEP.Main.Setup.fold_challenge_le`: if `|A_z| < t`, then a uniform challenge is DEEP-MCA-bad
  with probability at most `(t - 1)/q`. With the least threshold of `main_thm_delta_floor`,
  `t = ⌊δ n⌋ + 2`, this is `(⌊δ n⌋ + 1)/q`, which is at most the term `(δ n + 1)/|F|` of the error
  `κ₂` of Theorem 4.3 (and equal to it when `δ n` is an integer). Theorem 4.3 is not formalized
  here.

## Dictionary paper ↔ Lean

| paper (Sections 2 and 3 of `paper/main.typ`) | Lean |
|---|---|
| `Enc_C : F^ℓ → C`, linear and injective | `R.enc`, `R.enc_inj` |
| a codeword `c ∈ C` | its message `c : Fin R.ℓ → F`; the entries of the codeword are `R.enc c i` |
| `λ₁(α)`, `λ₂(α)`, with `a₁ d₂ ≠ a₂ d₁` | `R.lam₁ α`, `R.lam₂ α`, `R.det_ne` |
| the fold `λ₁(α) · u₁ + λ₂(α) · u₂` | `R.fold u₁ u₂ α` |
| `(u₁, u₂)` has CA with `C` over `S` | `R.CA u₁ u₂ S` |
| `(1 - δ) n` | `s`; then `δ n` is `n - s` (`= ⌊δ n⌋` for `s = ⌈(1 - δ) n⌉` and `0 ≤ δ ≤ 1`) |
| `α` satisfies the `δ`-MCA property; `α` is MCA-bad (Definition 3.1) | `R.SatisfiesMCA u₁ u₂ s α`; `R.MCABad u₁ u₂ s α` |
| Definition 3.2, `c` is an `α`-pretender | `R.IsPretender u₁ u₂ s α c` |
| the zero evader `(φ_z)_{z ∈ Z}` (Definition 2.3); `ε` is an error bound | `R.φ`; `R.IsErrorBound ε` |
| Definition 3.3 (consistency); DEEP-MCA-bad element | `R.Consistent z b α c`; `R.DeepBad u₁ u₂ s z b α` |
| `A_{z, b₁, b₂}`; `|A_z|` (maximal over `b₁, b₂`) | `R.hits u₁ u₂ s (fun _ => b) z`; `R.maxHits u₁ u₂ s z` |
| `C` is `(δ, L)`-list decodable | `R.ListDecodable s L` (or `hL` of `main_thm_delta`) |
| Definition 3.6, a parameterized line `θ(α) = c_{θ,1} + α · c_{θ,2}` | `c₁ + α • c₂`, for messages `c₁ c₂` |
| `A_θ^pret` of Lemma 3.7 | `R.lineHits u₁ u₂ s c₁ c₂` |
| `U((α_i, v_i)_{i ∈ [3]})` | `defect α₁ v₁ α₂ v₂ α₃ v₃` |
| `P` (pretender points), `T_z` | `R.pretPts u₁ u₂ s`, `R.consTriples u₁ u₂ s B z` |
| `δ n + 1` (Lemma 3.7), `t ≥ δ n + 2` | `n - s + 1`, `n - s + 2 ≤ t` |

Not needed for Theorem 3.4 in this form, and so not assumed: that `n` is a power of two, that
`δ < 1`, that `ε ≤ 1` and that `L ≥ 1`. The injectivity of the encoding map is used only to count
codewords instead of messages in the form with `δ` (`card_filter_codewords`).
-/

/-!
## Reading guide for newcomers to Lean

This guide follows the one of `BEEP/AffineMain.lean`, with what is new here (linear maps, vectors).

**What Lean checks.** A Lean file is a list of definitions (`def`) and theorems (`theorem`). A
theorem is a statement followed by a proof, and Lean accepts the file only if every proof is
complete: no step is left to the reader. This file compiles with no errors and no `sorry` (the
keyword for a missing proof), so all its theorems are proved. The only axioms involved are the
three standard ones of Lean's logic (propositional extensionality, the axiom of choice, and
soundness of quotients), as the command `#print axioms BEEP.Main.Setup.main_thm` shows.

**Types.** `x : X` means "`x` is an element of `X`". Types play the role of sets: `ℕ` (the
natural numbers, starting at `0`), `ℝ` (the reals), `F` (our field), `F × F` (pairs), `ι → F`
(functions from `ι` to `F`, that is, words of length `n`), `Fin k → F` (vectors of `F^k`).
Function application is written without brackets: `u₁ i` is `u₁(i)`, and `f a b` is `f(a, b)`.
`fun x => e` is the function `x ↦ e`.

**Statements are types as well.** `Prop` is the type of statements, and a proof of a statement
`P` is an element `h : P`. So the hypothesis `(hab : a ≠ b)` reads "`hab` is a proof that
`a ≠ b`". Logical symbols: `∧` (and), `∨` (or), `¬` (not), `→` (implies), `↔` (iff), `∀ x, P x`,
`∃ x, P x`, `∀ x ∈ S, P x`, `∃ x ∈ S, P x`, and `a ≠ b` for `¬ (a = b)`.
Working with proofs:
* from `h : P ∧ Q` we get `h.1 : P` and `h.2 : Q` (so `h.2.1` is the first part of `h.2`);
* from `h : P ↔ Q` we get `h.mp : P → Q` and `h.mpr : Q → P`;
* `⟨a, b⟩` is a proof of `P ∧ Q` made of `a : P` and `b : Q`, or a proof of `∃ x, P x` made of
  a witness `a` and a proof `b : P a`;
* `¬ P` is by definition `P → False`: a proof of `¬ P` turns a proof of `P` into a
  contradiction;
* `h.trans h'` chains `h : a ≤ b` and `h' : b ≤ c` into `a ≤ c` (also for `=`), and
  `h.symm : b = a` flips `h : a = b`;
* `rfl` proves `a = a`, and more generally `a = b` when both sides are equal by definition.

**Arguments.** In `def f {X : Type*} [Field X] (x : X) ...`:
* `(x : X)` is an explicit argument, written whenever `f` is used;
* `{X : Type*}` is an implicit argument, which Lean infers from the other arguments;
* `[Field X]` says that `X` carries a field structure; Lean finds it automatically.
`Type*` means "some type": read it as "some set". A `variable` line declares arguments once,
for all the definitions and theorems that follow it and use them. `(ε₁ := e)` passes an implicit
argument by name, when Lean cannot infer it.

**Structures.** A `structure` is a record with named fields. `Setup F ι Z` below has the fields
`ℓ`, `m`, `enc`, `enc_inj`, `a₁`, `d₁`, `a₂`, `d₂`, `det_ne` and `φ`, and for `R : Setup F ι Z`
they are written `R.ℓ`, `R.enc`, `R.φ`, ... Definitions in the namespace `Setup` are also written
with a dot: `R.fold u₁ u₂ α` is `Setup.fold R u₁ u₂ α`.

**Finite sets.** `Finset X` is the type of finite subsets of `X`.
* `univ` is the whole of a finite type `X`, and `Fintype.card X` is its number of elements;
* `U.filter P`, or `univ.filter fun x => P x`, is the set `{x ∈ U | P x}`;
* `U.card` is the number of elements of `U`; `∑ x ∈ U, f x` and `∑ x : X, f x` are sums;
* `U ∩ V`, `U ∪ V`, `U ⊆ V` as usual; `insert a U` is `{a} ∪ U`; `U.erase a` is `U` minus `{a}`;
  `U ×ˢ V` is the cartesian product; `Uᶜ` is the complement of `U` in `X`; `U.image f` is the
  set of the `f x` with `x ∈ U`; `U.biUnion T` is the union of the sets `T x` with `x ∈ U`;
* `F × F × F` means `F × (F × F)`, so the entries of a triple `t` are `t.1`, `t.2.1`, `t.2.2`.

**Linear algebra.** `α • v` is the scalar multiple of the vector `v` by `α ∈ F` (for `v ∈ F` it
is the product `α * v`). `α⁻¹` is the inverse in `F` (Lean sets `0⁻¹ = 0`). `V →ₗ[F] W` is the
type of `F`-linear maps from `V` to `W`; such a map `f` satisfies `f (v + w) = f v + f w`
(`map_add`), `f (v - w) = f v - f w` (`map_sub`) and `f (a • v) = a • f v` (`map_smul`). Vectors
of `F^k` are functions `Fin k → F`, added and scaled entry by entry (`Pi.add_apply`,
`Pi.smul_apply`).

**Numbers.** On `ℕ`, subtraction is truncated: `3 - 5 = 0`. `(n : ℝ)`, displayed `↑n`, is the
natural number `n` viewed as a real number. `⌈y⌉₊` is the least natural number `≥ y`, and `⌊y⌋₊`
is the largest natural number `≤ y` (for `y ≥ 0`).

**Tactic proofs.** After `:= by` comes a list of *tactics*. Lean keeps track of the current
*goal* (what remains to be proved) and of the hypotheses available. In the editor the goal is
displayed after the symbol `⊢`, which is also how tactics refer to it (`at h ⊢` means "in `h`
and in the goal"). Two tactics on one line are separated by `;`. The tactics used here:
* `intro x h`: to prove `∀ x, P x → Q x`, take an arbitrary `x` and assume `h : P x`; `rintro`
  does the same and also splits pairs, as in `rintro ⟨a, b⟩`;
* `exact e`: the term `e` proves the goal;
* `apply e`: the goal follows from `e`, whose hypotheses become the new goals;
* `refine e`: like `exact`, but `e` may contain holes `?_`, which become new goals;
* `have h : P := ...`: prove an auxiliary fact `P` and call it `h` (`have := ...` calls it
  `this`);
* `set x := e with hx`: introduce the abbreviation `x` for `e`, replace `e` by `x` everywhere,
  and record `hx : x = e`;
* `unfold f`: replace `f` by its definition;
* `constructor`: split a goal `P ∧ Q` (or `P ↔ Q`) into its two parts;
* `obtain ⟨a, b⟩ := h`: split `h : P ∧ Q` (or `h : ∃ x, P x`) into its two parts; a `-` in
  place of a name discards that part;
* `subst h`: with `h : x = e`, replace the variable `x` by `e` everywhere;
* `rcases h with h₁ | h₂`: argue by cases on `h : P ∨ Q`;
* `by_contra h`: argue by contradiction, with `h` the negation of the goal;
* `choose! S hS using h`: from `h : ∀ a ∈ A, ∃ S, P a S`, make a function `S` with
  `hS : ∀ a ∈ A, P a (S a)` (the axiom of choice);
* `·`: work on the first of the remaining goals (each `·` handles one goal);
* `rw [e₁, e₂]`: rewrite the goal with the equations (or equivalences) `e₁`, then `e₂`, from
  left to right (`← e` rewrites from right to left); `rw [...] at h` rewrites `h` instead.
  Afterwards `rw` closes the goal if it has become of the form `a = a`;
* `simp only [e₁, ...]`: simplify with exactly the listed facts; a definition in the list is
  unfolded;
* `calc`: a chain `a = b := proof`, `_ ≤ c := proof`, ..., in which `_` stands for the right-hand
  side of the previous line;
* `h ▸ e`: rewrite the statement of `e` with the equation `h`.
Tactics that finish a goal by themselves:
* `omega`: linear arithmetic over `ℕ` and `ℤ`, including truncated subtraction (it treats a
  product of two unknowns as one unknown);
* `linarith`: linear arithmetic over ordered fields such as `ℝ`; `nlinarith`: the same, after
  multiplying hypotheses together;
* `positivity`: goals of the form `0 ≤ e` or `0 < e`;
* `ring`: identities in commutative rings (here `F`, `ℕ` and `ℝ`);
* `linear_combination e`: an equation that is `e` (a combination of hypotheses) up to `ring`;
* `module`: identities in vector spaces, such as `a • (v + w) - a • w = a • v`; `abel`:
  identities in abelian groups, such as `v = w + (v - w)`;
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

**Plan.** `Setup` collects the data of Sections 2.2, 2.3 and 3.1, and the section `Defs` sets up
the objects of Section 3.1 (`fold`, `CA`, `SatisfiesMCA`, `MCABad`, `IsPretender`, `Consistent`,
`DeepBad`, `ListDecodable`, `IsErrorBound`). The section `Lemma37` proves Lemma 3.7
(`few_pretenders_on_line`). The section `TheU` has the vector `U` of Lemma 3.8 (`defect`) and the
lemma itself (`defect_eq_zero_iff`), and `evader_defect_eq_zero` is Lemma 3.9. The section
`Counting` follows the rest of the proof: the DEEP-MCA-bad elements (`hits`) and a chosen
pretender for each (`pt`); Lemma 3.10 (`card_collinear_le`, `card_goodTriples`,
`card_goodTriples_le`, `third_moment_bound`); the double count over the pretender points
(`card_pretPts`, `sum_card_consTriples`); the theorem for given answers (`main_thm_gen_nat`,
`main_thm_gen`); and the theorem with the maximal `A_z` (`maxHits`, `main_thm_nat`, `main_thm`,
`fold_challenge_le`). The last section, `WithDelta`, states the theorem with `δ`
(`main_thm_delta`, `main_thm_delta_real`, `main_thm_delta_floor`).
-/

-- `open Finset` lets us write `univ`, `card_le_card`, `mem_filter`, ... instead of `Finset.univ`,
-- `Finset.card_le_card`, `Finset.mem_filter`, ... (Mathlib's library on finite sets).
open Finset

-- Switch off a warning (a "linter") that complains when a theorem does not use every `variable` of
-- its section. It has no effect on the mathematics.
set_option linter.unusedSectionVars false

-- From here to the end of the file, definitions may use non-constructive ingredients (the axiom
-- of choice in `pt`, real numbers in `main_thm`), so Lean does not try to compile them into
-- executable code.
noncomputable section

-- All names defined below get the prefix `BEEP.Main.` (e.g. `BEEP.Main.Setup.main_thm`), so that
-- they cannot clash with names in Mathlib or in `BEEP/AffineMain.lean`. The namespace is closed by
-- `end BEEP.Main` at the end of the file.
namespace BEEP.Main

-- Classical logic: every statement `P` may be treated as decidable (true or false). Lean needs
-- this to form `U.filter P` and `if P then _ else _` when no algorithm deciding `P` is provided.
open Classical

-- Standing assumptions, added as arguments to every definition and theorem below that uses them.
-- `F` is a finite field: a type with a field structure (`Field F`) and finitely many elements
-- (`Fintype F`, which provides `univ : Finset F` and the number `Fintype.card F`, our `q`).
variable {F : Type*} [Field F] [Fintype F]
-- `ι` is the finite set of positions of a word, and `n = Fintype.card ι`.
variable {ι : Type*} [Fintype ι]
-- `Z` is the finite set that indexes the zero evader. The theorems that speak of a probability
-- over `z ∈ Z` also assume that `Z` is nonempty (`[Nonempty Z]`), as Definition 2.3 does.
variable {Z : Type*} [Fintype Z]

/-! ### The setting of Sections 2.2, 2.3 and 3.1 -/

/-- The data that the paper fixes in Sections 2.2, 2.3 and 3.1: the code (through its encoding
map), the weights of the fold, and the zero evader. -/
structure Setup (F : Type*) [Field F] (ι : Type*) (Z : Type*) where
  /-- the dimension `ℓ` of the code `C` -/
  ℓ : ℕ
  /-- the number `m` of entries of an output of the zero evader -/
  m : ℕ
  /-- the linear encoding map `Enc_C : F^ℓ → F^n`, whose image is the code `C` -/
  enc : (Fin ℓ → F) →ₗ[F] (ι → F)
  /-- the encoding map is injective -/
  enc_inj : Function.Injective enc
  /-- the constant term of the weight `λ₁(α) = a₁ + α d₁` -/
  a₁ : F
  /-- the coefficient of `α` in `λ₁(α) = a₁ + α d₁` -/
  d₁ : F
  /-- the constant term of the weight `λ₂(α) = a₂ + α d₂` -/
  a₂ : F
  /-- the coefficient of `α` in `λ₂(α) = a₂ + α d₂` -/
  d₂ : F
  /-- the assumption `a₁ d₂ ≠ a₂ d₁` of Section 3.1 -/
  det_ne : a₁ * d₂ ≠ a₂ * d₁
  /-- the zero evader: for every `z ∈ Z`, a linear map `φ_z : F^ℓ → F^m` -/
  φ : Z → (Fin ℓ → F) →ₗ[F] (Fin m → F)

namespace Setup

-- `R` is the data of the setting. Every definition and theorem below that mentions `R` takes it
-- as its first explicit argument, written with a dot: `R.fold`, `R.IsPretender`, ...
variable (R : Setup F ι Z)

/-- The weight `λ₁(α) = a₁ + α d₁`. -/
def lam₁ (α : F) : F := R.a₁ + α * R.d₁

/-- The weight `λ₂(α) = a₂ + α d₂`. -/
def lam₂ (α : F) : F := R.a₂ + α * R.d₂

/-- The fold `λ₁(α) · u₁ + λ₂(α) · u₂` of two words with the challenge `α`: the word whose `i`-th
entry is `λ₁(α) u₁(i) + λ₂(α) u₂(i)`. -/
def fold (u₁ u₂ : ι → F) (α : F) : ι → F :=
  fun i => R.lam₁ α * u₁ i + R.lam₂ α * u₂ i

/-! ### The MCA property, pretenders, consistency and DEEP-MCA-bad elements -/

section Defs

-- In this section `u₁ u₂` are the two words, and `s` is the agreement threshold (the paper's
-- `(1 - δ) n`). Round brackets make them explicit arguments.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- `(u₁, u₂)` has Correlated Agreement with `C` over `S`: there are codewords `c₁, c₂ ∈ C` such
that `u₁` agrees with `c₁` on `S` and `u₂` agrees with `c₂` on `S`. -/
-- (The codewords are given by their messages `c₁ c₂`, as everywhere in this file.)
def CA (S : Finset ι) : Prop :=
  ∃ c₁ c₂ : Fin R.ℓ → F, ∀ i ∈ S, u₁ i = R.enc c₁ i ∧ u₂ i = R.enc c₂ i

/-- `α` satisfies the MCA property with respect to `u₁, u₂`: for every set `S` of at least `s`
positions on which the fold `λ₁(α) u₁ + λ₂(α) u₂` agrees with `C` (that is, with some codeword of
`C`), the pair `(u₁, u₂)` has Correlated Agreement with `C` over `S`. -/
def SatisfiesMCA (α : F) : Prop :=
  ∀ S : Finset ι, s ≤ S.card →
    ((∃ c : Fin R.ℓ → F, ∀ i ∈ S, R.enc c i = R.fold u₁ u₂ α i) → R.CA u₁ u₂ S)

/-- **Definition 3.1.** `α` is MCA-bad: it does not satisfy the MCA property. -/
def MCABad (α : F) : Prop := ¬ R.SatisfiesMCA u₁ u₂ s α

/-- **Definition 3.2.** The codeword `c ∈ C` is an `α`-pretender: the fold
`λ₁(α) u₁ + λ₂(α) u₂` and `c` agree on a set `S` of size at least `s` such that `(u₁, u₂)` does
not have Correlated Agreement with `C` over `S`. -/
-- (The paper states the definition for an MCA-bad `α`. This is no restriction: an `α` with an
-- `α`-pretender is MCA-bad, see `mcaBad_iff_exists_pretender` below.)
def IsPretender (α : F) (c : Fin R.ℓ → F) : Prop :=
  ∃ S : Finset ι, s ≤ S.card ∧ (∀ i ∈ S, R.enc c i = R.fold u₁ u₂ α i) ∧ ¬ R.CA u₁ u₂ S

/-- **Definition 3.3.** `(α, c)` is consistent with `(z, b₁, b₂)`, where `b = (b₁, b₂)`:
`φ_z(c) = λ₁(α) · b₁ + λ₂(α) · b₂`. -/
def Consistent (z : Z) (b : (Fin R.m → F) × (Fin R.m → F)) (α : F) (c : Fin R.ℓ → F) : Prop :=
  R.φ z c = R.lam₁ α • b.1 + R.lam₂ α • b.2

/-- **Definition 3.3, second part.** `α` is a DEEP-MCA-bad element with respect to `z, b₁, b₂`
and `u₁, u₂`: `α` is MCA-bad and some `α`-pretender `c` is such that `(α, c)` is consistent with
`(z, b₁, b₂)`. -/
-- (The first condition follows from the second, by `mcaBad_iff_exists_pretender`; we keep both,
-- as the paper does.)
def DeepBad (z : Z) (b : (Fin R.m → F) × (Fin R.m → F)) (α : F) : Prop :=
  R.MCABad u₁ u₂ s α ∧ ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z b α c

/-- `C` is list decodable with list size `L` at agreement `s`: every word `w` agrees on at least
`s` positions with at most `L` codewords of `C` (counted through their messages, which is the
same since the encoding map is injective, see `card_filter_codewords`). -/
def ListDecodable (L : ℕ) : Prop :=
  ∀ w : ι → F, (univ.filter fun c : Fin R.ℓ → F =>
    s ≤ (univ.filter fun i => R.enc c i = w i).card).card ≤ L

/-- **Definition 2.3.** `ε` is an error bound of the zero evader: `ε ≥ 0`, and for every nonzero
`v ∈ F^ℓ`, `Pr_z[φ_z(v) = 0] ≤ ε`. The probability is the number of such `z` divided by `|Z|`. -/
-- (This definition does not mention `u₁ u₂ s`, so they are not among its arguments. The paper
-- takes `ε ∈ [0, 1]`; the bound `ε ≤ 1` is not needed.)
def IsErrorBound (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ v : Fin R.ℓ → F, v ≠ 0 →
    ((univ.filter fun z : Z => R.φ z v = 0).card : ℝ) / Fintype.card Z ≤ ε

/-- An element `α` is MCA-bad exactly when there exists an `α`-pretender. -/
theorem mcaBad_iff_exists_pretender (α : F) :
    R.MCABad u₁ u₂ s α ↔ ∃ c, R.IsPretender u₁ u₂ s α c := by
  -- Prove the two directions separately (`constructor` splits `↔` into `→` and `←`).
  constructor
  · -- `→`: let `α` be MCA-bad (`h`), and suppose that there is no `α`-pretender (`hno`).
    intro h
    by_contra hno
    -- We contradict `h` by showing that `α` satisfies the MCA property.
    apply h
    -- Let `S` have at least `s` positions (`hS`), and let the fold agree with `c` on `S` (`hc`).
    intro S hS hc
    obtain ⟨c, hc⟩ := hc
    -- If there were no CA over `S` (`hCA`), then `c` would be an `α`-pretender.
    by_contra hCA
    exact hno ⟨c, S, hS, hc, hCA⟩
  · -- `←`: let `c` be an `α`-pretender, with its set `S`, and let `α` satisfy MCA (`h`).
    intro hc h
    obtain ⟨c, S, hS, hc, hCA⟩ := hc
    -- The MCA property gives CA over `S`, which `hCA` excludes.
    exact hCA (h S hS ⟨c, hc⟩)

end Defs

/-! ### Lemma 3.7: a parameterized line contains few pretenders -/

section Lemma37

-- The two words and the agreement threshold, as in the section `Defs`.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- The step behind "linearly independent" in the proof of Lemma 3.7: for `α ≠ β`, the two
equations `λ₁(α) ε₁ + λ₂(α) ε₂ = 0` and `λ₁(β) ε₁ + λ₂(β) ε₂ = 0` give `ε₁ = ε₂ = 0`. In the
lemma, `(ε₁, ε₂) = (u₁(i) - c₁(i), u₂(i) - c₂(i))` at a position `i`. -/
theorem eq_zero_of_two_folds {α β ε₁ ε₂ : F} (hαβ : α ≠ β)
    (hα : R.lam₁ α * ε₁ + R.lam₂ α * ε₂ = 0) (hβ : R.lam₁ β * ε₁ + R.lam₂ β * ε₂ = 0) :
    ε₁ = 0 ∧ ε₂ = 0 := by
  -- The determinant of the 2×2 system is `(β - α)(a₁ d₂ - a₂ d₁)`, which is nonzero
  -- (`sub_ne_zero : a - b ≠ 0 ↔ a ≠ b`, and a product of nonzero factors is nonzero).
  have hk : (β - α) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hαβ)) (sub_ne_zero.mpr R.det_ne)
  -- Write the weights out: `hα : (a₁ + α d₁) ε₁ + (a₂ + α d₂) ε₂ = 0`, and `hβ` with `β`.
  simp only [lam₁, lam₂] at hα hβ
  constructor
  · -- Eliminating `ε₂` from the two equations: the determinant times `ε₁` is `0`, ...
    have h : (β - α) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) * ε₁ = 0 := by
      linear_combination (R.a₂ + β * R.d₂) * hα - (R.a₂ + α * R.d₂) * hβ
    -- ... so `ε₁ = 0` (`mul_eq_zero`: a product vanishes iff a factor does; `resolve_left`
    -- discards the first factor, which is nonzero).
    exact (mul_eq_zero.mp h).resolve_left hk
  · -- Eliminating `ε₁`: the determinant times `ε₂` is `0`, so `ε₂ = 0`.
    have h : (β - α) * (R.a₁ * R.d₂ - R.a₂ * R.d₁) * ε₂ = 0 := by
      linear_combination (R.a₁ + α * R.d₁) * hβ - (R.a₁ + β * R.d₁) * hα
    exact (mul_eq_zero.mp h).resolve_left hk

/-- The first sentence of the proof of Lemma 3.7: a parameterized line `θ(α) = c₁ + α c₂` can be
written with the weights, `θ(α) = λ₁(α) g₁ + λ₂(α) g₂` for all `α`, where `g₁, g₂` solve the
system `a₁ g₁ + a₂ g₂ = c₁`, `d₁ g₁ + d₂ g₂ = c₂`. -/
theorem exists_weights_form (c₁ c₂ : Fin R.ℓ → F) :
    ∃ g₁ g₂ : Fin R.ℓ → F, ∀ α : F, c₁ + α • c₂ = R.lam₁ α • g₁ + R.lam₂ α • g₂ := by
  -- The determinant `a₁ d₂ - a₂ d₁` of the system is nonzero.
  have hΔ : R.a₁ * R.d₂ - R.a₂ * R.d₁ ≠ 0 := sub_ne_zero.mpr R.det_ne
  -- The solution of the system (Cramer's rule): `g₁ = (d₂ c₁ - a₂ c₂)/Δ` and
  -- `g₂ = (a₁ c₂ - d₁ c₁)/Δ`, with `Δ = a₁ d₂ - a₂ d₁`.
  refine ⟨(R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ • (R.d₂ • c₁ - R.a₂ • c₂),
    (R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ • (R.a₁ • c₂ - R.d₁ • c₁), fun α => ?_⟩
  -- Expanding, the right-hand side is `(Δ⁻¹ Δ) • (c₁ + α c₂)` (an identity of vectors, in which
  -- `Δ⁻¹` is treated as an unknown scalar: `module`), ...
  have key : R.lam₁ α • ((R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ • (R.d₂ • c₁ - R.a₂ • c₂)) +
      R.lam₂ α • ((R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ • (R.a₁ • c₂ - R.d₁ • c₁)) =
      ((R.a₁ * R.d₂ - R.a₂ * R.d₁)⁻¹ * (R.a₁ * R.d₂ - R.a₂ * R.d₁)) • (c₁ + α • c₂) := by
    simp only [lam₁, lam₂]
    module
  -- ... and `Δ⁻¹ Δ = 1` (`inv_mul_cancel₀`, valid as `Δ ≠ 0`), `1 • v = v` (`one_smul`).
  rw [key, inv_mul_cancel₀ hΔ, one_smul]

/-- The set `A_θ^pret` of Lemma 3.7, for the parameterized line `θ(α) = c₁ + α c₂`: the elements
`α` such that `θ(α)` is an `α`-pretender. -/
-- (The paper also asks that `α` be MCA-bad, which follows: `mcaBad_iff_exists_pretender`.)
def lineHits (c₁ c₂ : Fin R.ℓ → F) : Finset F :=
  univ.filter fun α => R.IsPretender u₁ u₂ s α (c₁ + α • c₂)

/-- **Lemma 3.7.** A parameterized line contains at most `n - s + 1` pretenders: at most that many
elements `α` make `θ(α) = c₁ + α c₂` an `α`-pretender. -/
-- (In the paper, `δ n + 1`.)
theorem few_pretenders_on_line (c₁ c₂ : Fin R.ℓ → F) :
    (R.lineHits u₁ u₂ s c₁ c₂).card ≤ Fintype.card ι - s + 1 := by
  -- Idea (the paper's proof): write the line with the weights, `θ(α) = λ₁(α) g₁ + λ₂(α) g₂`, and
  -- let `D` be the set of positions where `(u₁, u₂)` differs from `(g₁, g₂)`. Each counted `α`
  -- has an agreement set `S α`, and the sets `T α = S α ∩ D` are nonempty, pairwise disjoint,
  -- and have at least `|D| - (n - s)` elements each. Counting inside `D` gives the bound.
  obtain ⟨g₁, g₂, hg⟩ := R.exists_weights_form c₁ c₂
  -- `A`: the elements counted in the statement (the goal becomes `#A ≤ n - s + 1`).
  set A := R.lineHits u₁ u₂ s c₁ c₂ with hA
  -- `D`: the positions `i` where `(u₁(i), u₂(i)) ≠ (g₁(i), g₂(i))`.
  set D : Finset ι := univ.filter fun i =>
    ¬ (u₁ i = R.enc g₁ i ∧ u₂ i = R.enc g₂ i) with hD
  -- For each `α ∈ A`, the definition of pretender gives a set `S` of size at least `s`, on which
  -- the line and the fold agree, and over which there is no CA.
  have hex : ∀ α ∈ A, ∃ S : Finset ι, s ≤ S.card ∧
      (∀ i ∈ S, R.enc (c₁ + α • c₂) i = R.fold u₁ u₂ α i) ∧ ¬ R.CA u₁ u₂ S := by
    intro α hα
    -- Unfold `α ∈ A`: membership in a filter (`mem_filter`); its second part is the pretender
    -- property, which is the statement to prove.
    rw [hA, lineHits, mem_filter] at hα
    exact hα.2
  -- Choose such a set `S α` for every `α ∈ A` (the paper's `S_α`).
  choose! S hS using hex
  -- `T α = S α ∩ D`, written as a filter.
  set T : F → Finset ι := fun α => (S α).filter fun i => i ∈ D with hT
  -- (1) `T α` is nonempty: otherwise `(g₁, g₂)` would give CA over `S α`.
  have hT1 : ∀ α ∈ A, 1 ≤ (T α).card := by
    intro α hα
    -- Suppose `|T α| < 1`, that is, `T α` is empty.
    by_contra hlt
    -- We contradict `¬ CA (S α)` by exhibiting CA with the codewords `g₁, g₂`: for `i ∈ S α`
    -- (`hi`) we must show that `(u₁, u₂)` agrees with `(g₁, g₂)` at `i`.
    apply (hS α hα).2.2
    refine ⟨g₁, g₂, fun i hi => ?_⟩
    -- If not (`hi'`), then `i ∈ D`, so `i ∈ T α` ...
    by_contra hi'
    have hiT : i ∈ T α := by
      simp only [hT, hD, mem_filter, mem_univ, true_and]
      exact ⟨hi, hi'⟩
    -- ... and `T α` has an element (`card_pos : 0 < #U ↔ U.Nonempty`), against `hlt`.
    have hpos : 0 < (T α).card := card_pos.mpr ⟨i, hiT⟩
    omega
  -- (2) `|T α| ≥ |D| - (n - s)`: the part of `S α` outside `D` has at most `n - |D|` elements.
  have hTd : ∀ α ∈ A, D.card - (Fintype.card ι - s) ≤ (T α).card := by
    intro α hα
    -- `s ≤ |S α|`, and `|S α| = |T α| + |S α \ D|` (`card_filter_add_card_filter_not`).
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
  -- (3) The sets `T α` are pairwise disjoint: two distinct elements of `A` share no position of
  -- `D`. (`(A : Set F)` views the finite set `A` as a set, and `PairwiseDisjoint T` says that
  -- `T α` and `T β` are disjoint whenever `α ≠ β` are in `A`.)
  have hdisj : (A : Set F).PairwiseDisjoint T := by
    -- Let `α, β ∈ A` with `hαβ : α ≠ β`.
    intro α hα β hβ hαβ
    -- Unfold the goal to `Disjoint (T α) (T β)` (`Function.onFun`), and then to
    -- `∀ i ∈ T α, i ∉ T β` (`disjoint_left`). Let `i ∈ T α` (`hiα`) and `i ∈ T β` (`hiβ`).
    rw [Function.onFun, disjoint_left]
    intro i hiα hiβ
    -- `i ∈ S α`, `i ∈ S β` and `i ∈ D`.
    simp only [hT, mem_filter] at hiα hiβ
    have hiD := hiα.2
    simp only [hD, mem_filter, mem_univ, true_and] at hiD
    -- `hiD : ¬ (u₁ i = g₁(i) ∧ u₂ i = g₂(i))`. Applying it, it suffices to prove that
    -- `(u₁, u₂)` agrees with `(g₁, g₂)` at `i`.
    apply hiD
    -- The agreement of the line with the fold at `i`, for `α` and for `β` (`mem_coe` turns
    -- membership in the set `(A : Set F)` back into membership in the finite set `A`), ...
    have eα := (hS α (mem_coe.mp hα)).2.1 i hiα.1
    have eβ := (hS β (mem_coe.mp hβ)).2.1 i hiβ.1
    -- ... with the line written with the weights (`hg`), and everything evaluated at `i`: the
    -- encoding map is linear (`map_add`, `map_smul`), and words are added and scaled entry by
    -- entry (`Pi.add_apply`, `Pi.smul_apply`). Now
    -- `eα : λ₁(α) g₁(i) + λ₂(α) g₂(i) = λ₁(α) u₁(i) + λ₂(α) u₂(i)`, and `eβ` with `β`.
    rw [hg α] at eα
    rw [hg β] at eβ
    simp only [fold, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at eα eβ
    -- These are the two equations of `eq_zero_of_two_folds` for
    -- `(ε₁, ε₂) = (u₁(i) - g₁(i), u₂(i) - g₂(i))`, after moving everything to one side.
    have h0 := R.eq_zero_of_two_folds (ε₁ := u₁ i - R.enc g₁ i) (ε₂ := u₂ i - R.enc g₂ i) hαβ
      (by linear_combination -eα) (by linear_combination -eβ)
    -- So `ε₁ = ε₂ = 0`, that is, `u₁(i) = g₁(i)` and `u₂(i) = g₂(i)` (`sub_eq_zero`).
    exact ⟨sub_eq_zero.mp h0.1, sub_eq_zero.mp h0.2⟩
  -- The sets `T α` fit disjointly into `D`: `∑_{α ∈ A} |T α| ≤ |D|`.
  have hsum : ∑ α ∈ A, (T α).card ≤ D.card := by
    -- For pairwise disjoint sets, `#(⋃_{α ∈ A} T α) = ∑_{α ∈ A} #(T α)` (`card_biUnion`). Read
    -- from right to left (`←`), this turns the goal into `#(⋃_{α ∈ A} T α) ≤ #D`.
    rw [← card_biUnion hdisj]
    -- The union lies in `D`, since each `T α = S α ∩ D` does (`biUnion_subset`).
    refine card_le_card (biUnion_subset.mpr fun α _ i hi => ?_)
    simp only [hT, mem_filter] at hi
    exact hi.2
  -- First consequence: `#A ≤ #D`, since each `T α` with `α ∈ A` has at least one element.
  have h1 : A.card ≤ D.card :=
    -- `#A = ∑_{α ∈ A} 1 ≤ ∑_{α ∈ A} #(T α) ≤ #D` (`sum_le_sum`: term by term).
    calc A.card = ∑ α ∈ A, 1 := card_eq_sum_ones A
      _ ≤ ∑ α ∈ A, (T α).card := sum_le_sum hT1
      _ ≤ D.card := hsum
  -- Second consequence: `#A · (#D - (n - s)) ≤ #D`, using (2).
  have h2 : A.card * (D.card - (Fintype.card ι - s)) ≤ D.card :=
    -- A constant sum is `#A • c` (`sum_const`), and `#A • c = #A * c` (`smul_eq_mul`).
    calc A.card * (D.card - (Fintype.card ι - s))
        = ∑ α ∈ A, (D.card - (Fintype.card ι - s)) := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ α ∈ A, (T α).card := sum_le_sum hTd
      _ ≤ D.card := hsum
  -- The final count, as in the paper: either `#D ≤ (n - s) + 1` or `#D > (n - s) + 1`.
  rcases le_or_gt D.card (Fintype.card ι - s + 1) with hd | hd
  · -- First case: `#A ≤ #D ≤ n - s + 1`.
    exact h1.trans hd
  · -- Second case: either `#A = 0` or `#A ≥ 1`.
    rcases Nat.eq_zero_or_pos A.card with hb | hb
    · -- If `#A = 0` there is nothing to prove.
      omega
    · -- If `#A ≥ 1`: put `k = #D - (n - s)`. Here `k ≥ 2`, and `k ≥ 1` is all we use.
      have he : 1 ≤ D.card - (Fintype.card ι - s) := by omega
      -- `(#A - 1)(k - 1) ≥ 0`, that is, `#A + k ≤ #A · k + 1`. `nlinarith` finds this by
      -- multiplying the hypotheses `1 ≤ #A` and `1 ≤ k`.
      have key : A.card + (D.card - (Fintype.card ι - s)) ≤
          A.card * (D.card - (Fintype.card ι - s)) + 1 := by nlinarith
      -- With `h2` (`#A · k ≤ #D`): `#A ≤ #D + 1 - k = (n - s) + 1`. Here `omega` treats the
      -- product `#A · k` as one unknown number.
      omega

end Lemma37

end Setup

/-! ### The vector `U` of Lemma 3.8 -/

section TheU

-- In this section `V` is any `F`-vector space: an abelian group (`AddCommGroup V`) with a scalar
-- multiplication by `F` (`Module F V`). Below it is `F^ℓ`, the space of messages, that is, of
-- codewords.
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The vector `U((α₁, v₁), (α₂, v₂), (α₃, v₃)) = (α₃ - α₁)(v₂ - v₁) - (α₂ - α₁)(v₃ - v₁)` of
Lemma 3.8. For codewords `v₁, v₂, v₃` it is a codeword. -/
def defect (α₁ : F) (v₁ : V) (α₂ : F) (v₂ : V) (α₃ : F) (v₃ : V) : V :=
  (α₃ - α₁) • (v₂ - v₁) - (α₂ - α₁) • (v₃ - v₁)

/-- The parameterized line through `(α₁, v₁)` and `(α₂, v₂)` contains `(α₁, v₁)`. -/
-- For `α₁ ≠ α₂`, the line through the two tuples is `θ(α) = c₁ + α c₂`, with
-- `c₂ = (α₂ - α₁)⁻¹ (v₂ - v₁)` and `c₁ = v₁ - α₁ c₂`, as in the proof of Lemma 3.10. At `α₁` it
-- passes through `v₁`.
theorem line_fst (α₁ α₂ : F) (v₁ v₂ : V) :
    v₁ = (v₁ - α₁ • ((α₂ - α₁)⁻¹ • (v₂ - v₁))) + α₁ • ((α₂ - α₁)⁻¹ • (v₂ - v₁)) :=
  -- `sub_add_cancel x y : x - y + y = x`, flipped by `.symm`.
  (sub_add_cancel _ _).symm

/-- The parameterized line through `(α₁, v₁)` and `(α₂, v₂)` contains `(α₂, v₂)`. -/
-- At `α₂` the same line passes through `v₂` (this needs `α₁ ≠ α₂`).
theorem line_snd {α₁ α₂ : F} (h12 : α₁ ≠ α₂) (v₁ v₂ : V) :
    v₂ = (v₁ - α₁ • ((α₂ - α₁)⁻¹ • (v₂ - v₁))) + α₂ • ((α₂ - α₁)⁻¹ • (v₂ - v₁)) := by
  -- `α₂ - α₁ ≠ 0` (`sub_ne_zero : x - y ≠ 0 ↔ x ≠ y`, and `Ne.symm h12 : α₂ ≠ α₁`).
  have h21 : α₂ - α₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  -- First `v₂ = v₁ + ((α₂ - α₁)(α₂ - α₁)⁻¹)(v₂ - v₁)`: rewrite `(α₂ - α₁)(α₂ - α₁)⁻¹ = 1`
  -- (`mul_inv_cancel₀`) and `1 • v = v` (`one_smul`); what is left, `v₂ = v₁ + (v₂ - v₁)`, holds
  -- in every abelian group (`abel`).
  calc v₂ = v₁ + ((α₂ - α₁) * (α₂ - α₁)⁻¹) • (v₂ - v₁) := by
        rw [mul_inv_cancel₀ h21, one_smul]; abel
    -- The last `_` is the right-hand side of the statement. Both sides agree after expanding
    -- (`module`), with `(α₂ - α₁)⁻¹` treated as an unknown scalar.
    _ = _ := by module

/-- **Lemma 3.8, one direction.** If `U = 0` and `α₁ ≠ α₂`, then `(α₃, v₃)` lies on the
parameterized line through `(α₁, v₁)` and `(α₂, v₂)`. -/
theorem onLine_of_defect_eq_zero {α₁ α₂ α₃ : F} {v₁ v₂ v₃ : V} (h12 : α₁ ≠ α₂)
    (h : defect α₁ v₁ α₂ v₂ α₃ v₃ = 0) :
    v₃ = (v₁ - α₁ • ((α₂ - α₁)⁻¹ • (v₂ - v₁))) + α₃ • ((α₂ - α₁)⁻¹ • (v₂ - v₁)) := by
  have h21 : α₂ - α₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  -- `U` is `x - y` with `x = (α₃ - α₁)(v₂ - v₁)` and `y = (α₂ - α₁)(v₃ - v₁)`, and
  -- `x - y = 0 ↔ x = y` (`sub_eq_zero`).
  have h' : (α₃ - α₁) • (v₂ - v₁) = (α₂ - α₁) • (v₃ - v₁) := sub_eq_zero.mp h
  -- Divide by `α₂ - α₁`: rewrite `(α₃ - α₁)(v₂ - v₁)` as `(α₂ - α₁)(v₃ - v₁)` (`h'`), and then
  -- `(α₂ - α₁)⁻¹ ((α₂ - α₁) v) = ((α₂ - α₁)⁻¹ (α₂ - α₁)) v = 1 v = v` (`smul_smul`,
  -- `inv_mul_cancel₀`, `one_smul`).
  have h'' : v₃ - v₁ = (α₂ - α₁)⁻¹ • ((α₃ - α₁) • (v₂ - v₁)) := by
    rw [h', smul_smul, inv_mul_cancel₀ h21, one_smul]
  -- `v₃ = v₁ + (v₃ - v₁) = v₁ + (α₂ - α₁)⁻¹ (α₃ - α₁)(v₂ - v₁)`, which is the right-hand side
  -- after expanding (`module`).
  calc v₃ = v₁ + (v₃ - v₁) := by abel
    _ = v₁ + (α₂ - α₁)⁻¹ • ((α₃ - α₁) • (v₂ - v₁)) := by rw [h'']
    _ = _ := by module

/-- **Lemma 3.8, other direction.** Three tuples on one parameterized line `θ(α) = c₁ + α c₂`
have `U = 0`. -/
theorem defect_eq_zero_of_onLine {c₁ c₂ : V} {α₁ α₂ α₃ : F} {v₁ v₂ v₃ : V}
    (h₁ : v₁ = c₁ + α₁ • c₂) (h₂ : v₂ = c₁ + α₂ • c₂) (h₃ : v₃ = c₁ + α₃ • c₂) :
    defect α₁ v₁ α₂ v₂ α₃ v₃ = 0 := by
  -- Replace `v₁, v₂, v₃` by their values on the line.
  subst h₁ h₂ h₃
  -- `U = (α₃ - α₁)(α₂ - α₁) c₂ - (α₂ - α₁)(α₃ - α₁) c₂ = 0`.
  simp only [defect]
  module

/-- **Lemma 3.8.** For `α₁ ≠ α₂`, the three tuples `(α_i, v_i)` belong to the same parameterized
line `θ(α) = c₁ + α c₂` if and only if `U((α_i, v_i)) = 0`. -/
-- (The paper assumes `α₁, α₂, α₃` pairwise distinct; only `α₁ ≠ α₂` is needed.)
theorem defect_eq_zero_iff {α₁ α₂ α₃ : F} {v₁ v₂ v₃ : V} (h12 : α₁ ≠ α₂) :
    defect α₁ v₁ α₂ v₂ α₃ v₃ = 0 ↔
      ∃ c₁ c₂ : V, v₁ = c₁ + α₁ • c₂ ∧ v₂ = c₁ + α₂ • c₂ ∧ v₃ = c₁ + α₃ • c₂ := by
  constructor
  · -- `→`: the line through the first two tuples (`line_fst`, `line_snd`) contains the third
    -- (`onLine_of_defect_eq_zero`). The two `_` are its `c₁` and `c₂`, which Lean infers.
    intro h
    exact ⟨_, _, line_fst α₁ α₂ v₁ v₂, line_snd h12 v₁ v₂, onLine_of_defect_eq_zero h12 h⟩
  · -- `←`: `defect_eq_zero_of_onLine`.
    intro h
    obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := h
    exact defect_eq_zero_of_onLine h₁ h₂ h₃

end TheU

namespace Setup

variable (R : Setup F ι Z)

/-- **Lemma 3.9.** If three tuples `(α_i, v_i)` are consistent with the same `(z, b₁, b₂)`, then
`φ_z(U((α_i, v_i))) = 0`. -/
theorem evader_defect_eq_zero {z : Z} {b : (Fin R.m → F) × (Fin R.m → F)} {α₁ α₂ α₃ : F}
    {v₁ v₂ v₃ : Fin R.ℓ → F} (h₁ : R.Consistent z b α₁ v₁) (h₂ : R.Consistent z b α₂ v₂)
    (h₃ : R.Consistent z b α₃ v₃) : R.φ z (defect α₁ v₁ α₂ v₂ α₃ v₃) = 0 := by
  -- The three consistency equations: `φ_z(v_i) = λ₁(α_i) b₁ + λ₂(α_i) b₂`.
  unfold Consistent at h₁ h₂ h₃
  -- `φ_z` is linear (`map_sub`, `map_smul`): this is the property of the zero evader that the
  -- paper uses. Substitute the three values `φ_z(v_i)` and write the weights out.
  simp only [defect, map_sub, map_smul, h₁, h₂, h₃, lam₁, lam₂]
  -- What remains is an identity of vectors: the coefficients of `b₁` and of `b₂` cancel.
  module

/-! ### The proof of Theorem 3.4 -/

section Counting

-- The words, the threshold, and the prover's answers `B`: for every `z ∈ Z` a pair
-- `B z = (b₁, b₂)` of vectors of `F^m`. The answers may depend on `z` in any way. Theorem 3.4
-- takes the answers that maximize the number of DEEP-MCA-bad elements (`maxHits` below).
variable (u₁ u₂ : ι → F) (s : ℕ) (B : Z → (Fin R.m → F) × (Fin R.m → F))

/-- The set `A_{z, b₁, b₂}` of DEEP-MCA-bad elements at `z`, with the answers `(b₁, b₂) = B z`. -/
def hits (z : Z) : Finset F :=
  univ.filter fun α => R.DeepBad u₁ u₂ s z (B z) α

/-- A chosen consistent pretender at the element `α` (junk if there is none): the paper's `c_α`
in the proof of Lemma 3.10. -/
def pt (z : Z) (α : F) : Fin R.ℓ → F :=
  -- `if h : P then x else y` is `x` if `P` holds and `y` otherwise; in the first branch `h` is a
  -- proof of `P`. From `h : ∃ c, ...` the axiom of choice gives a witness, `h.choose`.
  if h : ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z (B z) α c then h.choose else 0

/-- At a DEEP-MCA-bad element, the chosen point is a consistent pretender. -/
theorem pt_spec {z : Z} {α : F} (hα : α ∈ R.hits u₁ u₂ s B z) :
    R.IsPretender u₁ u₂ s α (R.pt u₁ u₂ s B z α) ∧
      R.Consistent z (B z) α (R.pt u₁ u₂ s B z α) := by
  -- `α ∈ hits` unfolds to `DeepBad`, whose second part is the `∃ c, ...` that we need.
  have h : ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z (B z) α c := (mem_filter.mp hα).2.2
  -- Unfold `pt` and take the first branch of the `if` (`dif_pos h`): the point is `h.choose`.
  rw [pt, dif_pos h]
  -- `h.choose_spec` says that `h.choose` has the property required in `h`.
  exact h.choose_spec

/-- **Lemma 3.10, the part that uses Lemma 3.7.** For two DEEP-MCA-bad elements `a ≠ b`, at most
`(n - s + 1) - 2` further ones have their chosen point on the parameterized line through the
chosen points at `a` and `b` (that is, `U = 0`). -/
theorem card_collinear_le {z : Z} {a b : F} (ha : a ∈ R.hits u₁ u₂ s B z)
    (hb : b ∈ R.hits u₁ u₂ s B z) (hab : a ≠ b) :
    ((((R.hits u₁ u₂ s B z).erase a).erase b).filter fun c =>
        defect a (R.pt u₁ u₂ s B z a) b (R.pt u₁ u₂ s B z b) c (R.pt u₁ u₂ s B z c) = 0).card +
        2 ≤
      Fintype.card ι - s + 1 := by
  -- Idea: `a`, `b` and these elements are counted by Lemma 3.7 for the line through the chosen
  -- points at `a` and `b`. Abbreviations: `p` for the choice of points, `Col` for the set counted.
  set p := R.pt u₁ u₂ s B z with hp
  set Col := (((R.hits u₁ u₂ s B z).erase a).erase b).filter fun c =>
    defect a (p a) b (p b) c (p c) = 0 with hCol
  -- The chosen points at `a` and `b` are consistent pretenders.
  have hpa := R.pt_spec u₁ u₂ s B ha
  have hpb := R.pt_spec u₁ u₂ s B hb
  -- The main step: `{a} ∪ {b} ∪ Col` lies in `A_θ^pret` (`lineHits`) for the line `θ` through
  -- `(a, p a)` and `(b, p b)`: `θ(α) = c₁ + α c₂` with `c₂ = (b - a)⁻¹ (p b - p a)` and
  -- `c₁ = p a - a c₂`.
  have hsub : insert a (insert b Col) ⊆ R.lineHits u₁ u₂ s
      (p a - a • ((b - a)⁻¹ • (p b - p a))) ((b - a)⁻¹ • (p b - p a)) := by
    -- Let `α` be in `{a} ∪ {b} ∪ Col`; we show that `θ(α)` is an `α`-pretender.
    intro α hα
    simp only [lineHits, mem_filter, mem_univ, true_and]
    rcases mem_insert.mp hα with h | hα
    · -- `α = a`: `θ(a) = p a` (`line_fst`, read from right to left), which is an `a`-pretender.
      rw [h, ← line_fst a b (p a) (p b)]
      exact hpa.1
    rcases mem_insert.mp hα with h | hα
    · -- `α = b`: `θ(b) = p b` (`line_snd`), which is a `b`-pretender.
      rw [h, ← line_snd hab (p a) (p b)]
      exact hpb.1
    · -- `α ∈ Col`: `α` is DEEP-MCA-bad, and `U = 0` gives `θ(α) = p α`
      -- (`onLine_of_defect_eq_zero`), which is an `α`-pretender.
      rw [hCol, mem_filter] at hα
      have hαH : α ∈ R.hits u₁ u₂ s B z := mem_of_mem_erase (mem_of_mem_erase hα.1)
      rw [← onLine_of_defect_eq_zero hab hα.2]
      exact (R.pt_spec u₁ u₂ s B hαH).1
  -- `b ∉ Col` and `a ∉ {b} ∪ Col`, since `Col ⊆ (H \ {a}) \ {b}` (`notMem_erase`).
  have hbC : b ∉ Col := fun h => by
    rw [hCol, mem_filter] at h
    exact (notMem_erase b _) h.1
  have haC : a ∉ insert b Col := by
    rw [mem_insert, not_or]
    refine ⟨hab, fun h => ?_⟩
    rw [hCol, mem_filter] at h
    exact (notMem_erase a _) (mem_of_mem_erase h.1)
  -- `#({a} ∪ {b} ∪ Col) ≤ #A_θ^pret ≤ n - s + 1`, by Lemma 3.7 (`few_pretenders_on_line`).
  have := (card_le_card hsub).trans (R.few_pretenders_on_line u₁ u₂ s _ _)
  -- As `a` and `b` are new elements, `#({a} ∪ {b} ∪ Col) = #Col + 1 + 1`.
  rw [card_insert_of_notMem haC, card_insert_of_notMem hbC] at this
  omega

/-- Ordered triples of distinct DEEP-MCA-bad elements whose chosen points have `U ≠ 0`. -/
def goodTriples (z : Z) : Finset (F × F × F) :=
  (R.hits u₁ u₂ s B z ×ˢ R.hits u₁ u₂ s B z ×ˢ R.hits u₁ u₂ s B z).filter fun t =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      defect t.1 (R.pt u₁ u₂ s B z t.1) t.2.1 (R.pt u₁ u₂ s B z t.2.1) t.2.2
        (R.pt u₁ u₂ s B z t.2.2) ≠ 0

/-- **Lemma 3.10, the count.** With `h = |A_{z,b₁,b₂}|` DEEP-MCA-bad elements there are at least
`h (h - 1) (h - N)` ordered triples of distinct ones whose chosen points have `U ≠ 0`, where
`N = n - s + 1`. -/
-- (For a pair `a ≠ b`, the line through the chosen points at `a` and `b` contains these two
-- points and at most `N - 2` others, by `card_collinear_le`. So among the `h - 2` elements other
-- than `a` and `b`, at least `(h - 2) - (N - 2) = h - N` are off the line: the count of the paper
-- needs no correction for the two points on the line.)
theorem card_goodTriples (z : Z) :
    (R.hits u₁ u₂ s B z).card * ((R.hits u₁ u₂ s B z).card - 1) *
        ((R.hits u₁ u₂ s B z).card - (Fintype.card ι - s + 1)) ≤
      (R.goodTriples u₁ u₂ s B z).card := by
  -- The abbreviations `H`, `p`, `N` and `h`.
  set H := R.hits u₁ u₂ s B z with hH
  set p := R.pt u₁ u₂ s B z with hp
  set N := Fintype.card ι - s + 1 with hN
  set h := H.card with hh
  -- for a fixed ordered pair `a ≠ b`, at least `h - N` third elements give a good triple
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

/-- The set `P` of the proof of Theorem 3.4: the pairs `(α, c)` with `c` an `α`-pretender. -/
def pretPts : Finset (F × (Fin R.ℓ → F)) :=
  univ.filter fun p => R.IsPretender u₁ u₂ s p.1 p.2

/-- `|P| ≤ q L`: for each of the `q` elements `α`, the `α`-pretenders are codewords that agree
with the fold `λ₁(α) u₁ + λ₂(α) u₂` on at least `s` positions, and there are at most `L` of
them. -/
theorem card_pretPts (L : ℕ) (hL : R.ListDecodable s L) :
    (R.pretPts u₁ u₂ s).card ≤ Fintype.card F * L := by
  -- Sort the points by their element `α = p.1` (`card_eq_sum_card_fiberwise`).
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ α ∈ (univ : Finset F), ((R.pretPts u₁ u₂ s).filter fun p => p.1 = α).card
      ≤ ∑ α ∈ (univ : Finset F), L := by
        -- Term by term: `p ↦ p.2` sends the fiber over `α` injectively into the set of codewords
        -- that agree with the fold on at least `s` positions, which has at most `L` elements
        -- (`hL` for the word `fold u₁ u₂ α`).
        refine sum_le_sum fun α _ =>
          (card_le_card_of_injOn Prod.snd ?_ ?_).trans (hL (R.fold u₁ u₂ α))
        · -- It lands in that set: a pretender at `α` agrees with the fold on its set `S`, of
          -- size at least `s`, so on at least `s` positions.
          intro p hp
          simp only [pretPts, coe_filter, mem_filter, mem_univ, true_and,
            Set.mem_setOf_eq] at hp ⊢
          obtain ⟨⟨S, hS, hagree, -⟩, hα⟩ := hp
          refine hS.trans (card_le_card fun i hi => ?_)
          rw [mem_filter]
          exact ⟨mem_univ _, hα ▸ hagree i hi⟩
        · -- It is injective: `p.2 = p'.2` and `p.1 = α = p'.1` give `p = p'`.
          intro p hp p' hp' h
          simp only [pretPts, coe_filter, mem_filter, mem_univ, true_and,
            Set.mem_setOf_eq] at hp hp'
          exact Prod.ext (hp.2.trans hp'.2.symm) h
    -- `∑_{α ∈ F} L = q L`.
    _ = Fintype.card F * L := by rw [sum_const, card_univ, smul_eq_mul]

/-- Ordered triples of pretender points with distinct elements `α_i` and `U ≠ 0`. -/
def triples : Finset ((F × (Fin R.ℓ → F)) × (F × (Fin R.ℓ → F)) × (F × (Fin R.ℓ → F))) :=
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

/-- The set `T_z` of the paper: the triples of `triples` whose three points are consistent with
`(z, B z)`. -/
-- (The four conditions of the paper: 1. consistency, here; 2. `U ≠ 0`, 3. the points are
-- pretenders and 4. the `α_i` are distinct, in `triples`.)
def consTriples (z : Z) :
    Finset ((F × (Fin R.ℓ → F)) × (F × (Fin R.ℓ → F)) × (F × (Fin R.ℓ → F))) :=
  (R.triples u₁ u₂ s).filter fun t => R.Consistent z (B z) t.1.1 t.1.2 ∧
    R.Consistent z (B z) t.2.1.1 t.2.1.2 ∧ R.Consistent z (B z) t.2.2.1 t.2.2.2

/-- **The double count of the proof of Theorem 3.4.** Let every nonzero `v ∈ F^ℓ` have
`φ_z(v) = 0` for at most `M` of the `z ∈ Z`. A triple with `U ≠ 0` belongs to `T_z` for at most
`M` of the `z`, since `φ_z(U) = 0` for each of them (Lemma 3.9). Hence
`∑_z |T_z| ≤ #triples · M`. -/
theorem sum_card_consTriples (M : ℕ)
    (hM : ∀ v : Fin R.ℓ → F, v ≠ 0 → (univ.filter fun z : Z => R.φ z v = 0).card ≤ M) :
    ∑ z : Z, (R.consTriples u₁ u₂ s B z).card ≤ (R.triples u₁ u₂ s).card * M := by
  -- Write `#consTriples(z)` as `∑_{t ∈ triples} [t is consistent with z]` (`card_filter`), and
  -- exchange the two sums (`sum_comm`).
  simp only [consTriples, card_filter]
  rw [sum_comm]
  calc ∑ t ∈ R.triples u₁ u₂ s, ∑ z : Z,
        (if R.Consistent z (B z) t.1.1 t.1.2 ∧ R.Consistent z (B z) t.2.1.1 t.2.1.2 ∧
          R.Consistent z (B z) t.2.2.1 t.2.2.2 then 1 else 0)
      ≤ ∑ t ∈ R.triples u₁ u₂ s, M := by
        -- Term by term: fix a triple `t ∈ triples` (`ht`).
        refine sum_le_sum fun t ht => ?_
        -- Back from indicators to a size: the goal is `#{z | t is consistent with z} ≤ M`.
        rw [← card_filter]
        -- Unfold `t ∈ triples`: we only need `U ≠ 0` (`hdef`).
        simp only [triples, mem_filter] at ht
        obtain ⟨-, -, -, -, hdef⟩ := ht
        -- Every `z` that `t` is consistent with has `φ_z(U) = 0` (`evader_defect_eq_zero`), and
        -- there are at most `M` such `z` since `U ≠ 0` (`hM`).
        refine (card_le_card fun z hz => ?_).trans (hM _ hdef)
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        exact R.evader_defect_eq_zero hz.1 hz.2.1 hz.2.2
    -- `∑_{t ∈ triples} M = #triples · M`.
    _ = (R.triples u₁ u₂ s).card * M := by rw [sum_const, smul_eq_mul]

/-- The good triples of a fixed `z` inject into `T_z`: `(a, b, c) ↦ ((a, c_a), (b, c_b), (c, c_c))`
with the chosen points. -/
theorem card_goodTriples_le (z : Z) :
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
    -- ... and supply it: the points are pretenders, the elements are distinct, `U ≠ 0`, and the
    -- points are consistent.
    exact ⟨⟨⟨s₁.1, s₂.1, s₃.1⟩, hne₁, hne₂, hne₃, hdef⟩, s₁.2, s₂.2, s₃.2⟩
  · -- It is injective: equal images have equal elements (`Prod.mk.injEq`).
    intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.2.1.1 h.2.2.1)

/-- **Lemma 3.10.** `|A| (|A| - 1) (|A| - (n - s) - 1) ≤ |T_z|`, where `A = A_{z,b₁,b₂}` is the
set of DEEP-MCA-bad elements at `z` for the answers `(b₁, b₂) = B z`. -/
-- (In the paper, `|A_z| (|A_z| - 1) (|A_z| - δ n - 1) ≤ |T_z|`. The subtractions are those of
-- `ℕ`: for `|A| ≤ n - s + 1` the left-hand side is `0`.)
theorem third_moment_bound (z : Z) :
    (R.hits u₁ u₂ s B z).card * ((R.hits u₁ u₂ s B z).card - 1) *
        ((R.hits u₁ u₂ s B z).card - (Fintype.card ι - s + 1)) ≤
      (R.consTriples u₁ u₂ s B z).card :=
  -- The count of good triples, and their injection into `T_z`.
  (R.card_goodTriples u₁ u₂ s B z).trans (R.card_goodTriples_le u₁ u₂ s B z)

/-! #### Theorem 3.4 for given answers -/

/-- The function `f(h) = h (h - 1) (h - N)` is monotone (as in `BEEP/AffineMain.lean`). -/
theorem cubic_mono {t h N : ℕ} (hth : t ≤ h) : t * (t - 1) * (t - N) ≤ h * (h - 1) * (h - N) :=
  -- Multiply the three inequalities `t ≤ h`, `t - 1 ≤ h - 1` and `t - N ≤ h - N`.
  Nat.mul_le_mul (Nat.mul_le_mul hth (Nat.sub_le_sub_right hth 1)) (Nat.sub_le_sub_right hth N)

/-- **Theorem 3.4 for given answers, counting form.** Let `N = n - s + 1`. If `C` is list
decodable with list size `L` at agreement `s`, and every nonzero `v ∈ F^ℓ` has `φ_z(v) = 0` for at
most `M` of the `z ∈ Z`, then for every `t` and every choice of answers `B`, the number `K` of
`z ∈ Z` with at least `t` DEEP-MCA-bad elements satisfies `t (t - 1) (t - N) K ≤ (q L)³ M`. For
`t ≤ N` the left-hand side is `0`. -/
theorem main_thm_gen_nat (L M t : ℕ) (hL : R.ListDecodable s L)
    (hM : ∀ v : Fin R.ℓ → F, v ≠ 0 → (univ.filter fun z : Z => R.φ z v = 0).card ≤ M) :
    t * (t - 1) * (t - (Fintype.card ι - s + 1)) *
        (univ.filter fun z : Z => t ≤ (R.hits u₁ u₂ s B z).card).card ≤
      (Fintype.card F * L) ^ 3 * M := by
  -- The proof of Theorem 3.4: a `z` with at least `t` DEEP-MCA-bad elements has
  -- `|T_z| ≥ f(t)`, and `∑_z |T_z| ≤ (q L)³ M`. Abbreviations `N` and `Zt` (the `z` with at
  -- least `t` DEEP-MCA-bad elements; the paper's `Z_t`).
  set N := Fintype.card ι - s + 1 with hN
  set Zt := (univ : Finset Z).filter fun z => t ≤ (R.hits u₁ u₂ s B z).card with hZt
  -- For `z ∈ Zt`: `f(t) ≤ |T_z|`.
  have hz : ∀ z ∈ Zt, t * (t - 1) * (t - N) ≤ (R.consTriples u₁ u₂ s B z).card := by
    intro z hz
    simp only [hZt, mem_filter, mem_univ, true_and] at hz
    -- `f(t) ≤ f(|A_z|)` (`cubic_mono`) `≤ |T_z|` (Lemma 3.10).
    calc t * (t - 1) * (t - N)
        ≤ (R.hits u₁ u₂ s B z).card * ((R.hits u₁ u₂ s B z).card - 1) *
            ((R.hits u₁ u₂ s B z).card - N) := cubic_mono hz
      _ ≤ (R.consTriples u₁ u₂ s B z).card := R.third_moment_bound u₁ u₂ s B z
  -- Sum over `Zt` and bound the total by the double count.
  calc t * (t - 1) * (t - N) * Zt.card = ∑ z ∈ Zt, t * (t - 1) * (t - N) := by
        rw [sum_const, smul_eq_mul]; ring
    _ ≤ ∑ z ∈ Zt, (R.consTriples u₁ u₂ s B z).card := sum_le_sum hz
    -- sum over all `z ∈ Z` instead of `Zt`
    _ ≤ ∑ z : Z, (R.consTriples u₁ u₂ s B z).card :=
        sum_le_sum_of_subset (filter_subset _ _)
    -- the double count (`sum_card_consTriples`)
    _ ≤ (R.triples u₁ u₂ s).card * M := R.sum_card_consTriples u₁ u₂ s B M hM
    -- `#triples ≤ |P|³ ≤ (q L)³` (`card_triples_le`, `card_pretPts`)
    _ ≤ (Fintype.card F * L) ^ 3 * M :=
        Nat.mul_le_mul_right _ ((R.card_triples_le u₁ u₂ s).trans
          (Nat.pow_le_pow_left (R.card_pretPts u₁ u₂ s L hL) 3))

/-- **Theorem 3.4 for given answers.** Let `ε` be an error bound of the zero evader. For every
integer `t ≥ n - s + 2` and every choice of answers `B`, for `z` uniform in `Z`,
`Pr[z has at least t DEEP-MCA-bad elements] ≤ (q L)³ ε / (t (t - 1) (t - (n - s) - 1))`. The
probability is written as the number of such `z` divided by `|Z|`, and the denominator
`t (t - 1) (t - N)`, with `N = n - s + 1`, is computed in `ℝ` (it is positive). -/
theorem main_thm_gen [Nonempty Z] (L t : ℕ) (ε : ℝ) (hL : R.ListDecodable s L)
    (hε : R.IsErrorBound ε) (ht : Fintype.card ι - s + 2 ≤ t) :
    ((univ.filter fun z : Z => t ≤ (R.hits u₁ u₂ s B z).card).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - ((Fintype.card ι - s + 1 : ℕ) : ℝ))) := by
  -- `|Z| > 0`, since `Z` is nonempty.
  have hZ : (0 : ℝ) < Fintype.card Z := Nat.cast_pos.mpr Fintype.card_pos
  -- `M = ⌊ε |Z|⌋`: the natural number that the error bound gives. `M ≤ ε |Z|`, since
  -- `ε |Z| ≥ 0` (`Nat.floor_le`).
  set M := ⌊ε * Fintype.card Z⌋₊ with hM
  have hMle : (M : ℝ) ≤ ε * Fintype.card Z := Nat.floor_le (mul_nonneg hε.1 hZ.le)
  -- Every nonzero `v` has `φ_z(v) = 0` for at most `M` of the `z`: their number is at most
  -- `ε |Z|` by the error bound (`div_le_iff₀ : a / c ≤ b ↔ a ≤ b c` for `c > 0`), and a natural
  -- number that is at most `y` is at most `⌊y⌋` (`Nat.le_floor`).
  have hMb : ∀ v : Fin R.ℓ → F, v ≠ 0 → (univ.filter fun z : Z => R.φ z v = 0).card ≤ M := by
    intro v hv
    have hv' := hε.2 v hv
    rw [div_le_iff₀ hZ] at hv'
    exact Nat.le_floor hv'
  -- The counting form: `h : f(t) K ≤ (q L)³ M` in `ℕ`.
  have h := R.main_thm_gen_nat u₁ u₂ s B L M t hL hMb
  -- `N`, and `K`: the number of `z` with at least `t` DEEP-MCA-bad elements.
  set N := Fintype.card ι - s + 1 with hN
  set K : ℕ := (univ.filter fun z : Z => t ≤ (R.hits u₁ u₂ s B z).card).card with hK
  -- `t ≥ N + 1 ≥ 2`, so no subtraction in `f(t)` is truncated. This is the only place where the
  -- hypothesis `t ≥ n - s + 2` is used: it makes `t (t - 1) (t - N)` positive, so that we can
  -- divide by it.
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
      ((Fintype.card F : ℝ) * L) ^ 3 * M := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub h1t, Nat.cast_sub hNt] at this
    exact this
  -- `div_le_div_iff₀ : a / b ≤ c / d ↔ a d ≤ c b` for `b, d > 0`.
  rw [div_le_div_iff₀ hZ hD]
  -- Reorder (`ring`), apply `h'`, and use `M ≤ ε |Z|` (`gcongr`).
  calc (K : ℝ) * ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N))
      = (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - N) * K := by ring
    _ ≤ ((Fintype.card F : ℝ) * L) ^ 3 * M := h'
    _ ≤ ((Fintype.card F : ℝ) * L) ^ 3 * (ε * Fintype.card Z) := by gcongr
    _ = ((Fintype.card F : ℝ) * L) ^ 3 * ε * Fintype.card Z := by ring

/-! #### Theorem 3.4, with the answers that maximize `|A_{z,b₁,b₂}|` -/

/-- `|A_z|`: the largest number of DEEP-MCA-bad elements at `z` over all answers `(b₁, b₂)`. -/
-- `fun _ => b` is the strategy that answers `b` to every `z`, and `univ.sup f` is the largest value
-- of `f b` over all `b` (Mathlib's `Finset.sup`).
def maxHits (z : Z) : ℕ :=
  univ.sup fun b : (Fin R.m → F) × (Fin R.m → F) => (R.hits u₁ u₂ s (fun _ => b) z).card

-- The DEEP-MCA-bad elements of `z` only depend on the answers `B z` to `z`, so
-- `|A_{z, B z}| ≤ |A_z|` for every strategy `B`.
theorem card_hits_le_maxHits (z : Z) :
    (R.hits u₁ u₂ s B z).card ≤ R.maxHits u₁ u₂ s z :=
  -- `le_sup : b ∈ U → f b ≤ U.sup f`, for the answer `b = B z`.
  le_sup (f := fun b : (Fin R.m → F) × (Fin R.m → F) => (R.hits u₁ u₂ s (fun _ => b) z).card)
    (mem_univ (B z))

-- The maximum is attained: some answer `b` to `z` has exactly `|A_z|` DEEP-MCA-bad elements
-- (the paper's `b₁*, b₂*`).
theorem exists_eq_maxHits (z : Z) :
    ∃ b : (Fin R.m → F) × (Fin R.m → F),
      (R.hits u₁ u₂ s (fun _ => b) z).card = R.maxHits u₁ u₂ s z := by
  -- `exists_mem_eq_sup : U.Nonempty → ∃ i ∈ U, U.sup f = f i`, with `U = univ` (nonempty).
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup (univ : Finset ((Fin R.m → F) × (Fin R.m → F)))
    univ_nonempty fun b => (R.hits u₁ u₂ s (fun _ => b) z).card
  exact ⟨b, hb.symm⟩

-- A worst-case strategy: a single `B'` that attains `|A_z|` at every `z` at once.
theorem exists_worst_answers :
    ∃ B' : Z → (Fin R.m → F) × (Fin R.m → F),
      ∀ z, (R.hits u₁ u₂ s B' z).card = R.maxHits u₁ u₂ s z := by
  -- The axiom of choice (`Classical.axiom_of_choice`) applied to `exists_eq_maxHits`.
  obtain ⟨b, hb⟩ := Classical.axiom_of_choice (R.exists_eq_maxHits u₁ u₂ s)
  exact ⟨b, hb⟩

/-- **Theorem 3.4, counting form.** For every `t`,
`t (t - 1) (t - N) · #{z ∈ Z | |A_z| ≥ t} ≤ (q L)³ M`, where `N = n - s + 1`, every nonzero
`v ∈ F^ℓ` has `φ_z(v) = 0` for at most `M` of the `z ∈ Z`, and `|A_z|` is the largest number of
DEEP-MCA-bad elements at `z` over all answers. As in `main_thm_gen_nat`, the subtractions are
those of `ℕ`, so for `t ≤ N` the left-hand side is `0`. -/
theorem main_thm_nat (L M t : ℕ) (hL : R.ListDecodable s L)
    (hM : ∀ v : Fin R.ℓ → F, v ≠ 0 → (univ.filter fun z : Z => R.φ z v = 0).card ≤ M) :
    t * (t - 1) * (t - (Fintype.card ι - s + 1)) *
        (univ.filter fun z : Z => t ≤ R.maxHits u₁ u₂ s z).card ≤
      (Fintype.card F * L) ^ 3 * M := by
  -- A worst-case strategy `B'`, with `hB' : ∀ z, |A_{z, B' z}| = |A_z|`.
  obtain ⟨B', hB'⟩ := R.exists_worst_answers u₁ u₂ s
  -- Replace `|A_z|` by `|A_{z, B' z}|` in the goal (`hB'` from right to left).
  simp only [← hB']
  -- This is `main_thm_gen_nat` for the strategy `B'`.
  exact R.main_thm_gen_nat u₁ u₂ s B' L M t hL hM

/-- **Theorem 3.4.** Let `C` be list decodable with list size `L` at agreement `s`, and let `ε` be
an error bound of the zero evader. Then for every integer `t ≥ n - s + 2` and `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - (n - s) - 1))`, where `|A_z|` is the largest number of
DEEP-MCA-bad elements at `z` over all answers `b₁, b₂`. -/
theorem main_thm [Nonempty Z] (L t : ℕ) (ε : ℝ) (hL : R.ListDecodable s L)
    (hε : R.IsErrorBound ε) (ht : Fintype.card ι - s + 2 ≤ t) :
    ((univ.filter fun z : Z => t ≤ R.maxHits u₁ u₂ s z).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - ((Fintype.card ι - s + 1 : ℕ) : ℝ))) := by
  -- A worst-case strategy `B'`, as in `main_thm_nat`.
  obtain ⟨B', hB'⟩ := R.exists_worst_answers u₁ u₂ s
  simp only [← hB']
  -- This is `main_thm_gen` for the strategy `B'`.
  exact R.main_thm_gen u₁ u₂ s B' L t ε hL hε ht

/-- **How Theorem 3.4 is used (the fold challenge).** If `|A_z| < t`, then whatever the answers `B`
to `z`, a uniform challenge `α ∈ F` is DEEP-MCA-bad with probability at most `(t - 1)/q`. With
`t = (n - s) + 2`, the least threshold of `main_thm`, this is `(n - s + 1)/q`; for
`s = ⌈(1 - δ) n⌉` it is at most the term `(δ n + 1)/|F|` of the error `κ₂` of Theorem 4.3. -/
theorem fold_challenge_le (z : Z) (t : ℕ) (hz : R.maxHits u₁ u₂ s z < t) :
    ((univ.filter fun α : F => R.DeepBad u₁ u₂ s z (B z) α).card : ℝ) / Fintype.card F ≤
      ((t : ℝ) - 1) / Fintype.card F := by
  -- In `ℕ`: `|A_{z, B z}| ≤ |A_z| < t`, so `|A_{z, B z}| + 1 ≤ t`.
  have h : (R.hits u₁ u₂ s B z).card + 1 ≤ t := by
    have := R.card_hits_le_maxHits u₁ u₂ s B z
    omega
  -- The same in `ℝ`.
  have h' : ((R.hits u₁ u₂ s B z).card : ℝ) + 1 ≤ t := by exact_mod_cast h
  -- The filter is `A_{z, B z}` by definition (`hits`), ...
  change ((R.hits u₁ u₂ s B z).card : ℝ) / _ ≤ _
  -- ... both sides are divided by `q ≥ 0` (`gcongr`), and `|A_{z, B z}| ≤ t - 1` (`linarith`).
  gcongr
  linarith

end Counting

/-! ### Theorem 3.4 with the proximity parameter `δ` -/

section WithDelta

-- In this section `u₁ u₂` are the words.
variable (u₁ u₂ : ι → F)

/-- The codewords of `C`, as words (functions `ι → F`): the image of the encoding map. -/
def codewords : Finset (ι → F) :=
  (univ : Finset (Fin R.ℓ → F)).image R.enc

/-- Counting the codewords of `C` with a property is counting their messages, since the encoding
map is injective. -/
theorem card_filter_codewords (P : (ι → F) → Prop) :
    ((R.codewords).filter P).card = (univ.filter fun c : Fin R.ℓ → F => P (R.enc c)).card := by
  -- The filter of an image is the image of a filter (`filter_image`), and an image under an
  -- injective map has the same size (`card_image_of_injective`).
  rw [codewords, filter_image, card_image_of_injective _ R.enc_inj]

/-- With `s = ⌈(1 - δ) n⌉`, the MCA property of `SatisfiesMCA` is the `δ`-MCA property of the
paper, about the sets `S` of size at least `(1 - δ) n`. -/
theorem satisfiesMCA_ceil_iff (δ : ℝ) (α : F) :
    R.SatisfiesMCA u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ α ↔
      ∀ S : Finset ι, (1 - δ) * Fintype.card ι ≤ S.card →
        (∃ c : Fin R.ℓ → F, ∀ i ∈ S, R.enc c i = R.fold u₁ u₂ α i) → R.CA u₁ u₂ S := by
  -- `Nat.ceil_le : ⌈y⌉₊ ≤ k ↔ y ≤ k`.
  simp only [SatisfiesMCA, Nat.ceil_le]

/-- With `s = ⌈(1 - δ) n⌉`, the pretenders of `IsPretender` are those of Definition 3.2, with
agreement sets of size at least `(1 - δ) n`. -/
theorem isPretender_ceil_iff (δ : ℝ) (α : F) (c : Fin R.ℓ → F) :
    R.IsPretender u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ α c ↔
      ∃ S : Finset ι, (1 - δ) * Fintype.card ι ≤ S.card ∧
        (∀ i ∈ S, R.enc c i = R.fold u₁ u₂ α i) ∧ ¬ R.CA u₁ u₂ S := by
  -- `Nat.ceil_le : ⌈y⌉₊ ≤ k ↔ y ≤ k`.
  simp only [IsPretender, Nat.ceil_le]

/-- The list decodability of Theorem 3.4, "`C` is `(δ, L)`-list decodable": if every word has at
most `L` codewords of `C` at relative Hamming distance at most `δ` (at most `δ n` positions where
they differ), then `C` is list decodable with list size `L` at agreement `⌈(1 - δ) n⌉`. -/
theorem listDecodable_of_delta {δ : ℝ} {L : ℕ}
    (hL : ∀ w : ι → F, ((R.codewords).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L) :
    R.ListDecodable ⌈(1 - δ) * Fintype.card ι⌉₊ L := by
  intro w
  -- Count the close codewords through their messages (`card_filter_codewords`).
  have h := hL w
  rw [R.card_filter_codewords] at h
  -- A codeword that agrees with `w` on at least `⌈(1 - δ) n⌉` positions differs from `w` on at
  -- most `δ n` positions, so the set to bound lies in the set of `h`.
  refine le_trans (card_le_card fun c hc => ?_) h
  simp only [mem_filter, mem_univ, true_and, ne_eq] at hc ⊢
  -- The positions split into those where `c(i) = w(i)` and the others.
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun i => R.enc c i = w i)
  rw [card_univ] at hsplit
  -- `(1 - δ) n ≤ #agree` (`Nat.ceil_le`), and `#agree + #differ = n` in `ℝ`.
  have hagree : (1 - δ) * Fintype.card ι ≤
      ((univ.filter fun i => R.enc c i = w i).card : ℝ) := Nat.ceil_le.mp hc
  have hsplit' : ((univ.filter fun i => R.enc c i = w i).card : ℝ) +
      ((univ.filter fun i => ¬ R.enc c i = w i).card : ℝ) = Fintype.card ι := by
    exact_mod_cast hsplit
  -- So `#differ = n - #agree ≤ n - (1 - δ) n = δ n`.
  linarith

/-- With `s = ⌈(1 - δ) n⌉` and `δ ≥ 0`, the integer `n - s` is at most `δ n`. -/
theorem card_sub_ceil_le {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Fintype.card ι - ⌈(1 - δ) * Fintype.card ι⌉₊ : ℕ) : ℝ) ≤ δ * Fintype.card ι := by
  -- If `s ≤ n`, because `s ≥ (1 - δ) n` (`Nat.le_ceil`); otherwise `n - s = 0` and `δ n ≥ 0`.
  rcases le_or_gt ⌈(1 - δ) * Fintype.card ι⌉₊ (Fintype.card ι) with h | h
  · rw [Nat.cast_sub h]
    have : (1 - δ) * Fintype.card ι ≤ (⌈(1 - δ) * Fintype.card ι⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    positivity

/-- **Theorem 3.4, as stated in the paper.** Let `δ ≥ 0` (the paper takes `δ ∈ (0, 1)`), let `C`
be `(δ, L)`-list decodable, and let `ε` be an error bound of the zero evader. Then for every
integer `t ≥ δ n + 2` and `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - δ n - 1))`, where `A_z` is defined with agreement sets
of size at least `(1 - δ) n`: `s = ⌈(1 - δ) n⌉`, for which the MCA property and the pretenders
are those of the paper (`satisfiesMCA_ceil_iff`, `isPretender_ceil_iff`). -/
theorem main_thm_delta [Nonempty Z] {δ ε : ℝ} (hδ : 0 ≤ δ) (L t : ℕ)
    (hL : ∀ w : ι → F, ((R.codewords).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (hε : R.IsErrorBound ε) (ht : δ * Fintype.card ι + 2 ≤ t) :
    ((univ.filter fun z : Z =>
        t ≤ R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - δ * Fintype.card ι - 1)) := by
  -- Idea: `main_thm` with `s = ⌈(1 - δ) n⌉`, for which `n - s ≤ δ n`; a smaller `n - s` gives a
  -- larger denominator, hence a smaller bound.
  set s := ⌈(1 - δ) * Fintype.card ι⌉₊ with hs
  -- `δ n ≥ 0`.
  have hδn : 0 ≤ δ * Fintype.card ι := by positivity
  -- `n - s ≤ δ n` (`card_sub_ceil_le`).
  have he : ((Fintype.card ι - s : ℕ) : ℝ) ≤ δ * Fintype.card ι := card_sub_ceil_le hδ
  -- So `t ≥ δ n + 2 ≥ (n - s) + 2`, in `ℕ`.
  have htN : Fintype.card ι - s + 2 ≤ t := by
    have : ((Fintype.card ι - s : ℕ) : ℝ) + 2 ≤ t := by linarith
    exact_mod_cast this
  -- `main_thm` with `s` and `L` (list decodability by `listDecodable_of_delta`).
  have hmain := R.main_thm u₁ u₂ s L t ε (R.listDecodable_of_delta hL) hε htN
  refine hmain.trans ?_
  -- It remains to compare the denominators: `t (t - 1) (t - δ n - 1) ≤ t (t - 1) (t - N)` with
  -- `N = (n - s) + 1`, both positive (`div_le_div_of_nonneg_left`), with the same nonnegative
  -- numerator.
  have ht2 : (2 : ℝ) ≤ t := by linarith
  have hpos : 0 < (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - δ * Fintype.card ι - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hε.1) hpos
  -- Write `↑((n - s) + 1)` as `↑(n - s) + 1` (`push_cast`). Then `t - δ n - 1 ≤ t - N`,
  -- multiplied by `t (t - 1) ≥ 0`.
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) (by linarith))

/-- **Theorem 3.4, as stated in the paper, for a real threshold.** The same as `main_thm_delta`
for a real number `t ≥ δ n + 2`. -/
-- (The paper does not say that `t` is an integer. `|A_z| ≥ t` is `|A_z| ≥ ⌈t⌉`, and the bound for
-- `⌈t⌉` is at most the bound for `t`.)
theorem main_thm_delta_real [Nonempty Z] {δ ε : ℝ} (hδ : 0 ≤ δ) (L : ℕ) (t : ℝ)
    (hL : ∀ w : ι → F, ((R.codewords).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (hε : R.IsErrorBound ε) (ht : δ * Fintype.card ι + 2 ≤ t) :
    ((univ.filter fun z : Z =>
        t ≤ (R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z : ℝ)).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε / (t * (t - 1) * (t - δ * Fintype.card ι - 1)) := by
  -- `k = ⌈t⌉`, a natural number with `t ≤ k` (`Nat.le_ceil`).
  set k := ⌈t⌉₊ with hk
  have htk : t ≤ (k : ℝ) := Nat.le_ceil t
  have hδn : 0 ≤ δ * Fintype.card ι := by positivity
  -- `main_thm_delta` for the integer `k ≥ t ≥ δ n + 2`.
  have hmain := R.main_thm_delta u₁ u₂ hδ L k hL hε (ht.trans htk)
  -- For a natural number `a`, `t ≤ a ↔ ⌈t⌉ ≤ a` (`Nat.ceil_le`): the set of `z` is the same.
  simp only [← Nat.ceil_le]
  refine hmain.trans ?_
  -- It remains to compare the denominators: each factor of `t (t - 1) (t - δ n - 1)` is positive
  -- and at most the factor of `k (k - 1) (k - δ n - 1)`.
  have hpos : 0 < t * (t - 1) * (t - δ * Fintype.card ι - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hε.1) hpos
  -- The second and third factors: `t - 1 ≤ k - 1` and `t - δ n - 1 ≤ k - δ n - 1`.
  have h1 : t - 1 ≤ (k : ℝ) - 1 := by linarith
  have h2 : t - δ * Fintype.card ι - 1 ≤ (k : ℝ) - δ * Fintype.card ι - 1 := by linarith
  -- `mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a c ≤ b d`, applied twice: first to
  -- `t (t - 1) ≤ k (k - 1)`, then to the products with the third factors.
  exact mul_le_mul (mul_le_mul htk h1 (by linarith) (by linarith)) h2 (by linarith)
    (mul_nonneg (by linarith) (by linarith))

/-- **Theorem 3.4 with `⌊δ n⌋` in place of `δ n`.** Under the hypotheses of `main_thm_delta`, for
every integer `t ≥ ⌊δ n⌋ + 2` and `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - ⌊δ n⌋ - 1))`. -/
-- (The notions of Section 3 depend on `δ` only through `⌊δ n⌋`, the largest number of positions
-- in which a word may differ from a `δ`-close codeword. When `δ n` is an integer this is
-- `main_thm_delta`. When it is not, this form is slightly stronger: it covers the threshold
-- `t = ⌊δ n⌋ + 2`, the least integer `t` for which "not `|A_z| ≥ t`" gives `|A_z| ≤ δ n + 1`.)
theorem main_thm_delta_floor [Nonempty Z] {δ ε : ℝ} (hδ : 0 ≤ δ) (L t : ℕ)
    (hL : ∀ w : ι → F, ((R.codewords).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (hε : R.IsErrorBound ε) (ht : ⌊δ * Fintype.card ι⌋₊ + 2 ≤ t) :
    ((univ.filter fun z : Z =>
        t ≤ R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - (⌊δ * Fintype.card ι⌋₊ : ℝ) - 1)) := by
  -- Idea: `main_thm` with `s = ⌈(1 - δ) n⌉`, for which `n - s ≤ ⌊δ n⌋`. Abbreviations `s` and
  -- `e = ⌊δ n⌋`.
  set s := ⌈(1 - δ) * Fintype.card ι⌉₊ with hs
  set e := ⌊δ * Fintype.card ι⌋₊ with he
  -- `n - s ≤ e`: the natural number `n - s` is at most `δ n` (`card_sub_ceil_le`), hence at most
  -- `⌊δ n⌋` (`Nat.le_floor`).
  have hle : Fintype.card ι - s ≤ e := Nat.le_floor (card_sub_ceil_le hδ)
  -- So `t ≥ e + 2 ≥ (n - s) + 2`.
  have htN : Fintype.card ι - s + 2 ≤ t := by omega
  -- `main_thm` with `s` and `L` (list decodability by `listDecodable_of_delta`).
  have hmain := R.main_thm u₁ u₂ s L t ε (R.listDecodable_of_delta hL) hε htN
  refine hmain.trans ?_
  -- The same facts in `ℝ`: `n - s ≤ e`, `0 ≤ e` and `e + 2 ≤ t`.
  have hle' : ((Fintype.card ι - s : ℕ) : ℝ) ≤ (e : ℝ) := Nat.cast_le.mpr hle
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg e
  have hte : (e : ℝ) + 2 ≤ t := by exact_mod_cast ht
  -- It remains to compare the denominators, as in `main_thm_delta`:
  -- `t (t - 1) (t - e - 1) ≤ t (t - 1) (t - N)` with `N = (n - s) + 1`, both positive.
  have hpos : 0 < (t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - (e : ℝ) - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hε.1) hpos
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) (by linarith))

end WithDelta

end Setup

end BEEP.Main
