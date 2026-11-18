-- [AI-drafted (claude-fable-5-2), 2026-11-16, at the author's request, as part of
-- `BEEP/MainTheorem.lean`, the formalization of Theorem 3.4 (`t:main_thm`) of `paper/main.typ`.
-- AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: that file is now the three
-- files `BEEP/Scalar/Defs.lean` (this one: the definitions that the statement of the theorem
-- uses), `BEEP/Scalar/Theorem.lean` (the statements) and `BEEP/Scalar/Proof.lean` (the lemmas,
-- the other definitions and the proofs). The definitions are moved here without change. The
-- namespace `BEEP.Main` is now `BEEP.Scalar`, the comments are adapted to the three files, and
-- the paper's numbers are those of November 17 (the zero evader is now Definition 2.2). Please
-- review the definitions against the paper; the dictionary is in the module documentation.]
-- [AI-revised (claude-fable-5-2), 2026-11-17, later, at the author's remark that `hits` took a
-- "strategy": `hits` now takes the pair `b = (b₁, b₂)` (it took a function from `z` to such
-- pairs), so that `hits z b` is the paper's `A_{z, b₁, b₂}`. `maxHits` is written with it and is
-- the same function as before. Please review these two definitions.]

-- A line starting with `--` is a comment, which Lean ignores. In this file each comment explains
-- the line, or the few lines, directly below it. The reading guide after the module documentation
-- explains the notation.

-- Load Mathlib, Lean's library of formalized mathematics (fields, vector spaces, linear maps,
-- finite sets, sums, real numbers, ...). Every name used below and not defined in this file
-- (`Finset`, `univ`, `Fintype.card`, ...) comes from Mathlib.
import Mathlib

/-!
# BEEP with scalar challenges: the definitions of Theorem 3.4

Theorem 3.4 of the BEEP paper (`paper/main.typ`, Section 3, "Better Elimination of Pretenders",
label `t:main_thm`, "For most `z ∈ Z`, there are few DEEP-MCA-bad elements `α ∈ F`") is formalized
in three files:

* `BEEP/Scalar/Defs.lean` (this file): the definitions that the statement of the theorem uses.
  It has no lemma and no proof.
* `BEEP/Scalar/Theorem.lean`: the statement of the theorem, as in the paper and in a few
  variants. Every proof in it is one line, which calls a theorem of `BEEP/Scalar/Proof.lean`.
* `BEEP/Scalar/Proof.lean`: the proof, with its lemmas (Lemmas 3.7 to 3.10 of the paper among
  them) and the definitions that only the proof uses.

To know what is proved, read this file and then `BEEP/Scalar/Theorem.lean`. There is no need to
read `BEEP/Scalar/Proof.lean`: Lean accepts `BEEP/Scalar/Theorem.lean` only if every statement in
it is proved, and these statements mention only objects defined in this file or in Mathlib
(`check.sh` checks both).

"Scalar" refers to the folding challenge `α`, which is an element of `F`. In `BEEP/Affine`, the
formalization of Theorem 5.3, the challenge is a polynomial `σ + τ X`. The two formalizations do
not depend on each other.

The numbers of theorems, lemmas and definitions are those of the PDF compiled from
`paper/main.typ` on November 17, 2026, which numbers them within sections; the labels do not
change when the numbers do.

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
  `λ₁(α) u₁ + λ₂(α) u₂`. (Since November 17 the paper writes `θ₁(α)`, `θ₂(α)` for these weights.
  The Lean names `lam₁`, `lam₂` and the comments of the three files keep the letter `λ`; in the
  comments, `θ` is always a parameterized line, as in Definition 3.6.)
* The zero evader is a family of linear maps `φ_z : F^ℓ → F^m`, indexed by a finite nonempty type
  `Z` (Definition 2.2), here `R.φ z`. A number `ε ≥ 0` is an error bound of the evader if every
  nonzero `v ∈ F^ℓ` has `Pr_z[φ_z(v) = 0] ≤ ε` (`R.IsErrorBound ε`).
* The paper measures agreement with the proximity parameter `δ` (agreement sets of size at least
  `(1 - δ) n`). As in `BEEP/Affine/Defs.lean`, we use instead an integer agreement threshold `s`
  (agreement sets of size at least `s`), so that `δ n` becomes `n - s`.
  `BEEP/Scalar/Theorem.lean` states the theorem with `δ` again, with `s = ⌈(1 - δ) n⌉`. For this
  `s` and `0 ≤ δ ≤ 1`, `n - s = ⌊δ n⌋` (and `n - s ≤ ⌊δ n⌋ ≤ δ n` for every `δ ≥ 0`), so the
  form with `s` is slightly stronger when `δ n` is not an integer.

## Dictionary paper ↔ Lean

| paper (Sections 2 and 3 of `paper/main.typ`) | Lean |
|---|---|
| `Enc_C : F^ℓ → C`, linear and injective | `R.enc`, `R.enc_inj` |
| a codeword `c ∈ C` | its message `c : Fin R.ℓ → F`; the entries of the codeword are `R.enc c i` |
| the code `C`, as a set of words | `R.codewords` |
| the weights `θ₁(α)`, `θ₂(α)` (`λ₁(α)`, `λ₂(α)` in the comments), with `a₁ d₂ ≠ a₂ d₁` | `R.lam₁ α`, `R.lam₂ α`, `R.det_ne` |
| the fold `θ₁(α) · u₁ + θ₂(α) · u₂` | `R.fold u₁ u₂ α` |
| `(u₁, u₂)` has CA with `C` over `S` | `R.CA u₁ u₂ S` |
| `(1 - δ) n` | `s`; then `δ n` is `n - s` (`= ⌊δ n⌋` for `s = ⌈(1 - δ) n⌉` and `0 ≤ δ ≤ 1`) |
| `α` satisfies the `δ`-MCA property; `α` is MCA-bad (Definition 3.1) | `R.SatisfiesMCA u₁ u₂ s α`; `R.MCABad u₁ u₂ s α` |
| Definition 3.2, `c` is an `α`-pretender | `R.IsPretender u₁ u₂ s α c` |
| the zero evader `(φ_z)_{z ∈ Z}` (Definition 2.2); `ε` is an error bound | `R.φ`; `R.IsErrorBound ε` |
| Definition 3.3 (consistency); DEEP-MCA-bad element | `R.Consistent z b α c`; `R.DeepBad u₁ u₂ s z b α` |
| `A_{z, b₁, b₂}`; `|A_z|` (maximal over `b₁, b₂`) | `R.hits u₁ u₂ s z b`; `R.maxHits u₁ u₂ s z` |
| `C` is `(δ, L)`-list decodable | `R.ListDecodable s L` (or the hypothesis `hL` of `main_thm_delta`) |

The objects that only the proof uses (parameterized lines, the vector `U`, the sets `P` and
`T_z`) are in the dictionary of `BEEP/Scalar/Proof.lean`.
-/

/-!
## Reading guide for newcomers to Lean: the notation

This guide explains the notation of this file and of `BEEP/Scalar/Theorem.lean`. It follows the
one of `BEEP/Affine/Defs.lean`, with what is new here (linear maps, vectors). The guide of
`BEEP/Scalar/Proof.lean` explains how to read a proof.

**What Lean checks.** A Lean file is a list of definitions (`def`) and theorems (`theorem`). A
theorem is a statement followed by a proof, and Lean accepts the file only if every proof is
complete: no step is left to the reader. The three files compile with no errors and no `sorry`
(the keyword for a missing proof), so all their theorems are proved. The only axioms involved are
the three standard ones of Lean's logic (propositional extensionality, the axiom of choice, and
soundness of quotients), as the command `#print axioms BEEP.Scalar.Setup.main_thm_delta` shows.

**Types.** `x : X` means "`x` is an element of `X`". Types play the role of sets: `ℕ` (the
natural numbers, starting at `0`), `ℝ` (the reals), `F` (our field), `F × F` (pairs), `ι → F`
(functions from `ι` to `F`, that is, words of length `n`), `Fin k → F` (vectors of `F^k`).
Function application is written without brackets: `u₁ i` is `u₁(i)`, and `f a b` is `f(a, b)`.
`fun x => e` is the function `x ↦ e`.

**Statements are types as well.** `Prop` is the type of statements, and a proof of a statement
`P` is an element `h : P`. So the hypothesis `(hab : a ≠ b)` reads "`hab` is a proof that
`a ≠ b`". Logical symbols: `∧` (and), `∨` (or), `¬` (not), `→` (implies), `↔` (iff), `∀ x, P x`,
`∃ x, P x`, `∀ x ∈ S, P x`, `∃ x ∈ S, P x`, and `a ≠ b` for `¬ (a = b)`.

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

**Reading interactively.** In VS Code with the Lean 4 extension, hovering over a name shows its
statement or its definition, and a click with the `Ctrl` key (`Cmd` on a Mac) opens the place
where it is defined.

**Plan.** `Setup` collects the data of Sections 2.2, 2.3 and 3.1, and the section `Defs` sets up
the objects of Section 3.1 (`fold`, `CA`, `SatisfiesMCA`, `MCABad`, `IsPretender`, `Consistent`,
`DeepBad`, `ListDecodable`, `IsErrorBound`). The section `Hits` has the set `A_{z, b₁, b₂}` of
DEEP-MCA-bad elements (`hits`) and its largest size `|A_z|` (`maxHits`). The last definition,
`codewords`, is the code as a set of words.
-/

-- `open Finset` lets us write `univ`, `filter`, `card`, ... instead of `Finset.univ`,
-- `Finset.filter`, `Finset.card`, ... (Mathlib's library on finite sets).
open Finset

-- From here to the end of the file, definitions may use non-constructive ingredients (classical
-- logic in `hits`, real numbers in `IsErrorBound`), so Lean does not try to compile them into
-- executable code.
noncomputable section

-- All names defined below get the prefix `BEEP.Scalar.` (e.g. `BEEP.Scalar.Setup.IsPretender`),
-- so that they cannot clash with names in Mathlib or in `BEEP/Affine`. The namespace is closed by
-- `end BEEP.Scalar` at the end of the file.
namespace BEEP.Scalar

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
-- over `z ∈ Z` also assume that `Z` is nonempty (`[Nonempty Z]`), as Definition 2.2 does.
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
-- (The codewords are given by their messages `c₁ c₂`, as everywhere in these files.)
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
-- `α`-pretender is MCA-bad, see `mcaBad_iff_exists_pretender` in `BEEP/Scalar/Proof.lean`.)
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
same since the encoding map is injective, see `card_filter_codewords` in `Proof.lean`). -/
def ListDecodable (L : ℕ) : Prop :=
  ∀ w : ι → F, (univ.filter fun c : Fin R.ℓ → F =>
    s ≤ (univ.filter fun i => R.enc c i = w i).card).card ≤ L

/-- **Definition 2.2.** `ε` is an error bound of the zero evader: `ε ≥ 0`, and for every nonzero
`v ∈ F^ℓ`, `Pr_z[φ_z(v) = 0] ≤ ε`. The probability is the number of such `z` divided by `|Z|`. -/
-- (This definition does not mention `u₁ u₂ s`, so they are not among its arguments. The paper
-- takes `ε ∈ [0, 1]`; the bound `ε ≤ 1` is not needed.)
def IsErrorBound (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ v : Fin R.ℓ → F, v ≠ 0 →
    ((univ.filter fun z : Z => R.φ z v = 0).card : ℝ) / Fintype.card Z ≤ ε

end Defs

/-! ### The DEEP-MCA-bad elements at `z`, and their largest number `|A_z|` -/

section Hits

-- The two words and the agreement threshold, as in the section `Defs`.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- The set `A_{z, b₁, b₂}` of Theorem 3.4: the DEEP-MCA-bad elements with respect to `z` and
`b = (b₁, b₂)`, two vectors of `F^m`. -/
def hits (z : Z) (b : (Fin R.m → F) × (Fin R.m → F)) : Finset F :=
  univ.filter fun α => R.DeepBad u₁ u₂ s z b α

/-- `|A_z|` of Theorem 3.4: the largest `|A_{z, b₁, b₂}|` over all `(b₁, b₂)`, for a fixed `z`.
(The paper lets `b₁*, b₂*` be such that `|A_{z, b₁*, b₂*}|` is maximal, and `A_z` is that set.) -/
-- `univ.sup f` is the largest value of `f b` over all `b` (Mathlib's `Finset.sup`).
def maxHits (z : Z) : ℕ :=
  univ.sup fun b : (Fin R.m → F) × (Fin R.m → F) => (R.hits u₁ u₂ s z b).card

end Hits

/-! ### The code as a set of words -/

/-- The codewords of `C`, as words (functions `ι → F`): the image of the encoding map. -/
def codewords : Finset (ι → F) :=
  (univ : Finset (Fin R.ℓ → F)).image R.enc

end Setup

end BEEP.Scalar
