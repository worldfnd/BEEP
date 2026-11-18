-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request, as part of
-- `BEEP/AffineMain.lean`, the formalization of what is now Theorem 5.3 (`t:affine_main_0`) of
-- `paper/main.typ` (then Theorem 30 of `typst/deep+.typ`). AI-revised (claude-opus-5-5 and
-- claude-fable-5-2), 2026-11-16: the paper's new numbers and paths, in the comments only.
-- AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: that file is now the three
-- files `BEEP/Affine/Defs.lean` (this one: the definitions that the statement of the theorem
-- uses), `BEEP/Affine/Theorem.lean` (the statements) and `BEEP/Affine/Proof.lean` (the lemmas,
-- the other definitions and the proofs). The definitions are moved here without change. The
-- namespace `BEEP` is now `BEEP.Affine`, and the comments are adapted to the three files. Please
-- review the definitions against the paper; the dictionary is in the module documentation.]
-- [AI-revised (claude-fable-5-2), 2026-11-17, later, at the author's remark that `hits` took a
-- "strategy": `hits` now takes the pair `b = (b₁, b₂)` (it took a function from `z` to such
-- pairs), so that `hits z b` is the paper's `A_{z, b₁, b₂}`. `maxHits` is written with it and is
-- the same function as before. Please review these two definitions.]

-- A line starting with `--` is a comment, which Lean ignores. In this file each comment explains
-- the line, or the few lines, directly below it. The reading guide after the module documentation
-- explains the notation.

-- Load Mathlib, Lean's library of formalized mathematics (fields, polynomials, finite sets, sums,
-- real numbers, ...). Every name used below and not defined in this file (`Finset`, `Polynomial`,
-- `degreeLT`, `univ`, ...) comes from Mathlib.
import Mathlib

/-!
# BEEP with affine challenges: the definitions of Theorem 5.3

Theorem 5.3 of the BEEP paper (`paper/main.typ`, Section 5, "BEEP with affine folding for
Reed-Solomon codes", label `t:affine_main_0`, "For most `z ∈ F^m`, there are few DEEP-MCA-bad
challenges") is formalized in three files:

* `BEEP/Affine/Defs.lean` (this file): the definitions that the statement of the theorem uses.
  It has no lemma and no proof.
* `BEEP/Affine/Theorem.lean`: the statement of the theorem, as in the paper and in a few
  variants. Every proof in it is one line, which calls a theorem of `BEEP/Affine/Proof.lean`.
* `BEEP/Affine/Proof.lean`: the proof, with its lemmas (Lemma 5.5 of the paper among them) and
  the definitions that only the proof uses.

To know what is proved, read this file and then `BEEP/Affine/Theorem.lean`. There is no need to
read `BEEP/Affine/Proof.lean`: Lean accepts `BEEP/Affine/Theorem.lean` only if every statement in
it is proved, and these statements mention only objects defined in this file or in Mathlib
(`check.sh` checks both).

"Affine" refers to the folding challenge `α`, which is a polynomial `σ + τ X`. In `BEEP/Scalar`,
the formalization of Theorem 3.4, the challenge is an element of `F`. The two formalizations do
not depend on each other.

The numbers of theorems, lemmas and definitions are those of the PDF compiled from
`paper/main.typ` on November 17, 2026, which numbers them within sections; the labels do not
change when the numbers do.

## Setting (Section 5.1 of the paper)

* `F` is a finite field with `q = |F|` elements.
* The positions of a word form a finite type `ι` with `n = |ι|` elements, and `R.x : ι → F` gives
  the distinct evaluation points `x_i` of the Reed–Solomon codes (`R` collects the data that the
  paper fixes in Section 5.1, see `Setup`).
* As in the paper, a codeword of the Reed–Solomon code `RS_e` is identified with its polynomial
  of degree less than `e` (unique when `e ≤ n`), so `RS_e` is Mathlib's `degreeLT F e`. The code
  dimension is `ℓ`, `C = RS_ℓ` and `C⁺ = RS_{ℓ+1}`.
* A challenge is a polynomial `α = σ + τ X` of degree at most one. We write it as the pair
  `(σ, τ) : F × F`, so that there are `q²` challenges, and `chal (σ, τ)` is the polynomial.
* Words are folded with the weights `λ₁(α) = a₁ + α d₁` and `λ₂(α) = a₂ + α d₂` of Section 3, where
  `a₁ d₂ ≠ a₂ d₁`. The affine fold of `u₁, u₂` is the word with entries
  `λ₁(α)(x_i) u₁(i) + λ₂(α)(x_i) u₂(i)`. (Since November 17 the paper writes `θ₁(α)`, `θ₂(α)` for
  these weights, and `C_θ^{≡2}` for the set `C_λ^{≡2}`. The Lean names `lam₁`, `lam₂` and the
  comments of the three files keep the letter `λ`; in the comments, `θ` is always a parameterized
  line, as in Definition 5.4.)
* The paper measures agreement with the proximity parameter `δ` (agreement sets of size at least
  `(1 - δ) n`). As in `DeepFold/Lemma1.lean`, we use instead an integer agreement threshold `s`
  (agreement sets of size at least `s`), so that `δ n` becomes `n - s`.
  `BEEP/Affine/Theorem.lean` states the theorem with `δ` again, with `s = ⌈(1 - δ) n⌉`. For this
  `s` and `0 ≤ δ ≤ 1`, `n - s = ⌊δ n⌋` (and `n - s ≤ δ n` for every `δ ≥ 0`), so the `N` of the
  form with `s` is at most the paper's `N`, and the form with `s` is slightly stronger when `δ n`
  is not an integer.
* The zero evader is the evaluation at `m` points of `F`: for `z : Fin m → F` (that is,
  `z ∈ F^m`), `φ_z(p) = (p(z_1), ..., p(z_m))`.

## Dictionary paper ↔ Lean

| paper (Section 5 of `paper/main.typ`) | Lean |
|---|---|
| `x_1, ..., x_n`, distinct | `R.x : ι → F`, `R.x_inj` |
| `RS_e`, `C = RS_ℓ`, `C⁺ = RS_{ℓ+1}` | `degreeLT F e`, `degreeLT F R.ℓ`, `degreeLT F (R.ℓ + 1)` |
| `RS_e`, as a finite set of polynomials; as a set of words | `polysLT F e`; `R.rsWords e` |
| challenge `α = σ + τ X ∈ F^lin[X]` | `α : F × F`, the polynomial `chal α` |
| the weights `θ₁(α)`, `θ₂(α)` (`λ₁(α)`, `λ₂(α)` in the comments) | `R.lam₁ α`, `R.lam₂ α` |
| affine fold `θ₁(α) · u₁ + θ₂(α) · u₂` | `R.affineFold u₁ u₂ α` |
| `C_θ^{≡2}` (`C_λ^{≡2}` in the comments) | `R.Pairs c₁ c₂` |
| CA with `C_θ^{≡2}` over `S` up to one position | `R.CAUpToOne u₁ u₂ S` |
| `(1 - δ) n` | `s`; then `δ n` is `n - s` (`= ⌊δ n⌋` for `s = ⌈(1 - δ) n⌉` and `0 ≤ δ ≤ 1`) |
| Definition 5.1, `c` is an `α`-pretender; `α` MCA-bad | `R.IsPretender u₁ u₂ s α c`; `R.MCABad u₁ u₂ s α` |
| `φ_z`, Definition 5.2 (consistency) | `p.eval (z j)`; `R.Consistent z b α c` |
| DEEP-MCA-bad challenge | `R.DeepBad u₁ u₂ s z b α` |
| `A_{z, b₁, b₂}`; `|A_z|` (maximal over `b₁, b₂`) | `R.hits u₁ u₂ s z b`; `R.maxHits u₁ u₂ s z` |
| `C⁺` is `(δ, L)`-list decodable | `R.ListDecodable s L` (or the hypothesis `hL` of `affine_main_delta`) |

The objects that only the proof uses (parameterized lines, the polynomial `U`, the sets `P` and
`T_z`) are in the dictionary of `BEEP/Affine/Proof.lean`.
-/

/-!
## Reading guide for newcomers to Lean: the notation

This guide explains the notation of this file and of `BEEP/Affine/Theorem.lean`. It follows the
one of `2-deep-fold-lemma/lean/DeepFold/Lemma1.lean`, with what is new here (polynomials,
structures). The guide of `BEEP/Affine/Proof.lean` explains how to read a proof.

**What Lean checks.** A Lean file is a list of definitions (`def`) and theorems (`theorem`). A
theorem is a statement followed by a proof, and Lean accepts the file only if every proof is
complete: no step is left to the reader. The three files compile with no errors and no `sorry`
(the keyword for a missing proof), so all their theorems are proved. The only axioms involved are
the three standard ones of Lean's logic (propositional extensionality, the axiom of choice, and
soundness of quotients), as the command `#print axioms BEEP.Affine.Setup.affine_main_delta`
shows.

**Types.** `x : X` means "`x` is an element of `X`". Types play the role of sets: `ℕ` (the
natural numbers, starting at `0`), `ℝ` (the reals), `F` (our field), `F × F` (pairs), `ι → F`
(functions from `ι` to `F`, that is, words of length `n`), `Fin m → F` (vectors `z ∈ F^m`).
Function application is written without brackets: `u₁ i` is `u₁(i)`, and `f a b` is `f(a, b)`.
`fun x => e` is the function `x ↦ e`.

**Statements are types as well.** `Prop` is the type of statements, and a proof of a statement
`P` is an element `h : P`. So the hypothesis `(hD : D ≠ 0)` reads "`hD` is a proof that `D ≠ 0`".
Logical symbols: `∧` (and), `∨` (or), `¬` (not), `→` (implies), `↔` (iff), `∀ x, P x`,
`∃ x, P x`, `∀ x ∈ S, P x`, `∃ x ∈ S, P x`, `∃ S' ⊆ S, P S'`, and `a ≠ b` for `¬ (a = b)`.

**Arguments.** In `def f {X : Type*} [Field X] (x : X) ...`:
* `(x : X)` is an explicit argument, written whenever `f` is used;
* `{X : Type*}` is an implicit argument, which Lean infers from the other arguments;
* `[Field X]` says that `X` carries a field structure; Lean finds it automatically.
`Type*` means "some type": read it as "some set". A `variable` line declares arguments once,
for all the definitions and theorems that follow it and use them. `(m := m)` passes an implicit
argument by name, when Lean cannot infer it.

**Structures.** A `structure` is a record with named fields. `Setup F ι` below has the fields
`x`, `x_inj`, `ℓ`, `a₁`, `d₁`, `a₂`, `d₂` and `det_ne`, and for `R : Setup F ι` they are written
`R.x`, `R.ℓ`, `R.a₁`, ... Definitions in the namespace `Setup` are also written with a dot:
`R.affineFold u₁ u₂ α` is `Setup.affineFold R u₁ u₂ α`.

**Finite sets.** `Finset X` is the type of finite subsets of `X`.
* `univ` is the whole of a finite type `X`, and `Fintype.card X` is its number of elements;
* `U.filter P`, or `univ.filter fun x => P x`, is the set `{x ∈ U | P x}`;
* `U.card` is the number of elements of `U`; `∑ x ∈ U, f x` and `∑ x : X, f x` are sums;
* `U ∩ V`, `U ∪ V`, `U ⊆ V` as usual; `insert a U` is `{a} ∪ U`; `U.erase a` is `U` minus `{a}`;
  `U ×ˢ V` is the cartesian product; `Uᶜ` is the complement of `U` in `X`;
* `U.offDiag` is the set of ordered pairs `(i, j)` with `i, j ∈ U` and `i ≠ j`; it has
  `#U · #U - #U` elements;
* `F × F × F` means `F × (F × F)`, so the entries of a triple `t` are `t.1`, `t.2.1`, `t.2.2`.

**Polynomials.** `F[X]` is the ring of polynomials with coefficients in `F`, `X` is the variable
and `C a` is the constant polynomial `a`. `p.eval y` is the value `p(y)`, `p.coeff k` is the
coefficient of `X^k`, `p.degree` is the degree (with `degree 0 = -∞`) and `p.natDegree` the degree
as a natural number (with `natDegree 0 = 0`). `degreeLT F k` is the `F`-linear subspace of the
polynomials of degree less than `k`: the Reed–Solomon code `RS_k`, with codewords identified with
their polynomials. `a • p` is the scalar multiple of `p` by `a ∈ F`, which is `C a * p`.

**Numbers.** On `ℕ`, subtraction is truncated: `3 - 5 = 0`, and division rounds down. `(n : ℝ)`,
displayed `↑n`, is the natural number `n` viewed as a real number. `⌈y⌉₊` is the least natural
number `≥ y`.

**Reading interactively.** In VS Code with the Lean 4 extension, hovering over a name shows its
statement or its definition, and a click with the `Ctrl` key (`Cmd` on a Mac) opens the place
where it is defined.

**Plan.** The first section has the polynomials of bounded degree as a finite set (`polysLT`) and
the challenges (`chal`). Then `Setup` collects the data of Section 5.1, and the section `Defs`
sets up the objects of Section 5.1 (`affineFold`, `Pairs`, `CAUpToOne`, `IsPretender`, `MCABad`,
`Consistent`, `DeepBad`, `ListDecodable`). The section `Hits` has the set `A_{z, b₁, b₂}` of
DEEP-MCA-bad challenges (`hits`) and its largest size `|A_z|` (`maxHits`). The last definition,
`rsWords`, is a Reed–Solomon code as a set of words.
-/

-- `open Finset Polynomial` lets us write `univ`, `filter`, `C`, `X`, `degreeLT`, ... instead of
-- `Finset.univ`, `Finset.filter`, `Polynomial.C`, `Polynomial.X`, ..., and gives the notation
-- `F[X]`.
open Finset Polynomial

-- From here to the end of the file, definitions may use non-constructive ingredients (classical
-- logic in `hits`, polynomials), so Lean does not try to compile them into executable code.
noncomputable section

-- All names defined below get the prefix `BEEP.Affine.` (e.g. `BEEP.Affine.Setup.IsPretender`),
-- so that they cannot clash with names in Mathlib or in `BEEP/Scalar`. The namespace is closed by
-- `end BEEP.Affine` at the end of the file.
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

/-! ### Polynomials of degree less than `k`, and challenges -/

-- `variable (F) in` makes `F` an explicit argument of the next definition only: we write
-- `polysLT F k`, as Mathlib writes `degreeLT F k`.
variable (F) in
/-- The polynomials of degree less than `k`, as a finite set (for `k ≤ n`, one for each codeword of
`RS_k`). -/
-- Mathlib's `degreeLTEquiv F k` is the linear bijection between `degreeLT F k` and `F^k`, which sends
-- a polynomial to its first `k` coefficients. We take the image of all of `F^k` (a finite type)
-- under the inverse bijection, and keep the polynomials (`(... : F[X])` forgets that they lie in
-- `degreeLT F k`). A polynomial lies in `polysLT F k` exactly when it has degree less than `k`
-- (`mem_polysLT` in `BEEP/Affine/Proof.lean`).
def polysLT (k : ℕ) : Finset F[X] :=
  (univ : Finset (Fin k → F)).image fun v => ((degreeLTEquiv F k).symm v : F[X])

/-- The challenge `σ + τ X` of the pair `α = (σ, τ)`. -/
def chal (α : F × F) : F[X] := C α.2 * X + C α.1

/-! ### The setting of Section 5.1 -/

/-- The data that Section 5.1 of the paper fixes: the evaluation points, the code dimension and
the weights of the fold. -/
structure Setup (F : Type*) [Field F] (ι : Type*) where
  /-- the evaluation point `x_i` of each position `i` -/
  x : ι → F
  /-- the evaluation points are distinct -/
  x_inj : Function.Injective x
  /-- the code dimension `ℓ`, so that `C = RS_ℓ` and `C⁺ = RS_{ℓ+1}` -/
  ℓ : ℕ
  /-- the constant term of the weight `λ₁(α) = a₁ + α d₁` -/
  a₁ : F
  /-- the coefficient of `α` in `λ₁(α) = a₁ + α d₁` -/
  d₁ : F
  /-- the constant term of the weight `λ₂(α) = a₂ + α d₂` -/
  a₂ : F
  /-- the coefficient of `α` in `λ₂(α) = a₂ + α d₂` -/
  d₂ : F
  /-- the assumption `a₁ d₂ ≠ a₂ d₁` of Section 3 -/
  det_ne : a₁ * d₂ ≠ a₂ * d₁

namespace Setup

-- `R` is the data of Section 5.1. Every definition and theorem below that mentions `R` takes it as
-- its first explicit argument, written with a dot: `R.affineFold`, `R.IsPretender`, ...
variable (R : Setup F ι)

/-- The weight `λ₁(α) = a₁ + α d₁`, a polynomial of degree at most one. -/
def lam₁ (α : F × F) : F[X] := C R.a₁ + C R.d₁ * chal α

/-- The weight `λ₂(α) = a₂ + α d₂`. -/
def lam₂ (α : F × F) : F[X] := C R.a₂ + C R.d₂ * chal α

/-- The affine fold `λ₁(α) · u₁ + λ₂(α) · u₂` of two words: the word whose `i`-th entry is
`λ₁(α)(x_i) u₁(i) + λ₂(α)(x_i) u₂(i)`. -/
def affineFold (u₁ u₂ : ι → F) (α : F × F) : ι → F :=
  fun i => (R.lam₁ α).eval (R.x i) * u₁ i + (R.lam₂ α).eval (R.x i) * u₂ i

/-! ### Pretenders, consistency and DEEP-MCA-bad challenges -/

section Defs

-- In this section `u₁ u₂` are the two words, and `s` is the agreement threshold (the paper's
-- `(1 - δ) n`). Round brackets make them explicit arguments.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- `(c₁, c₂)` belongs to the set `C_λ^{≡2}`: `c₁, c₂ ∈ C⁺` and `d₁ c₁ + d₂ c₂ ∈ C`. -/
def Pairs (c₁ c₂ : F[X]) : Prop :=
  c₁ ∈ degreeLT F (R.ℓ + 1) ∧ c₂ ∈ degreeLT F (R.ℓ + 1) ∧
    C R.d₁ * c₁ + C R.d₂ * c₂ ∈ degreeLT F R.ℓ

/-- `(u₁, u₂)` has Correlated Agreement with `C_λ^{≡2}` over `S` up to one position: some pair
`(c₁, c₂)` of `C_λ^{≡2}` agrees with `(u₁, u₂)` on a set `S' ⊆ S` with `|S'| ≥ |S| - 1`. -/
-- (`|S'| ≥ |S| - 1` is written `|S| ≤ |S'| + 1`, which avoids truncated subtraction.)
def CAUpToOne (S : Finset ι) : Prop :=
  ∃ c₁ c₂ : F[X], R.Pairs c₁ c₂ ∧
    ∃ S' ⊆ S, S.card ≤ S'.card + 1 ∧ ∀ i ∈ S', u₁ i = c₁.eval (R.x i) ∧ u₂ i = c₂.eval (R.x i)

/-- **Definition 5.1.** `c ∈ C⁺` is an `α`-pretender: the affine fold and `c` agree on a set `S` of
size at least `s` such that `(u₁, u₂)` does not have Correlated Agreement with `C_λ^{≡2}` over `S`
up to one position. -/
def IsPretender (α : F × F) (c : F[X]) : Prop :=
  c ∈ degreeLT F (R.ℓ + 1) ∧
    ∃ S : Finset ι, s ≤ S.card ∧ (∀ i ∈ S, c.eval (R.x i) = R.affineFold u₁ u₂ α i) ∧
      ¬ R.CAUpToOne u₁ u₂ S

/-- **Definition 5.1, second part.** The challenge `α` is MCA-bad: there exists an `α`-pretender. -/
def MCABad (α : F × F) : Prop := ∃ c, R.IsPretender u₁ u₂ s α c

/-- **Definition 5.2.** `(α, c)` is consistent with `(z, b₁, b₂)`, where `b = (b₁, b₂)`:
`φ_z(c) = φ_z(λ₁(α)) ⊙ b₁ + φ_z(λ₂(α)) ⊙ b₂`, that is,
`c(z_j) = λ₁(α)(z_j) b₁(j) + λ₂(α)(z_j) b₂(j)` for every `j`. -/
def Consistent {m : ℕ} (z : Fin m → F) (b : (Fin m → F) × (Fin m → F)) (α : F × F)
    (c : F[X]) : Prop :=
  ∀ j, c.eval (z j) = (R.lam₁ α).eval (z j) * b.1 j + (R.lam₂ α).eval (z j) * b.2 j

/-- **Definition 5.2, second part.** `α` is a DEEP-MCA-bad challenge with respect to `z, b₁, b₂`
and `u₁, u₂`: `α` is MCA-bad and some `α`-pretender `c` is such that `(α, c)` is consistent with
`(z, b₁, b₂)`. -/
-- (The first condition follows from the second, since an `α`-pretender shows that `α` is MCA-bad;
-- we keep both, as the paper does.)
def DeepBad {m : ℕ} (z : Fin m → F) (b : (Fin m → F) × (Fin m → F)) (α : F × F) : Prop :=
  R.MCABad u₁ u₂ s α ∧ ∃ c, R.IsPretender u₁ u₂ s α c ∧ R.Consistent z b α c

/-- `C⁺` is list decodable with list size `L` at agreement `s`: every word `w` agrees on at least
`s` positions with at most `L` codewords of `C⁺` (counted through their polynomials). -/
def ListDecodable (L : ℕ) : Prop :=
  ∀ w : ι → F, ((polysLT F (R.ℓ + 1)).filter fun c =>
    s ≤ (univ.filter fun i => c.eval (R.x i) = w i).card).card ≤ L

end Defs

/-! ### The DEEP-MCA-bad challenges at `z`, and their largest number `|A_z|` -/

section Hits

-- The two words, the agreement threshold, and the number `m` of samples.
variable (u₁ u₂ : ι → F) (s : ℕ) {m : ℕ}

/-- The set `A_{z, b₁, b₂}` of Theorem 5.3: the DEEP-MCA-bad challenges with respect to `z` and
`b = (b₁, b₂)`, two vectors of `F^m`. -/
def hits (z : Fin m → F) (b : (Fin m → F) × (Fin m → F)) : Finset (F × F) :=
  univ.filter fun α => R.DeepBad u₁ u₂ s z b α

/-- `|A_z|` of Theorem 5.3: the largest `|A_{z, b₁, b₂}|` over all `(b₁, b₂)`, for a fixed `z`.
(The paper lets `b₁*, b₂*` be such that `|A_{z, b₁*, b₂*}|` is maximal, and `A_z` is that set.) -/
-- `univ.sup f` is the largest value of `f b` over all `b` (Mathlib's `Finset.sup`).
def maxHits (z : Fin m → F) : ℕ :=
  univ.sup fun b : (Fin m → F) × (Fin m → F) => (R.hits u₁ u₂ s z b).card

end Hits

/-! ### The Reed–Solomon codes as sets of words -/

/-- The codewords of `RS_k`, as words (functions `ι → F`). -/
def rsWords (k : ℕ) : Finset (ι → F) :=
  (polysLT F k).image fun p => fun i => p.eval (R.x i)

end Setup

end BEEP.Affine
