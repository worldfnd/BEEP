-- [AI-drafted (claude-fable-5-2), 2026-11-16, at the author's request, as part of
-- `BEEP/MainTheorem.lean`, the formalization of Theorem 3.4 (`t:main_thm`) of `paper/main.typ`.
-- AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: that file is now the three
-- files `BEEP/Scalar/Defs.lean` (the definitions that the statement of the theorem uses),
-- `BEEP/Scalar/Theorem.lean` (this one: the statements) and `BEEP/Scalar/Proof.lean` (the lemmas,
-- the other definitions and the proofs). The statements are those of `BEEP/MainTheorem.lean`,
-- without change; each proof is now one line, and the proof that was here is in
-- `BEEP/Scalar/Proof.lean`. The namespace `BEEP.Main` is now `BEEP.Scalar`. Please review the
-- statements against the paper.]
-- [AI-revised (claude-fable-5-2), 2026-11-17, later, at the author's remark: `fold_challenge_le`
-- is stated for every pair `b = (b₁, b₂)` (it was stated for a function from `z` to such pairs).
-- The other statements are unchanged. Please review.]

-- A line starting with `--` is a comment, which Lean ignores. The reading guide of
-- `BEEP/Scalar/Defs.lean` explains the notation.

-- Load the proofs. `BEEP/Scalar/Proof.lean` loads `BEEP/Scalar/Defs.lean` (the definitions), which
-- loads Mathlib.
import BEEP.Scalar.Proof

/-!
# BEEP with scalar challenges: Theorem 3.4

The statement of Theorem 3.4 of the BEEP paper (`paper/main.typ`, Section 3, "Better Elimination
of Pretenders", label `t:main_thm`, "For most `z ∈ Z`, there are few DEEP-MCA-bad elements
`α ∈ F`"), about the objects defined in `BEEP/Scalar/Defs.lean`. Read that file first: its module
documentation has the setting, the dictionary between the paper and Lean, and a guide to the
notation.

Every proof in this file is one line: it calls the theorem with the same name followed by
`_proof`, which `BEEP/Scalar/Proof.lean` proves from the lemmas of the paper. Lean accepts this
file only if these proofs are complete, so the statements below are proved, and there is no need
to read `BEEP/Scalar/Proof.lean` to know what they say.

## The statements

`main_thm_delta` is the theorem as the paper states it. The others are variants.

* `BEEP.Scalar.Setup.main_thm_delta` (Theorem 3.4 as stated in the paper): let `δ ≥ 0`, let `C`
  be `(δ, L)`-list decodable, and let `ε` be an error bound of the zero evader. Then for every
  integer `t ≥ δ n + 2`, for `z` uniform in `Z`,
  `Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - δ n - 1))`.
* `BEEP.Scalar.Setup.main_thm_delta_real`: the same for a real threshold `t`.
* `BEEP.Scalar.Setup.main_thm_delta_floor`: the same with `⌊δ n⌋` in place of `δ n`, for every
  integer `t ≥ ⌊δ n⌋ + 2`. When `δ n` is not an integer this is slightly stronger: it covers the
  threshold `t = ⌊δ n⌋ + 2`, which `main_thm_delta` does not, and its bound is smaller.
* `BEEP.Scalar.Setup.main_thm` (Theorem 3.4 with the integer agreement threshold `s` of the
  definitions): for every integer `t ≥ n - s + 2`, for `z` uniform in `Z`,
  `Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - (n - s) - 1))`. The three forms with `δ` follow
  from this one with `s = ⌈(1 - δ) n⌉`.
* `BEEP.Scalar.Setup.main_thm_nat` (Theorem 3.4, counting form): for every `t`,
  `t (t - 1) (t - (n - s) - 1) · #{z ∈ Z | |A_z| ≥ t} ≤ (q L)³ M`, where `M` bounds the number of
  `z` with `φ_z(v) = 0` for every nonzero `v`. The subtractions are those of `ℕ`, so for
  `t ≤ n - s + 1` the left-hand side is `0` and the statement says nothing.
* `BEEP.Scalar.Setup.fold_challenge_le`: if `|A_z| < t`, then a uniform challenge is DEEP-MCA-bad
  with probability at most `(t - 1)/q`. With the least threshold of `main_thm_delta_floor`,
  `t = ⌊δ n⌋ + 2`, this is `(⌊δ n⌋ + 1)/q`, which is at most the term `(δ n + 1)/|F|` of the error
  `κ₂` of Theorem 4.3 (and equal to it when `δ n` is an integer). Theorem 4.3 is not formalized
  here.

In all of them `|A_z|` is `R.maxHits u₁ u₂ s z`, the largest number of DEEP-MCA-bad elements at
`z` over all `b₁, b₂ ∈ F^m`.

## How the statements are written

* `q = |F|`, `n` and `|Z|` are `Fintype.card F`, `Fintype.card ι` and `Fintype.card Z`.
* A probability over a uniform `z ∈ Z` is the number of the `z` with the property divided by
  `|Z|`: `((univ.filter fun z : Z => ...).card : ℝ) / Fintype.card Z`.
* `(k : ℝ)` is the natural number `k` viewed as a real number: the bounds are computed in `ℝ`.
  In the counting form everything is a natural number.
* In the forms with `δ`, the agreement threshold `s` is `⌈(1 - δ) * Fintype.card ι⌉₊`, that is,
  `⌈(1 - δ) n⌉`, and "`C` is `(δ, L)`-list decodable" is the hypothesis `hL`: every word `w` has
  at most `L` codewords `c` of `C` with at most `δ n` positions `i` where `c i ≠ w i`.

## What is not formalized, and what is not assumed

Since November 17, 2026 the paper's Theorem 3.4 ends with the sentence "Moreover, if `C` has
`δ`-MCA error `ε_MCA` then the factor `(|F| L)³` can be replaced by `(ε_MCA |F| L)³`". This
sentence is not formalized: the statements below have the factor `(q L)³`.

Not needed for Theorem 3.4 in this form, and so not assumed: that `n` is a power of two, that
`δ < 1`, that `ε ≤ 1` and that `L ≥ 1`. The injectivity of the encoding map is used only to count
codewords instead of messages in the forms with `δ` (`card_filter_codewords` in
`BEEP/Scalar/Proof.lean`).
-/

-- `open Finset` lets us write `univ`, `filter`, `card`, ... instead of `Finset.univ`,
-- `Finset.filter`, `Finset.card`, ... (Mathlib's library on finite sets).
open Finset

-- All names defined below get the prefix `BEEP.Scalar.` (e.g. `BEEP.Scalar.Setup.main_thm_delta`).
-- The namespace is closed by `end BEEP.Scalar` at the end of the file.
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

namespace Setup

-- `R` is the data of the setting. Every definition and theorem below that mentions `R` takes it
-- as its first explicit argument, written with a dot: `R.fold`, `R.IsPretender`, ...
variable (R : Setup F ι Z)

/-! ### Theorem 3.4, as stated in the paper -/

section WithDelta

-- In this section `u₁ u₂` are the words.
variable (u₁ u₂ : ι → F)

/-- **Theorem 3.4, as stated in the paper.** Let `δ ≥ 0` (the paper takes `δ ∈ (0, 1)`), let `C`
be `(δ, L)`-list decodable, and let `ε` be an error bound of the zero evader. Then for every
integer `t ≥ δ n + 2` and `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - δ n - 1))`, where `A_z` is defined with agreement sets
of size at least `(1 - δ) n`: `s = ⌈(1 - δ) n⌉`, for which the MCA property and the pretenders
are those of the paper (`satisfiesMCA_ceil_iff` and `isPretender_ceil_iff` in `Proof.lean`). -/
theorem main_thm_delta [Nonempty Z] {δ ε : ℝ} (hδ : 0 ≤ δ) (L t : ℕ)
    (hL : ∀ w : ι → F, ((R.codewords).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (hε : R.IsErrorBound ε) (ht : δ * Fintype.card ι + 2 ≤ t) :
    ((univ.filter fun z : Z =>
        t ≤ R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - δ * Fintype.card ι - 1)) :=
  R.main_thm_delta_proof u₁ u₂ hδ L t hL hε ht

/-! ### Variants: a real threshold `t`, and `⌊δ n⌋` in place of `δ n` -/

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
      ((Fintype.card F : ℝ) * L) ^ 3 * ε / (t * (t - 1) * (t - δ * Fintype.card ι - 1)) :=
  R.main_thm_delta_real_proof u₁ u₂ hδ L t hL hε ht

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
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - (⌊δ * Fintype.card ι⌋₊ : ℝ) - 1)) :=
  R.main_thm_delta_floor_proof u₁ u₂ hδ L t hL hε ht

end WithDelta

/-! ### Variants: the integer agreement threshold `s` of the definitions -/

section Counting

-- In this section `u₁ u₂` are the words and `s` is the agreement threshold.
variable (u₁ u₂ : ι → F) (s : ℕ)

/-- **Theorem 3.4, with the agreement threshold `s`.** Let `C` be list decodable with list size
`L` at agreement `s`, and let `ε` be an error bound of the zero evader. Then for every integer
`t ≥ n - s + 2` and `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (q L)³ ε / (t (t - 1) (t - (n - s) - 1))`, where `|A_z|` is the largest number of
DEEP-MCA-bad elements at `z` over all `b₁, b₂ ∈ F^m`. -/
theorem main_thm [Nonempty Z] (L t : ℕ) (ε : ℝ) (hL : R.ListDecodable s L)
    (hε : R.IsErrorBound ε) (ht : Fintype.card ι - s + 2 ≤ t) :
    ((univ.filter fun z : Z => t ≤ R.maxHits u₁ u₂ s z).card : ℝ) / Fintype.card Z ≤
      ((Fintype.card F : ℝ) * L) ^ 3 * ε /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - ((Fintype.card ι - s + 1 : ℕ) : ℝ))) :=
  R.main_thm_proof u₁ u₂ s L t ε hL hε ht

/-- **Theorem 3.4, counting form.** For every `t`,
`t (t - 1) (t - N) · #{z ∈ Z | |A_z| ≥ t} ≤ (q L)³ M`, where `N = n - s + 1`, every nonzero
`v ∈ F^ℓ` has `φ_z(v) = 0` for at most `M` of the `z ∈ Z`, and `|A_z|` is the largest number of
DEEP-MCA-bad elements at `z` over all `b₁, b₂`. The subtractions are those of `ℕ`, so for
`t ≤ N` the left-hand side is `0`. -/
theorem main_thm_nat (L M t : ℕ) (hL : R.ListDecodable s L)
    (hM : ∀ v : Fin R.ℓ → F, v ≠ 0 → (univ.filter fun z : Z => R.φ z v = 0).card ≤ M) :
    t * (t - 1) * (t - (Fintype.card ι - s + 1)) *
        (univ.filter fun z : Z => t ≤ R.maxHits u₁ u₂ s z).card ≤
      (Fintype.card F * L) ^ 3 * M :=
  R.main_thm_nat_proof u₁ u₂ s L M t hL hM

/-- **How Theorem 3.4 is used (the fold challenge).** If `|A_z| < t`, then for every
`b = (b₁, b₂)`, a uniform challenge `α ∈ F` is DEEP-MCA-bad with respect to `z, b₁, b₂` with
probability at most `(t - 1)/q`. With `t = (n - s) + 2`, the least threshold of `main_thm`, this
is `(n - s + 1)/q`; for `s = ⌈(1 - δ) n⌉` it is at most the term `(δ n + 1)/|F|` of the error
`κ₂` of Theorem 4.3. -/
theorem fold_challenge_le (z : Z) (b : (Fin R.m → F) × (Fin R.m → F)) (t : ℕ)
    (hz : R.maxHits u₁ u₂ s z < t) :
    ((univ.filter fun α : F => R.DeepBad u₁ u₂ s z b α).card : ℝ) / Fintype.card F ≤
      ((t : ℝ) - 1) / Fintype.card F :=
  R.fold_challenge_le_proof u₁ u₂ s z b t hz

end Counting

end Setup

end BEEP.Scalar
