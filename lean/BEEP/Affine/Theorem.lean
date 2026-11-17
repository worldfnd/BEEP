-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request, as part of
-- `BEEP/AffineMain.lean`, the formalization of what is now Theorem 5.3 (`t:affine_main_0`) of
-- `paper/main.typ` (then Theorem 30 of `typst/deep+.typ`). AI-revised (claude-opus-5-5 and
-- claude-fable-5-2), 2026-11-16: the paper's new numbers and paths, in the comments only.
-- AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: that file is now the three
-- files `BEEP/Affine/Defs.lean` (the definitions that the statement of the theorem uses),
-- `BEEP/Affine/Theorem.lean` (this one: the statements) and `BEEP/Affine/Proof.lean` (the lemmas,
-- the other definitions and the proofs). The statements are those of `BEEP/AffineMain.lean`,
-- without change; each proof is now one line, and the proof that was here is in
-- `BEEP/Affine/Proof.lean`. The namespace `BEEP` is now `BEEP.Affine`. Please review the
-- statements against the paper.]

-- A line starting with `--` is a comment, which Lean ignores. The reading guide of
-- `BEEP/Affine/Defs.lean` explains the notation.

-- Load the proofs. `BEEP/Affine/Proof.lean` loads `BEEP/Affine/Defs.lean` (the definitions), which
-- loads Mathlib.
import BEEP.Affine.Proof

/-!
# BEEP with affine challenges: Theorem 5.3

The statement of Theorem 5.3 of the BEEP paper (`paper/main.typ`, Section 5, "BEEP with affine
folding for Reed-Solomon codes", label `t:affine_main_0`, "For most `z ∈ F^m`, there are few
DEEP-MCA-bad challenges"), about the objects defined in `BEEP/Affine/Defs.lean`. Read that file
first: its module documentation has the setting, the dictionary between the paper and Lean, and a
guide to the notation.

Every proof in this file is one line: it calls the theorem with the same name followed by
`_proof`, which `BEEP/Affine/Proof.lean` proves from Lemma 5.5 of the paper. Lean accepts this
file only if these proofs are complete, so the statements below are proved, and there is no need
to read `BEEP/Affine/Proof.lean` to know what they say.

## The statements

`affine_main_delta` is the theorem as the paper states it. The others are variants.

* `BEEP.Affine.Setup.affine_main_delta` (Theorem 5.3 as stated in the paper): let `δ ≥ 0`, let
  `ℓ + 1 ≤ n`, let `C⁺ = RS_{ℓ+1}` be `(δ, L)`-list decodable, and let
  `N = max(q, (δ n + 2)(δ n + 1)/2)`. Then for every integer `t ≥ N + 1`, for `z` uniform in
  `F^m`, `Pr[|A_z| ≥ t] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`.
* `BEEP.Affine.Setup.affine_main` (Theorem 5.3 with the integer agreement threshold `s` of the
  definitions): the same with `N = max(q, (n - s + 2)(n - s + 1)/2)`, for a code `C⁺` that is
  list decodable with list size `L` at agreement `s`. The form with `δ` follows from this one
  with `s = ⌈(1 - δ) n⌉`.
* `BEEP.Affine.Setup.affine_main_nat` (Theorem 5.3, counting form): for every `t`,
  `t (t - 1) (t - N) · #{z ∈ F^m | |A_z| ≥ t} ≤ (q² L)³ (ℓ + 1)^m`. The subtractions are those of
  `ℕ`, so for `t ≤ N` the left-hand side is `0` and the statement says nothing.
* `BEEP.Affine.Setup.fold_challenge_le`: if `|A_z| < t`, then a uniform challenge is DEEP-MCA-bad
  with probability at most `(t - 1)/q²`. This is the error of the fold challenge that follows the
  samples in a protocol that uses Theorem 5.3 (no such protocol is formalized here).

In all of them `|A_z|` is `R.maxHits u₁ u₂ s z`, the largest number of DEEP-MCA-bad challenges at
`z` over all answers `b₁, b₂`.

## How the statements are written

* `q = |F|` and `n` are `Fintype.card F` and `Fintype.card ι`.
* A probability over a uniform `z ∈ F^m` is the number of the `z` with the property divided by
  `q^m`: `((univ.filter fun z : Fin m → F => ...).card : ℝ) / (Fintype.card F : ℝ) ^ m`.
* `(k : ℝ)` is the natural number `k` viewed as a real number: the bounds are computed in `ℝ`.
  In the counting form everything is a natural number.
* In the form with `s`, `N` is `max (Fintype.card F) ((n - s + 2) * (n - s + 1) / 2)`, a natural
  number (the division is exact, since one of two consecutive numbers is even). In the form with
  `δ` it is the real number `max (Fintype.card F : ℝ) ((δ n + 2) * (δ n + 1) / 2)`.
* In the form with `δ`, the agreement threshold `s` is `⌈(1 - δ) * Fintype.card ι⌉₊`, that is,
  `⌈(1 - δ) n⌉`, and "`C⁺` is `(δ, L)`-list decodable" is the hypothesis `hL`: every word `w` has
  at most `L` codewords `c` of `RS_{ℓ+1}` with at most `δ n` positions `i` where `c i ≠ w i`.

## What is not assumed

The standing assumption `ℓ ≥ 1` of Section 5.1 is not needed for Theorem 5.3 in this form. The
list decodability of `R.ListDecodable` counts polynomials of degree `≤ ℓ`, which is the same as
counting the codewords of `C⁺` when `ℓ + 1 ≤ n` (`card_close_rsWords` in
`BEEP/Affine/Proof.lean`); the form with `δ` assumes `ℓ + 1 ≤ n` and counts codewords.
-/

-- `open Finset Polynomial` lets us write `univ`, `filter`, `card`, ... instead of `Finset.univ`,
-- `Finset.filter`, `Finset.card`, ..., and gives the notation `F[X]`.
open Finset Polynomial

-- All names defined below get the prefix `BEEP.Affine.` (e.g.
-- `BEEP.Affine.Setup.affine_main_delta`). The namespace is closed by `end BEEP.Affine` at the end
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

namespace Setup

-- `R` is the data of Section 5.1. Every definition and theorem below that mentions `R` takes it as
-- its first explicit argument, written with a dot: `R.affineFold`, `R.IsPretender`, ...
variable (R : Setup F ι)

/-! ### Theorem 5.3, as stated in the paper -/

section WithDelta

-- In this section `u₁ u₂` are the words and `m` is the number of samples.
variable (u₁ u₂ : ι → F) {m : ℕ}

/-- **Theorem 5.3, as stated in the paper.** Let `δ ≥ 0` (the paper takes `δ ∈ (0, 1)`), let
`ℓ + 1 ≤ n`, and let `C⁺` be `(δ, L)`-list decodable. Let `N = max(q, (δ n + 2)(δ n + 1)/2)`. Then for
every integer `t ≥ N + 1` and `z` uniform in `F^m`,
`Pr[|A_z| ≥ t] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`, where `A_z` is defined with agreement
sets of size at least `(1 - δ) n` (`s = ⌈(1 - δ) n⌉`; see `isPretender_ceil_iff` in
`BEEP/Affine/Proof.lean`). -/
theorem affine_main_delta {δ : ℝ} (hδ : 0 ≤ δ) (L t : ℕ) (hn : R.ℓ + 1 ≤ Fintype.card ι)
    (hL : ∀ w : ι → F, ((R.rsWords (R.ℓ + 1)).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card ι).card ≤ L)
    (ht : max (Fintype.card F : ℝ)
        ((δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2) + 1 ≤ t) :
    ((univ.filter fun z : Fin m → F =>
        t ≤ R.maxHits u₁ u₂ ⌈(1 - δ) * Fintype.card ι⌉₊ z).card : ℝ) /
        (Fintype.card F : ℝ) ^ m ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * (((R.ℓ : ℝ) + 1) / Fintype.card F) ^ m /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) - max (Fintype.card F : ℝ)
          ((δ * Fintype.card ι + 2) * (δ * Fintype.card ι + 1) / 2))) :=
  R.affine_main_delta_proof u₁ u₂ hδ L t hn hL ht

end WithDelta

/-! ### Variants: the integer agreement threshold `s` of the definitions -/

section Counting

-- The words, the threshold, the number `m` of samples, and the prover's answers `B`: for every
-- `z ∈ F^m` a pair `B z = (b₁, b₂)`. The answers may depend on `z` in any way. Theorem 5.3 takes
-- the answers that maximize the number of DEEP-MCA-bad challenges (`maxHits` of `Defs.lean`).
variable (u₁ u₂ : ι → F) (s : ℕ) {m : ℕ} (B : (Fin m → F) → (Fin m → F) × (Fin m → F))

/-- **Theorem 5.3, with the agreement threshold `s`.** Let `N = max(q, (n - s + 2)(n - s + 1)/2)`,
and let `C⁺` be list decodable with list size `L` at agreement `s`. Then for every integer
`t ≥ N + 1` and `z` uniform in `F^m`,
`Pr[|A_z| ≥ t] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`, where `|A_z|` is the largest number
of DEEP-MCA-bad challenges at `z` over all answers `b₁, b₂`. -/
theorem affine_main (L t : ℕ) (hL : R.ListDecodable s L)
    (ht : max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) + 1 ≤
      t) :
    ((univ.filter fun z : Fin m → F => t ≤ R.maxHits u₁ u₂ s z).card : ℝ) /
        (Fintype.card F : ℝ) ^ m ≤
      ((Fintype.card F : ℝ) ^ 2 * L) ^ 3 * (((R.ℓ : ℝ) + 1) / Fintype.card F) ^ m /
        ((t : ℝ) * ((t : ℝ) - 1) * ((t : ℝ) -
          ((max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2) :
            ℕ) : ℝ))) :=
  R.affine_main_proof u₁ u₂ s L t hL ht

/-- **Theorem 5.3, counting form.** For every `t`,
`t (t - 1) (t - N) · #{z ∈ F^m | |A_z| ≥ t} ≤ (q² L)³ (ℓ + 1)^m`, where
`N = max(q, (n - s + 2)(n - s + 1)/2)` and `|A_z|` is the largest number of DEEP-MCA-bad
challenges at `z` over all answers. The subtractions are those of `ℕ`, so for `t ≤ N` the
left-hand side is `0`. -/
theorem affine_main_nat (L t : ℕ) (hL : R.ListDecodable s L) :
    t * (t - 1) *
        (t - max (Fintype.card F) ((Fintype.card ι - s + 2) * (Fintype.card ι - s + 1) / 2)) *
        (univ.filter fun z : Fin m → F => t ≤ R.maxHits u₁ u₂ s z).card ≤
      (Fintype.card F ^ 2 * L) ^ 3 * (R.ℓ + 1) ^ m :=
  R.affine_main_nat_proof u₁ u₂ s L t hL

/-- **How Theorem 5.3 is used (the fold challenge).** If `|A_z| < t`, then whatever the answers `B`
to `z`, a uniform challenge `α ∈ F × F` is DEEP-MCA-bad with probability at most `(t - 1)/q²`. This
is the error of the fold challenge that follows the samples in a protocol that uses Theorem 5.3. -/
theorem fold_challenge_le (z : Fin m → F) (t : ℕ) (hz : R.maxHits u₁ u₂ s z < t) :
    ((univ.filter fun α : F × F => R.DeepBad u₁ u₂ s z (B z) α).card : ℝ) /
        (Fintype.card (F × F) : ℝ) ≤ ((t : ℝ) - 1) / (Fintype.card F : ℝ) ^ 2 :=
  R.fold_challenge_le_proof u₁ u₂ s B z t hz

end Counting

end Setup

end BEEP.Affine
