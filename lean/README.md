<!-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request ("Write a Lean formalization of Theorem 30 in the BEEP paper. Use the same formatting (with lots of comments) as you did when formalizing the result in the folder deep improvement"): this README, BEEP/AffineMain.lean, BEEP.lean, check.sh, lakefile.toml and lean-toolchain; please review] -->
<!-- [AI-revised (claude-opus-5-5), 2026-11-16, at the author's request ("Create a new repository called BEEP ... It should contain ... Lean formalizations of Theorems 3.4 and Theorem 5.3"; then "If a lean implementation is missing, leave it out. We will work on it later"): the folder is copied from typst/lean of the repository random-domain-ligerito to lean/ of the repository BEEP; the paper's numbers are those of its current numbering within sections (Theorem 30 is now Theorem 5.3, Lemma 33 is Lemma 5.5, Definitions 28, 29 and 32 are Definitions 5.1, 5.2 and 5.4), the labels are the current ones, the paths are those of the new repository, the section "Status" is new, and the record of the check is that of the copy; please review] -->

# Lean formalization of Theorem 5.3 of the BEEP paper

`BEEP/AffineMain.lean` formalizes Theorem 5.3 of the BEEP paper (`../typst/deep+.typ`, Section 5,
"BEEP with affine folding for Reed-Solomon codes", label `t:affine_main_0`) together with the lemma
behind it, Lemma 5.5 (label `l:few_bad_points_on_line_0`). The numbers are those of the PDF compiled
from `../typst/deep+.typ` on November 16, 2026, which numbers its results within sections; the
labels are the stable names. It is written in Lean 4 with Mathlib v4.30.0, in the style of
`2-deep-fold-lemma/lean/DeepFold/Lemma1.lean` of the repository `random-domain-ligerito` (the
formalization of Lemma 1 of the "deep improvement" note): a reading guide for newcomers to Lean at
the top, and a comment before almost every line of every proof. It has no `sorry`, and all its
theorems depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Status

| paper | Lean |
|---|---|
| Theorem 5.3 and Lemma 5.5 (affine folds, Reed-Solomon codes) | formalized here, `BEEP/AffineMain.lean` |
| Theorem 3.4 (the main theorem, any linear code, any zero evader) | not yet formalized |

For Theorem 3.4, the closest formalization is that of Lemma 1 of the "deep improvement" note
(`2-deep-fold-lemma/lean/DeepFold/Lemma1.lean` of the repository `random-domain-ligerito`, the
theorem `lemma1_rbr_max_gen`). Its bound has the same form, but it is for the weights `(1, α)` only and for a
zero evader made of `m` independent samples of a scalar family (error `σ^m`), where Theorem 3.4
allows any weights `λ₁, λ₂` with `a₁ d₂ ≠ a₂ d₁` and any zero evader. It is not part of this
repository.

## The main theorems

| paper | Lean (namespace `BEEP.Setup`) |
|---|---|
| Lemma 5.5, second case of the proof (a line of `C_λ^{≡2}`) | `affine_line_pairs` |
| Lemma 5.5 | `affine_line` |
| Theorem 5.3, for given answers (counting form, probability form) | `affine_main_gen_nat`, `affine_main_gen` |
| Theorem 5.3, with `A_z` maximal over the answers `b₁, b₂` | `affine_main_nat`, `affine_main` |
| Theorem 5.3 as stated, with `δ` and the relative Hamming distance | `affine_main_delta` |
| if `|A_z| < t`, a uniform challenge is DEEP-MCA-bad with probability at most `(t - 1)/|F|²` | `fold_challenge_le` |

`affine_main` reads: let `N = max(q, (n - s + 2)(n - s + 1)/2)` and let `C⁺ = RS_{ℓ+1}` be list
decodable with list size `L` at agreement `s`; then for every integer `t ≥ N + 1`, for `z` uniform in
`F^m`, `Pr[|A_z| ≥ t] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`, where `q = |F|`, `n` is the block
length, and `|A_z|` is the largest number of DEEP-MCA-bad challenges at `z` over all answers. The
module documentation at the top of the file has a dictionary between the paper and the Lean names.

`fold_challenge_le` is the error of the fold challenge that follows the samples in a protocol that
uses Theorem 5.3. The paper describes no such protocol for affine folds (Section 5 says why), and
none is formalized here.

## How the formalization differs from the paper's presentation

None of these changes the content of Theorem 5.3; the last section of the file (`WithDelta`) turns
the theorem back into the paper's form.

1. **Agreement threshold.** As in `DeepFold/Lemma1.lean`, the file uses an integer agreement
   threshold `s` (agreement sets of size at least `s`) in place of `(1 - δ) n`, so that `δ n` becomes
   `n - s`. `affine_main_delta` takes `s = ⌈(1 - δ) n⌉`, for which the pretenders are exactly those of
   Definition 5.1 (`isPretender_ceil_iff`), and its `N` is the paper's
   `max(|F|, (δn + 2)(δn + 1)/2)`. The `N` of the integer form is at most that one, so the integer
   form is slightly stronger.
2. **Codewords are polynomials**, as in Section 5.1 of the paper: `RS_e` is Mathlib's `degreeLT F e`.
   The list decodability `ListDecodable` therefore counts polynomials of degree at most `ℓ`; this is
   the same as counting codewords when `ℓ + 1 ≤ n` (`card_close_rsWords`). `affine_main_delta`
   assumes `ℓ + 1 ≤ n` and counts codewords, with the relative Hamming distance.
3. **Challenges are pairs** `(σ, τ) ∈ F × F`, with the polynomial `chal (σ, τ) = σ + τ X`.
4. **Lines with rational coefficients** (Definition 5.4) are written with a common denominator:
   `θ(α) = P/D + α · Q/D` with polynomials `D ≠ 0`, `P`, `Q`, and "`c` lies on the line at `α`" is
   `D c = P + α Q`. This way the whole file stays with polynomials (no `RatFunc`).
5. **Answers.** The prover's answers are a function `B` from `z` to `(b₁, b₂)`. Theorem 5.3 is about
   `maxHits`, the largest number of DEEP-MCA-bad challenges over all answers to `z`, and a single
   worst-case `B` attains it at every `z` (`exists_worst_answers`).
6. **Standing assumptions.** `ℓ ≥ 1` and `ℓ + 2 ≤ n` (Section 5.1) are not needed for the integer
   form; `affine_main_delta` uses `ℓ + 1 ≤ n` (to identify codewords with polynomials) and `δ ≥ 0`.

The proof follows the paper step by step: `affine_line` (Lemma 5.5, with the pigeonhole argument of
its first case and the count of pairs of positions of its second case, `pair_count_arith` being the
final arithmetic); `onLine_of_defect_eq_zero` and `defect_eq_zero_of_onLine` (first step: three
tuples on one line iff `U = 0`); `eval_defect_eq_zero` (second step: `φ_z(U) = 0` for consistent
tuples, using that evaluation is multiplicative); `card_collinear_le`, `card_goodTriples`,
`card_goodTriples_le` (third step: `|A_z| (|A_z| - 1) (|A_z| - N) ≤ |T_z|`, the analogue of
Lemma 3.10); `card_pretPts` and `sum_card_consTriples` (last step: `|P| ≤ |F|² L`, and a nonzero `U`
of degree at most `ℓ + 1` has at most `ℓ + 1` roots in each coordinate of `z`). The structure is that
of `DeepFold/Lemma1.lean` (Claim 1 there corresponds to `affine_line_pairs` here, Claim 3 to
`card_goodTriples`), but the file does not import it: the objects differ (polynomials, challenges in
`F × F`).

Not formalized: Remarks 5.6 and 5.7.

## Checking it

All the checks in one go (it writes only a scratch file in `$TMPDIR`, and refuses to run while a
benchmark campaign holds `/tmp/bitz-bench.lock`):

    ~/BEEP/lean/check.sh

It passes `-DautoImplicit=false -DrelaxedAutoImplicit=false`, the options of `lakefile.toml`, to every
`lean` call, type-checks `BEEP/AffineMain.lean`, and then checks a scratch file made of the file and a
few examples: a `Setup` over `ZMod 5` with the weights `(1, α)` and one with the weights `(1 - α, α)`
of Section 4, `affine_main` applied to both and `affine_main_delta` (with `δ = 1/4`) to the second,
every hypothesis proved, with the trivial list size (so the hypotheses can be met; with that list
size the bounds exceed 1, so the examples show that the theorems apply, not a useful bound). It
prints the axioms of 14 theorems.

On November 14, 2026, in the repository `random-domain-ligerito`, with the file at `shasum`
`a86a02cd3f4d927cf6165255c1885f186b23052d`, Lean printed nothing but the axioms, every theorem
depending on `[propext, Classical.choice, Quot.sound]`. The same day, a separate agent read the
definitions and statements against Section 5 of the paper (without the reasoning that produced
them) and found no mismatch; the Lean statements are the paper's, or slightly stronger (item 1 of
the list above). On November 16, 2026, the copy in this repository, whose comments cite the
paper's current numbers (only comments differ from the file above), at `shasum`
`aa578a3d2c2525706bd756ba97a699020d8e761d`, gave the same output in about 32 s.

By hand, with the Mathlib build of `~/math in lean` (same version, v4.30.0):

    cd "$HOME/math in lean" && lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
      ~/BEEP/lean/BEEP/AffineMain.lean

No output means that the file type-checks. The root file `BEEP.lean` only imports
`BEEP/AffineMain.lean`, which is not on the search path of `~/math in lean`, so there we check the
file directly.

As a standalone project (downloads and unpacks Mathlib v4.30.0, several GB; not tested):

    cd ~/BEEP/lean && lake exe cache get && lake build
