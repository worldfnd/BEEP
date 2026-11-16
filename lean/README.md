<!-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request ("Write a Lean formalization of Theorem 30 in the BEEP paper. Use the same formatting (with lots of comments) as you did when formalizing the result in the folder deep improvement"): this README, BEEP/AffineMain.lean, BEEP.lean, check.sh, lakefile.toml and lean-toolchain; please review] -->
<!-- [AI-revised (claude-opus-5-5), 2026-11-16, at the author's request ("Create a new repository called BEEP ... It should contain ... Lean formalizations of Theorems 3.4 and Theorem 5.3"; then "If a lean implementation is missing, leave it out. We will work on it later"): the folder is copied from typst/lean of the repository random-domain-ligerito to lean/ of the repository BEEP; the paper's numbers are those of its current numbering within sections (Theorem 30 is now Theorem 5.3, Lemma 33 is Lemma 5.5, Definitions 28, 29 and 32 are Definitions 5.1, 5.2 and 5.4), the labels are the current ones, the paths are those of the new repository, the section "Status" is new, and the record of the check is that of the copy; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request ("Let's add a lean formalization of theorem 3.4"): BEEP/MainTheorem.lean is new, and this README describes both files. New: the table at the top (in place of the section "Status"), the section "Theorem 3.4" and the section "Checking them". The section "Theorem 5.3" is the previous text of this README, with its headings one level down; please review] -->

# Lean formalizations of Theorems 3.4 and 5.3 of the BEEP paper

Two files, in Lean 4 with Mathlib v4.30.0. They do not depend on each other.

| paper (`../paper/main.typ`) | file | namespace |
|---|---|---|
| Theorem 3.4 (label `t:main_thm`), with Lemmas 3.7 to 3.10 of its proof | `BEEP/MainTheorem.lean` | `BEEP.Main` |
| Theorem 5.3 (label `t:affine_main_0`), with Lemma 5.5 (`l:few_bad_points_on_line_0`) | `BEEP/AffineMain.lean` | `BEEP` |

The numbers are those of the PDF compiled from `../paper/main.typ` on November 16, 2026, which
numbers its results within sections; the labels are the stable names. Both files are written in the
style of `2-deep-fold-lemma/lean/DeepFold/Lemma1.lean` of the repository `random-domain-ligerito`
(the formalization of Lemma 1 of the "deep improvement" note, which is not part of this
repository): a reading guide for newcomers to Lean at the top, and a comment before almost every
line of every proof. They have no `sorry`, and all their theorems depend only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Theorem 3.4: `BEEP/MainTheorem.lean`

Theorem 3.4 is the main theorem of the paper, for any linear code, any weights `λ₁, λ₂` with
`a₁ d₂ ≠ a₂ d₁` and any zero evader. (Lemma 1 of the "deep improvement" note, formalized in
`DeepFold/Lemma1.lean`, is the case of the weights `(1, α)` and of a zero evader made of `m`
independent samples of a scalar family.)

### The main theorems

| paper | Lean (namespace `BEEP.Main.Setup`, unless the full name is given) |
|---|---|
| Lemma 3.7 (a parameterized line contains few pretenders) | `few_pretenders_on_line` |
| Lemma 3.8 (colinearity of codewords) | `BEEP.Main.defect_eq_zero_iff` |
| Lemma 3.9 (`U` vanishes under `φ_z` for consistent tuples) | `evader_defect_eq_zero` |
| Lemma 3.10 (`|A_z| (|A_z| - 1) (|A_z| - δn - 1) ≤ |T_z|`) | `third_moment_bound` |
| Theorem 3.4, for given answers (counting form, probability form) | `main_thm_gen_nat`, `main_thm_gen` |
| Theorem 3.4, with `A_z` maximal over the answers `b₁, b₂` | `main_thm_nat`, `main_thm` |
| Theorem 3.4 as stated, with `δ` and the relative Hamming distance | `main_thm_delta` (integer `t`), `main_thm_delta_real` (real `t`) |
| the same with `⌊δ n⌋` in place of `δ n`, for every integer `t ≥ ⌊δ n⌋ + 2` | `main_thm_delta_floor` |
| if `|A_z| < t`, a uniform challenge is DEEP-MCA-bad with probability at most `(t - 1)/|F|` | `fold_challenge_le` |

`main_thm_delta` reads: let `δ ≥ 0`, let `C` be `(δ, L)`-list decodable (every word has at most `L`
codewords at relative Hamming distance at most `δ`), and let `ε` be an error bound of the zero
evader; then for every integer `t ≥ δ n + 2`, for `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (|F| L)³ ε / (t (t - 1) (t - δ n - 1))`, where `n` is the block length and `|A_z|`
is the largest number of DEEP-MCA-bad elements at `z` over all answers `b₁, b₂`, defined with
agreement sets of size at least `(1 - δ) n`. The module documentation at the top of the file has a
dictionary between the paper and the Lean names.

`main_thm_delta_floor` is slightly stronger than the theorem as stated when `δ n` is not an
integer: its bound is smaller, and it covers the threshold `t = ⌊δ n⌋ + 2`, which is the least
integer `t` for which "not `|A_z| ≥ t`" gives `|A_z| ≤ δ n + 1`. (The notions of Section 3 depend
on `δ` only through `⌊δ n⌋`. The proof of Theorem 4.3 takes `t = δ n + 2` and then uses
`|A_z| ≤ δ n + 1` for the other `z`, which is this threshold; so for a `δ n` that is not an integer
it is `main_thm_delta_floor` that applies there, with `(⌊δ n⌋ + 2)(⌊δ n⌋ + 1)` where the theorem
has `(δ n + 2)(δ n + 1)`.)

`fold_challenge_le` is the error of the fold challenge that follows the samples in a protocol that
uses Theorem 3.4: with `t = ⌊δ n⌋ + 2` it gives `(⌊δ n⌋ + 1)/|F|`, which is at most the term
`(δ n + 1)/|F|` of the error `κ₂` of Theorem 4.3, and equal to it when `δ n` is an integer.
Theorem 4.3 is not formalized here.

### How the formalization differs from the paper's presentation

None of these changes the content of Theorem 3.4; the last section of the file (`WithDelta`) turns
the theorem back into the paper's form.

1. **Agreement threshold.** As in `BEEP/AffineMain.lean`, the file uses an integer agreement
   threshold `s` (agreement sets of size at least `s`) in place of `(1 - δ) n`, so that `δ n` becomes
   `n - s`: the bound of Lemma 3.7 is `n - s + 1`, and Theorem 3.4 is for `t ≥ n - s + 2`.
   `main_thm_delta` takes `s = ⌈(1 - δ) n⌉`, for which the MCA property and the pretenders are
   exactly those of the paper (`satisfiesMCA_ceil_iff`, `isPretender_ceil_iff`). For
   `0 ≤ δ ≤ 1`, `n - s = ⌊δ n⌋` (and `n - s ≤ ⌊δ n⌋ ≤ δ n` for every `δ ≥ 0`), so the integer form
   is slightly stronger when `δ n` is not an integer; `main_thm_delta_floor` is that form, written
   with `δ`.
2. **Codewords are messages.** The code is given by its injective linear encoding map
   `Enc_C : F^ℓ → F^n` (Section 2.2), the field `enc` of `Setup`, and a codeword is represented by
   its message: `c : Fin R.ℓ → F` stands for the codeword with entries `R.enc c i`. The paper does
   the same when it applies the zero evader to a codeword (`φ_z(Enc_C(w)) := φ_z(w)`). The list
   decodability `ListDecodable` therefore counts messages, which is the same as counting codewords
   since the encoding map is injective (`card_filter_codewords`); `main_thm_delta` counts
   codewords, with the relative Hamming distance. The injectivity is used nowhere else.
3. **The zero evader.** It is the field `φ` of `Setup`: a linear map `F^ℓ → F^m` for every `z` in a
   finite type `Z`. `IsErrorBound ε` is Definition 2.3: `ε ≥ 0`, and every nonzero `v` has
   `Pr_z[φ_z(v) = 0] ≤ ε` (the bound `ε ≤ 1` of the paper is not needed). The counting forms take
   instead a natural number `M` such that every nonzero `v` has `φ_z(v) = 0` for at most `M` of
   the `z`. The theorems that speak of a probability assume that `Z` is nonempty.
4. **Answers.** The prover's answers are a function `B` from `z` to `(b₁, b₂)`. Theorem 3.4 is about
   `maxHits`, the largest number of DEEP-MCA-bad elements over all answers to `z`, and a single
   worst-case `B` attains it at every `z` (`exists_worst_answers`).
5. **MCA-bad elements.** Definition 3.1 is `MCABad` (the negation of the MCA property,
   `SatisfiesMCA`). Definition 3.2 and the set `A_θ^pret` of Lemma 3.7 are stated without the
   condition "`α` is MCA-bad", which follows from the existence of an `α`-pretender
   (`mcaBad_iff_exists_pretender`).
6. **Hypotheses that are not needed.** Lemma 3.8 only needs `α₁ ≠ α₂` (the paper takes the three
   `α_i` pairwise distinct). That `n` is a power of two, that `δ < 1` and that `L ≥ 1` are not
   used.
7. **The threshold `t`.** It is a natural number in `main_thm_delta`, as in Theorem 5.3;
   `main_thm_delta_real` is the same statement for a real `t ≥ δ n + 2`.

The proof follows the paper step by step: `exists_weights_form` and `eq_zero_of_two_folds` (the
first sentence and the "linearly independent" step of the proof of Lemma 3.7), then
`few_pretenders_on_line`; `line_fst`, `line_snd`, `onLine_of_defect_eq_zero` and
`defect_eq_zero_of_onLine` (the line through two tuples, and the two directions of Lemma 3.8);
`evader_defect_eq_zero` (Lemma 3.9, by the linearity of `φ_z`); `card_collinear_le`,
`card_goodTriples` and `card_goodTriples_le` (Lemma 3.10); `card_pretPts` (`|P| ≤ |F| L`) and
`sum_card_consTriples` (the double count `∑_z |T_z| ≤ |P|³ M`). Two points of the paper's proof
that the formalization settles: in Lemma 3.10 the count needs no correction for `α₃ ∉ {α₁, α₂}`
(the line through the chosen points at `α₁` and `α₂` contains these two points among its at most
`δ n + 1` pretender points, so at least `|A_z| - δ n - 1` of the others are off it); and the
hypothesis `t ≥ δ n + 2` is used only to divide by `t (t - 1) (t - δ n - 1)`, which it makes
positive (the counting forms hold for every `t`).

Not formalized: Remark 3.5; Section 4 (Constructions 4.1 and 4.4, Theorems 4.3 and 4.5); the error
bounds of the univariate and multilinear evaders (Lemmas 2.6 and 2.9; the examples of `check.sh`
prove the case of one sample of the univariate evader over `ZMod 5`).

## Theorem 5.3: `BEEP/AffineMain.lean`

`BEEP/AffineMain.lean` formalizes Theorem 5.3 of the paper (Section 5, "BEEP with affine folding for
Reed-Solomon codes") together with the lemma behind it, Lemma 5.5.

### The main theorems

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

### How the formalization differs from the paper's presentation

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
of `BEEP/MainTheorem.lean` (`few_pretenders_on_line` there corresponds to `affine_line_pairs` here),
but neither file imports the other: the objects differ (polynomials, challenges in `F × F`).

Not formalized: Remarks 5.6 and 5.7.

## Checking them

All the checks in one go (it writes only to the scratch folder `$TMPDIR/beep-lean-check`, and
refuses to run while a benchmark campaign holds `/tmp/bitz-bench.lock`):

    ~/BEEP/lean/check.sh

It passes `-DautoImplicit=false -DrelaxedAutoImplicit=false`, the options of `lakefile.toml`, to every
`lean` call. It type-checks the two files and compiles them into the scratch folder; type-checks
the root file `BEEP.lean`, which imports both; and then checks two files of examples, which
import the compiled files, and prints the axioms of 14 theorems of `BEEP/AffineMain.lean` and of
21 of `BEEP/MainTheorem.lean` (with its examples).

- **Examples for `BEEP/AffineMain.lean`**: a `Setup` over `ZMod 5` with the weights `(1, α)` and one
  with the weights `(1 - α, α)` of Section 4, `affine_main` applied to both and `affine_main_delta`
  (with `δ = 1/4`) to the second, every hypothesis proved, with the trivial list size.
- **Examples for `BEEP/MainTheorem.lean`**: the Reed-Solomon code of dimension 2 on four points of
  `ZMod 5` (with a proof that its encoding map is injective), the univariate zero evader with one
  sample and a proof that `1/5` is an error bound of it, the weights `(1, α)` and `(1 - α, α)`;
  `main_thm` applied to both setups, `main_thm_delta` and `main_thm_delta_real` (with `δ = 1/4`)
  to the second, and `main_thm_delta_floor` with `δ = 3/10` (so `δ n = 1.2` is not an integer and
  `t = 3` is allowed), every hypothesis proved, with the trivial list size. And a concrete
  case in which the definitions are inhabited: for `u₁ = (0, 0, 1, 0)`, `u₂ = (0, 0, -1, 0)` and
  `s = 3`, the zero codeword is a `1`-pretender, and `α = 1` is a DEEP-MCA-bad element at every `z`.

With the trivial list size the bounds exceed 1, so the examples show that the hypotheses can be
met and that the theorems apply, not a useful bound.

The record of the checks:

- On November 14, 2026, in the repository `random-domain-ligerito`, with `BEEP/AffineMain.lean` at
  `shasum` `a86a02cd3f4d927cf6165255c1885f186b23052d`, Lean printed nothing but the axioms, every
  theorem depending on `[propext, Classical.choice, Quot.sound]`. The same day, a separate agent read
  its definitions and statements against Section 5 of the paper (without the reasoning that
  produced them) and found no mismatch; the Lean statements are the paper's, or slightly stronger.
- On November 16, 2026, in this repository, with `BEEP/AffineMain.lean` at `shasum`
  `aa578a3d2c2525706bd756ba97a699020d8e761d` (only comments differ from the file above: they cite the
  paper's current numbers), the script printed nothing but the axioms. The same day the paper
  became `../paper/main.typ` (it was `typst/deep+.typ`) and `BEEP/MainTheorem.lean` was written.
  With `BEEP/AffineMain.lean` at `shasum` `d484d8253b6ac000e52677b2908441d8ecb4984c` (again only
  comments differ: the new path of the paper) and `BEEP/MainTheorem.lean` at `shasum`
  `0ba955d0d4475ef15d80f14e3d6e70e315d7ce8c`, Lean printed nothing but the axioms, every theorem
  depending on `[propext, Classical.choice, Quot.sound]`, and the script took 35 to 65 s, with the
  machine short of memory.
- The same day, a separate agent read the definitions and statements of `BEEP/MainTheorem.lean`
  against Sections 2.2, 2.3 and 3 of the paper (without the reasoning that produced them; the file
  was at `shasum` `370fff12ea96969b6249e9ffa3740017afa14057`) and found no mismatch: every Lean
  statement is the paper's, or slightly stronger, and `main_thm_delta` is Theorem 3.4 as stated,
  with the paper's hypotheses or weaker ones. Its three remarks on the comments were applied.
  Added after that review, and so not read by it: `satisfiesMCA_ceil_iff`, `card_sub_ceil_le` and
  `main_thm_delta_floor` (the last one after its remark that the paper uses `δ n` as an integer).
  No definition or statement that it read was changed.

By hand, with the Mathlib build of `~/math in lean` (same version, v4.30.0), one file at a time:

    cd "$HOME/math in lean" && lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
      ~/BEEP/lean/BEEP/MainTheorem.lean

No output means that the file type-checks. The root file `BEEP.lean` imports the two files, which
are not on the search path of `~/math in lean`; `check.sh` compiles them into its scratch folder
first and puts that folder on the search path.

As a standalone project (downloads and unpacks Mathlib v4.30.0, several GB; not tested):

    cd ~/BEEP/lean && lake exe cache get && lake build
