<!-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request: this README and the formalization of Theorem 5.3 (then Theorem 30), with BEEP.lean, check.sh, lakefile.toml and lean-toolchain; please review] -->
<!-- [AI-revised (claude-opus-5-5), 2026-11-16, at the author's request: the folder is copied from typst/lean of the repository random-domain-ligerito to lean/ of the repository BEEP; the paper's numbers are those of its numbering within sections (Theorem 30 is now Theorem 5.3, Lemma 33 is Lemma 5.5, Definitions 28, 29 and 32 are Definitions 5.1, 5.2 and 5.4), and the paths are those of the new repository; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request: the formalization of Theorem 3.4 is new, and this README describes both; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: each formalization is now a folder of three files (definitions, statements, proofs), so that knowing what is proved only takes reading the definitions and the statements. This README is reorganized accordingly: the first section is new, each of the two sections on a theorem now has a part for each file, and the paper's numbers are those of November 17 (Definition 2.2, Lemmas 2.5 and 2.8, Construction 4.5, Theorem 4.6, Remark 5.6). The sections on the differences with the paper and the earlier records of the checks are the previous text; please review] -->

# Lean formalizations of Theorems 3.4 and 5.3 of the BEEP paper

Lean 4 with Mathlib v4.30.0. There is one folder for each theorem, and the two folders do not
depend on each other.

| paper (`../paper/main.typ`) | folder | namespace |
|---|---|---|
| Theorem 3.4 (label `t:main_thm`): folding challenges in `F`, any linear code | `BEEP/Scalar` | `BEEP.Scalar` |
| Theorem 5.3 (label `t:affine_main_0`): folding challenges `σ + τ X`, Reed-Solomon codes | `BEEP/Affine` | `BEEP.Affine` |

## What to read

Each folder has the same three files:

| file | contents |
|---|---|
| `Defs.lean` | the definitions that the statement of the theorem uses; no lemma and no proof |
| `Theorem.lean` | the statement of the theorem, as in the paper and in a few variants; every proof is one line, which calls a theorem of `Proof.lean` |
| `Proof.lean` | the lemmas of the paper's proof, the definitions that only the proof uses, and the proofs |

**To know what is proved, read `Defs.lean` and then `Theorem.lean`.** There is no need to read
`Proof.lean`, for three reasons, which `check.sh` checks:

- Lean accepts `Theorem.lean` only if every statement in it is proved;
- these statements mention only declarations of `Defs.lean` and of Mathlib, and `Defs.lean`
  imports Mathlib only;
- `Proof.lean` contains definitions and theorems only (no notation, no instance, no attribute, no
  axiom), so it cannot change how a statement of `Theorem.lean` is read.

In `Theorem.lean` the first theorem is the one of the paper (`main_thm_delta` in `BEEP/Scalar`,
`affine_main_delta` in `BEEP/Affine`); the others are variants of it. In `Proof.lean` the proof of
a theorem `x` of `Theorem.lean` is the theorem `x_proof`, which has the same statement.

The numbers are those of the PDF compiled from `../paper/main.typ` on November 17, 2026, which
numbers its results within sections; the labels are the stable names. The files are written in the
style of `2-deep-fold-lemma/lean/DeepFold/Lemma1.lean` of the repository `random-domain-ligerito`
(the formalization of Lemma 1 of the "deep improvement" note, which is not part of this
repository): a reading guide for newcomers to Lean (the notation in `Defs.lean`, the tactics in
`Proof.lean`), and a comment before almost every line of every proof. They have no `sorry`, and
all their theorems depend only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

Since November 17, 2026 the paper writes `θ₁(α)`, `θ₂(α)` for the weights of the fold, which the
Lean names (`lam₁`, `lam₂`) and the comments of the files call `λ₁(α)`, `λ₂(α)`. In the comments,
`θ` is always a parameterized line.

## Theorem 3.4: `BEEP/Scalar`

Theorem 3.4 is the main theorem of the paper, for any linear code, any weights `λ₁, λ₂` with
`a₁ d₂ ≠ a₂ d₁` and any zero evader. (Lemma 1 of the "deep improvement" note, formalized in
`DeepFold/Lemma1.lean`, is the case of the weights `(1, α)` and of a zero evader made of `m`
independent samples of a scalar family.)

### The statements: `BEEP/Scalar/Theorem.lean`

| paper | Lean (namespace `BEEP.Scalar.Setup`) |
|---|---|
| Theorem 3.4 as stated, with `δ` and the relative Hamming distance | `main_thm_delta` (integer `t`), `main_thm_delta_real` (real `t`) |
| the same with `⌊δ n⌋` in place of `δ n`, for every integer `t ≥ ⌊δ n⌋ + 2` | `main_thm_delta_floor` |
| Theorem 3.4 with the integer agreement threshold `s` of the definitions (probability form, counting form) | `main_thm`, `main_thm_nat` |
| if `|A_z| < t`, a uniform challenge is DEEP-MCA-bad with probability at most `(t - 1)/|F|` | `fold_challenge_le` |

`main_thm_delta` reads: let `δ ≥ 0`, let `C` be `(δ, L)`-list decodable (every word has at most `L`
codewords at relative Hamming distance at most `δ`), and let `ε` be an error bound of the zero
evader; then for every integer `t ≥ δ n + 2`, for `z` uniform in `Z`,
`Pr[|A_z| ≥ t] ≤ (|F| L)³ ε / (t (t - 1) (t - δ n - 1))`, where `n` is the block length and `|A_z|`
is the largest number of DEEP-MCA-bad elements at `z` over all answers `b₁, b₂`, defined with
agreement sets of size at least `(1 - δ) n`.

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

Not in the Lean statements: the last sentence of Theorem 3.4, which the paper has since November
17, 2026 ("Moreover, if `C` has `δ`-MCA error `ε_MCA` then the factor `(|F| L)³` can be replaced by
`(ε_MCA |F| L)³`"). The statements have the factor `(|F| L)³`.

### The definitions: `BEEP/Scalar/Defs.lean`

| paper | Lean (namespace `BEEP.Scalar.Setup`, unless the full name is given) |
|---|---|
| the code through its encoding map, the weights of the fold, the zero evader (Sections 2.2, 2.3, 3.1) | the structure `BEEP.Scalar.Setup` |
| the weights and the fold | `lam₁`, `lam₂`, `fold` |
| Correlated Agreement over `S`; the MCA property; MCA-bad element (Definition 3.1) | `CA`, `SatisfiesMCA`, `MCABad` |
| `α`-pretender (Definition 3.2) | `IsPretender` |
| consistency and DEEP-MCA-bad element (Definition 3.3) | `Consistent`, `DeepBad` |
| list decodability, with the integer agreement threshold | `ListDecodable` |
| error bound of the zero evader (Definition 2.2) | `IsErrorBound` |
| `A_{z, b₁, b₂}` and `|A_z|` | `hits`, `maxHits` |
| the code as a set of words | `codewords` |

The module documentation of the file has the setting and the full dictionary between the paper
and the Lean names.

### The lemmas and the proofs: `BEEP/Scalar/Proof.lean`

| paper | Lean (namespace `BEEP.Scalar.Setup`, unless the full name is given) |
|---|---|
| Lemma 3.7 (a parameterized line contains few pretenders) | `few_pretenders_on_line` |
| Lemma 3.8 (colinearity of codewords) | `BEEP.Scalar.defect_eq_zero_iff` |
| Lemma 3.9 (`U` vanishes under `φ_z` for consistent tuples) | `evader_defect_eq_zero` |
| Lemma 3.10 (`|A_z| (|A_z| - 1) (|A_z| - δn - 1) ≤ |T_z|`) | `third_moment_bound` |
| Theorem 3.4, for given answers (counting form, probability form) | `main_thm_gen_nat`, `main_thm_gen` |
| the proofs of the six theorems of `Theorem.lean` | `main_thm_delta_proof`, `main_thm_delta_real_proof`, `main_thm_delta_floor_proof`, `main_thm_proof`, `main_thm_nat_proof`, `fold_challenge_le_proof` |

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

### How the formalization differs from the paper's presentation

None of these changes the content of Theorem 3.4; the theorems with `δ` of `Theorem.lean` are in
the paper's form.

1. **Agreement threshold.** As in `BEEP/Affine`, the definitions use an integer agreement
   threshold `s` (agreement sets of size at least `s`) in place of `(1 - δ) n`, so that `δ n` becomes
   `n - s`: the bound of Lemma 3.7 is `n - s + 1`, and Theorem 3.4 is for `t ≥ n - s + 2`.
   `main_thm_delta` takes `s = ⌈(1 - δ) n⌉`, for which the MCA property and the pretenders are
   exactly those of the paper (`satisfiesMCA_ceil_iff`, `isPretender_ceil_iff` in `Proof.lean`).
   For `0 ≤ δ ≤ 1`, `n - s = ⌊δ n⌋` (and `n - s ≤ ⌊δ n⌋ ≤ δ n` for every `δ ≥ 0`), so the integer
   form is slightly stronger when `δ n` is not an integer; `main_thm_delta_floor` is that form,
   written with `δ`.
2. **Codewords are messages.** The code is given by its injective linear encoding map
   `Enc_C : F^ℓ → F^n` (Section 2.2), the field `enc` of `Setup`, and a codeword is represented by
   its message: `c : Fin R.ℓ → F` stands for the codeword with entries `R.enc c i`. The paper does
   the same when it applies the zero evader to a codeword (`φ_z(Enc_C(w)) := φ_z(w)`). The list
   decodability `ListDecodable` therefore counts messages, which is the same as counting codewords
   since the encoding map is injective (`card_filter_codewords` in `Proof.lean`); `main_thm_delta`
   counts codewords, with the relative Hamming distance. The injectivity is used nowhere else.
3. **The zero evader.** It is the field `φ` of `Setup`: a linear map `F^ℓ → F^m` for every `z` in a
   finite type `Z`. `IsErrorBound ε` is Definition 2.2: `ε ≥ 0`, and every nonzero `v` has
   `Pr_z[φ_z(v) = 0] ≤ ε` (the bound `ε ≤ 1` of the paper is not needed). The counting form takes
   instead a natural number `M` such that every nonzero `v` has `φ_z(v) = 0` for at most `M` of
   the `z`. The theorems that speak of a probability assume that `Z` is nonempty.
4. **Answers.** The prover's answers are a function `B` from `z` to `(b₁, b₂)`. Theorem 3.4 is about
   `maxHits`, the largest number of DEEP-MCA-bad elements over all answers to `z`, and a single
   worst-case `B` attains it at every `z` (`exists_worst_answers` in `Proof.lean`).
5. **MCA-bad elements.** Definition 3.1 is `MCABad` (the negation of the MCA property,
   `SatisfiesMCA`). Definition 3.2 and the set `A_θ^pret` of Lemma 3.7 are stated without the
   condition "`α` is MCA-bad", which follows from the existence of an `α`-pretender
   (`mcaBad_iff_exists_pretender` in `Proof.lean`).
6. **Hypotheses that are not needed.** Lemma 3.8 only needs `α₁ ≠ α₂` (the paper takes the three
   `α_i` pairwise distinct). That `n` is a power of two, that `δ < 1` and that `L ≥ 1` are not
   used.
7. **The threshold `t`.** It is a natural number in `main_thm_delta`, as in Theorem 5.3;
   `main_thm_delta_real` is the same statement for a real `t ≥ δ n + 2`.

Not formalized: the last sentence of Theorem 3.4 on the `δ`-MCA error (see above); Remark 3.5;
Section 4 (Constructions 4.1 and 4.5, Theorems 4.3 and 4.6); the error bounds of the univariate
and multilinear evaders (Lemmas 2.5 and 2.8; the examples of `check.sh` prove the case of one
sample of the univariate evader over `ZMod 5`).

## Theorem 5.3: `BEEP/Affine`

`BEEP/Affine` formalizes Theorem 5.3 of the paper (Section 5, "BEEP with affine folding for
Reed-Solomon codes") together with the lemma behind it, Lemma 5.5.

### The statements: `BEEP/Affine/Theorem.lean`

| paper | Lean (namespace `BEEP.Affine.Setup`) |
|---|---|
| Theorem 5.3 as stated, with `δ` and the relative Hamming distance | `affine_main_delta` |
| Theorem 5.3 with the integer agreement threshold `s` of the definitions (probability form, counting form) | `affine_main`, `affine_main_nat` |
| if `|A_z| < t`, a uniform challenge is DEEP-MCA-bad with probability at most `(t - 1)/|F|²` | `fold_challenge_le` |

`affine_main` reads: let `N = max(q, (n - s + 2)(n - s + 1)/2)` and let `C⁺ = RS_{ℓ+1}` be list
decodable with list size `L` at agreement `s`; then for every integer `t ≥ N + 1`, for `z` uniform in
`F^m`, `Pr[|A_z| ≥ t] ≤ (q² L)³ ((ℓ + 1)/q)^m / (t (t - 1) (t - N))`, where `q = |F|`, `n` is the block
length, and `|A_z|` is the largest number of DEEP-MCA-bad challenges at `z` over all answers.
`affine_main_delta` is the same with `s = ⌈(1 - δ) n⌉`, the relative Hamming distance in the list
decodability of `C⁺`, and the paper's `N = max(|F|, (δn + 2)(δn + 1)/2)`.

`fold_challenge_le` is the error of the fold challenge that follows the samples in a protocol that
uses Theorem 5.3. The paper describes no such protocol for affine folds (Section 5 says why), and
none is formalized here.

### The definitions: `BEEP/Affine/Defs.lean`

| paper | Lean (namespace `BEEP.Affine.Setup`, unless the full name is given) |
|---|---|
| the evaluation points, the code dimension, the weights of the fold (Section 5.1) | the structure `BEEP.Affine.Setup` |
| the polynomials of degree less than `k`, as a finite set; the challenge `σ + τ X` of a pair `(σ, τ)` | `BEEP.Affine.polysLT`, `BEEP.Affine.chal` |
| the weights and the affine fold | `lam₁`, `lam₂`, `affineFold` |
| the set `C_θ^{≡2}`; Correlated Agreement with it over `S` up to one position | `Pairs`, `CAUpToOne` |
| `α`-pretender and MCA-bad challenge (Definition 5.1) | `IsPretender`, `MCABad` |
| consistency and DEEP-MCA-bad challenge (Definition 5.2) | `Consistent`, `DeepBad` |
| list decodability of `C⁺`, with the integer agreement threshold | `ListDecodable` |
| `A_{z, b₁, b₂}` and `|A_z|` | `hits`, `maxHits` |
| the code `RS_k` as a set of words | `rsWords` |

The module documentation of the file has the setting and the full dictionary between the paper
and the Lean names.

### The lemmas and the proofs: `BEEP/Affine/Proof.lean`

| paper | Lean (namespace `BEEP.Affine.Setup`) |
|---|---|
| Lemma 5.5, second case of the proof (a line of `C_θ^{≡2}`) | `affine_line_pairs` |
| Lemma 5.5 | `affine_line` |
| Theorem 5.3, for given answers (counting form, probability form) | `affine_main_gen_nat`, `affine_main_gen` |
| the proofs of the four theorems of `Theorem.lean` | `affine_main_delta_proof`, `affine_main_proof`, `affine_main_nat_proof`, `fold_challenge_le_proof` |

The proof follows the paper step by step: `affine_line` (Lemma 5.5, with the pigeonhole argument of
its first case and the count of pairs of positions of its second case, `pair_count_arith` being the
final arithmetic); `onLine_of_defect_eq_zero` and `defect_eq_zero_of_onLine` (first step: three
tuples on one line iff `U = 0`); `eval_defect_eq_zero` (second step: `φ_z(U) = 0` for consistent
tuples, using that evaluation is multiplicative); `card_collinear_le`, `card_goodTriples`,
`card_goodTriples_le` (third step: `|A_z| (|A_z| - 1) (|A_z| - N) ≤ |T_z|`, the analogue of
Lemma 3.10); `card_pretPts` and `sum_card_consTriples` (last step: `|P| ≤ |F|² L`, and a nonzero `U`
of degree at most `ℓ + 1` has at most `ℓ + 1` roots in each coordinate of `z`). The structure is that
of `BEEP/Scalar/Proof.lean` (`few_pretenders_on_line` there corresponds to `affine_line_pairs`
here), but neither folder imports the other: the objects differ (polynomials, challenges in
`F × F`).

### How the formalization differs from the paper's presentation

None of these changes the content of Theorem 5.3; `affine_main_delta` is in the paper's form.

1. **Agreement threshold.** As in `DeepFold/Lemma1.lean`, the definitions use an integer agreement
   threshold `s` (agreement sets of size at least `s`) in place of `(1 - δ) n`, so that `δ n` becomes
   `n - s`. `affine_main_delta` takes `s = ⌈(1 - δ) n⌉`, for which the pretenders are exactly those of
   Definition 5.1 (`isPretender_ceil_iff` in `Proof.lean`), and its `N` is the paper's
   `max(|F|, (δn + 2)(δn + 1)/2)`. The `N` of the integer form is at most that one, so the integer
   form is slightly stronger.
2. **Codewords are polynomials**, as in Section 5.1 of the paper: `RS_e` is Mathlib's `degreeLT F e`.
   The list decodability `ListDecodable` therefore counts polynomials of degree at most `ℓ`; this is
   the same as counting codewords when `ℓ + 1 ≤ n` (`card_close_rsWords` in `Proof.lean`).
   `affine_main_delta` assumes `ℓ + 1 ≤ n` and counts codewords, with the relative Hamming distance.
3. **Challenges are pairs** `(σ, τ) ∈ F × F`, with the polynomial `chal (σ, τ) = σ + τ X`.
4. **Lines with rational coefficients** (Definition 5.4) are written with a common denominator:
   `θ(α) = P/D + α · Q/D` with polynomials `D ≠ 0`, `P`, `Q`, and "`c` lies on the line at `α`" is
   `D c = P + α Q`. This way the whole proof stays with polynomials (no `RatFunc`).
5. **Answers.** The prover's answers are a function `B` from `z` to `(b₁, b₂)`. Theorem 5.3 is about
   `maxHits`, the largest number of DEEP-MCA-bad challenges over all answers to `z`, and a single
   worst-case `B` attains it at every `z` (`exists_worst_answers` in `Proof.lean`).
6. **Standing assumptions.** `ℓ ≥ 1` (Section 5.1) is not needed for the integer form;
   `affine_main_delta` uses `ℓ + 1 ≤ n` (to identify codewords with polynomials) and `δ ≥ 0`.

Not formalized: Remark 5.6.

## Checking them

All the checks in one go (it writes only to the scratch folder `$TMPDIR/beep-lean-check`, and
refuses to run while a benchmark campaign holds `/tmp/bitz-bench.lock`):

    ~/BEEP/lean/check.sh

It passes `-DautoImplicit=false -DrelaxedAutoImplicit=false`, the options of `lakefile.toml`, to every
`lean` call. In this order, it

1. checks that the two `Defs.lean` import Mathlib only, and that the two `Proof.lean` import their
   `Defs.lean` only and contain no command other than definitions and theorems;
2. type-checks the six files and compiles them into the scratch folder, and type-checks the root
   file `BEEP.lean`, which imports the two `Theorem.lean`;
3. checks two files of examples, which import the compiled files, and prints the axioms of 14
   theorems of `BEEP/Affine` and of 21 of `BEEP/Scalar` (with its examples); it stops with an error
   if one of them depends on anything but `propext`, `Classical.choice` and `Quot.sound`;
4. checks that the statement of each of the 6 theorems of `BEEP/Scalar/Theorem.lean` and of the 4
   of `BEEP/Affine/Theorem.lean` mentions only declarations of the `Defs.lean` of its folder and of
   Mathlib.

The examples:

- **Examples for `BEEP/Affine`**: a `Setup` over `ZMod 5` with the weights `(1, α)` and one
  with the weights `(1 - α, α)` of Section 4, `affine_main` applied to both and `affine_main_delta`
  (with `δ = 1/4`) to the second, every hypothesis proved, with the trivial list size.
- **Examples for `BEEP/Scalar`**: the Reed-Solomon code of dimension 2 on four points of
  `ZMod 5` (with a proof that its encoding map is injective), the univariate zero evader with one
  sample and a proof that `1/5` is an error bound of it, the weights `(1, α)` and `(1 - α, α)`;
  `main_thm` applied to both setups, `main_thm_delta` and `main_thm_delta_real` (with `δ = 1/4`)
  to the second, and `main_thm_delta_floor` with `δ = 3/10` (so `δ n = 1.2` is not an integer and
  `t = 3` is allowed), every hypothesis proved, with the trivial list size. And a concrete
  case in which the definitions are inhabited: for `u₁ = (0, 0, 1, 0)`, `u₂ = (0, 0, -1, 0)` and
  `s = 3`, the zero codeword is a `1`-pretender, and `α = 1` is a DEEP-MCA-bad element at every `z`.

With the trivial list size the bounds exceed 1, so the examples show that the hypotheses can be
met and that the theorems apply, not a useful bound.

The record of the checks. The first three entries are about the two files that held the
formalizations until November 17, 2026, `BEEP/AffineMain.lean` (Theorem 5.3, namespace `BEEP`) and
`BEEP/MainTheorem.lean` (Theorem 3.4, namespace `BEEP.Main`).

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
- On November 17, 2026 the two files (`BEEP/AffineMain.lean` at `shasum`
  `d484d8253b6ac000e52677b2908441d8ecb4984c`, `BEEP/MainTheorem.lean` at `shasum`
  `4cf6c22bac6be84fa75968070941e68587ed8db9`: the file of November 16 with the author's edit of its
  first comment and a pair of brackets added in `SatisfiesMCA`) became the six files of `BEEP/Scalar` and
  `BEEP/Affine`, by a script that moved every definition, lemma and proof without retyping it.
  A Lean program then compared each of the 273 declarations of the two old files (the definitions
  and theorems, and what Lean generates for them) with the declaration of the same name in the new
  files, up to the names of the namespaces: 269 have the same kind, the same statement (binder
  names and kinds included) and, for the 75 definitions, the same body; the other 4 are auxiliary
  lemmas that Lean generates inside the proofs of four theorems that are now called `x_proof`. The
  new files have 10 more theorems, the `x_proof`, each with the statement of its `x`. So no
  definition and no statement changed. With the six files at the `shasum`s below, the script
  printed what the section above describes and nothing else, in about a minute.

  | file | `shasum` |
  |---|---|
  | `BEEP/Scalar/Defs.lean` | `0c65579f3b780e50c003725404a6295dbbec779e` |
  | `BEEP/Scalar/Theorem.lean` | `dc3052c83ec6f8f622b2356515684f2dd28b192d` |
  | `BEEP/Scalar/Proof.lean` | `cbffcffce5c763b47150bac618bca802a43b890e` |
  | `BEEP/Affine/Defs.lean` | `6078a132edf888560d86685ca6176fc1e6d33994` |
  | `BEEP/Affine/Theorem.lean` | `b73cb52c7cc2fa24fb5e8a4bb90e64fe601fb9a8` |
  | `BEEP/Affine/Proof.lean` | `17e63b6085205aa4b1198a636ae2cb35442db9a4` |

By hand, with the Mathlib build of `~/math in lean` (same version, v4.30.0), a `Defs.lean` can be
checked alone:

    cd "$HOME/math in lean" && lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
      ~/BEEP/lean/BEEP/Scalar/Defs.lean

No output means that the file type-checks. The other files import files of this folder, which are
not on the search path of `~/math in lean`; `check.sh` compiles them into its scratch folder first
and puts that folder on the search path.

As a standalone project (`lake exe cache get` downloads and unpacks Mathlib v4.30.0, several GB):

    cd ~/BEEP/lean && lake exe cache get && lake build

Tested on November 17, 2026 with the Mathlib cache already in `.lake`: `lake build` compiled the seven
files of this folder (the six above and `BEEP.lean`) in a little over two minutes, and wrote only to
`.lake/build`. This is also what the Lean extension of VS Code does when a file of this folder is
opened.
