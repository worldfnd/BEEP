<!-- [AI-drafted (claude-fable-5-2), 2026-11-16, at the author's request ("Can you make sure we are using the optimized version of BEEP-Ligerito from the folder 7-beep-ligerito"); the numbers of this file are written by a script from `output.txt`; please review] -->

# The bench binary of the original folder against today's, side by side (November 16, 2026)

**Question.** Is the BEEP-Ligerito that the paper's section measures the optimized one of
`random-domain-ligerito/7-beep-ligerito`?

**The sources.** `diff -rq` of `random-domain-ligerito/7-beep-ligerito/flock` against `beep-ligerito/flock` of this
repository: two files differ, `crates/flock-core/src/pcs/ligerito/beep.rs` and
`crates/flock-core/benches/ligerito_three_way.rs`. Everything else is identical, `affine_fast.rs`, `affine.rs`,
the manifests and `.cargo/config.toml` (`-C target-cpu=native`) included. The original folder has no commit and
no uncommitted change after November 14, 2026. In `beep.rs` the diff is the additions of November 16 (the
ladders `mca_ladder_at` and `mca_ladder_no_first_sample_at`, a fold grind per round, comments, tests) and eleven
changed lines, all of them the passing of that grind (`fold` becomes `fold[j]` in the two round functions and in
the verifier; `min_bits`; `pow_grinds`; the import list of the tests). The fold passes, the kernels and the
cache hint are untouched. The variant `beep-<eta>` of the bench calls `prove_beep_timed`, i.e. the prover with
one pass per fold round (`rounds_fast`); the direct prover only runs as `beepref-<eta>` and `beepold-<eta>`.

**The measurement** (`ab_compare.py`, `output.txt`). The binary of the original folder, built on November 14
(the binary of its run `100bits-3`, hash `80c4da9a5f673136`), and the one of this repository (hash
`3f285843e5fcbb34`, the binary of the run `minimal-20261116-ac3`), on the same five cells, alternating three
times, 9 repetitions each time, without proofs of work (`FLOCK_NO_GRIND=1`). By hand, not through the gate, on
a machine in use and on battery power: a comparison of two binaries under the same conditions, not a
measurement for the paper.

- The proofs of the 25 rows (five cells, five variants) have the same size in both binaries: yes.
- Median time of the new binary over that of the old one: 0.94 to 1.00 for the ten BEEP-Ligerito
  rows, 0.91 to 1.03 over all the rows (Flock's own prover, which is the same code in both, is
  among them, at 0.91 to 1.03).
- BEEP-Ligerito against the same ladder with no samples (`control-<eta>`), without proofs of work:
  1.23 to 1.38 times as long in the old binary, 1.23 to 1.34 in the new one.
  In the night run of November 14 of the original folder (`three-way-20261114g`, a quiet machine) the same
  ratio was 1.27 to 1.51 for the slack 0.001 at rate 1/2.

**Conclusion.** The two binaries are the same prover. The cost of the samples that the paper's section reports
is the cost in the optimized prover, and it was already there on November 14.
