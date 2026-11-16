<!-- [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: the provenance of the Flock copy of this folder and the list of local changes; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-13: the second version of beep.rs and of the bench (run 20261113b), and the affine ladders at their least certified slack] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14: the third version (run 20261113e): eight files, with the counters of the bench and Flock's derivation of a profile at another rate; the patch is regenerated] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14: the fourth version (run 20261114g): nine files, with our prover for the affine ladder (affine_fast.rs) and the affine configuration with no sample on its first commitment; the patch is regenerated] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14: the fifth version (run 20261114h, at 100 bits): the round-by-round target of the BEEP and affine ladders is a parameter, and the bench takes `bits=100` with Flock's profiles `fast100` and `slim100`; the same nine files; the patch is regenerated] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-15: the run at 100 bits is now 100bits-3; the patch was checked against the source of that run (identical), and the sentence on which run it belongs to says so] -->

# The Flock copy in `flock/`

`flock/` is copied from `https://github.com/succinctlabs/flock`, branch `affine-fold-f128`, commit
`14b78c09b182fdbf0c88fbbf999adbc0ea394fe0` (November 10, 2026). That branch is `main` at
`eac05379f95580052daa108c5bef30bdf63cc913` (November 9, 2026) plus the affine fold of Ligerito. The copy was made
with `git archive` on November 13, 2026. Copyright notices and licenses are retained (`LICENSE-APACHE`,
`LICENSE-MIT`; the workspace is MIT OR Apache-2.0).

What is copied: `Cargo.toml`, `Cargo.lock`, `.cargo/config.toml`, the crates `flock-core`, `flock-field`,
`flock-hash`, `flock-merkle`, `flock-multilinear`, `flock-parallel` and `flock-transcript`, the script
`scripts/affine_fold_params.py` and the design note `docs/affine-fold-f128.tex`. The crates `flock-prover` and
`flock-cuda-ffi`, the other documents, the benchmarks folder and the CUDA code are not copied.

## Local changes

`beep.patch` is the output of `diff -ruN` between the copy as extracted (`a/`) and `flock/` (`b/`), regenerated on
November 14, 2026 for the code of the runs at 100 bits (for 128 bits it builds the same ladders and writes the
same proofs as the code of the run 20261114g). It is the source of the run 100bits-3, whose `binaries.txt` has
the hashes of `beep.rs`, of the bench and of `affine_fast.rs`. The first run at 100 bits, 20261114h, was built
before a header comment of four lines was added to `beep.rs` (the file without its lines 25 to 28 has the hash
that the `binaries.txt` of that run records): the same code, another hash of the bench binary. It has nine
files:

| file | change |
|---|---|
| `crates/flock-core/src/pcs/ligerito/beep.rs` | new: the BEEP ladder (parameters, prover, verifier, 13 tests), for a round-by-round target of 128 bits (`beep_ladder`) or another one (`beep_ladder_at`: 100 bits on Flock's profiles `fast100` and `slim100`); its proofs of work in whole bits or with a threshold (`Grind`), through the searches that Flock's transcript already has; `PowGrinds`, the proof-of-work searches of a proof of each of the three ladders; the prover with one pass per fold round and its NEON kernels, and the direct prover that it is tested against; `affine_ladder_at`, which builds the configuration of Flock's affine ladder at a slack per level (Flock's `affine_ladder` with its constant slack 0.02 replaced), and `affine_ladder_target`, the same for another target than 128 bits; the byte counts of a proof per part and per level |
| `crates/flock-core/src/pcs/ligerito/affine_fast.rs` | new: `prove_affine_fast`, a prover for Flock's affine ladder on a dense table with one pass per fold round (NEON kernels, buffers from Flock's pool), which writes the same proof as Flock's `prove_affine`, byte for byte; `without_first_sample`, which turns an affine configuration into the one with no out of domain sample on its first commitment and a given fold grinding at its first level; `will_overwrite`, a cache hint that `beep.rs` also uses; 3 tests |
| `crates/flock-core/benches/ligerito_three_way.rs` | new: the bench of the comparison |
| `crates/flock-core/benches/support/run_counters.rs` | new: what a prover run used besides its wall time (`proc_pid_rusage` and `getrusage`; macOS only, zeros elsewhere) |
| `crates/flock-core/src/pcs/ligerito.rs` | `pub mod beep;` and `pub mod affine_fast;` with their comments; and `derive_profile_ladder_at_rate`, which is the body of Flock's `derive_profile_ladder` with the rate of the first level as an argument (`derive_profile_ladder` now calls it with the rate of the profile, so it returns what it did) |
| `crates/flock-core/src/pcs/ligerito/affine.rs` | visibility only: private items become `pub(super)`, so that `beep.rs` and `affine_fast.rs` can use them (`level_shapes`, `native_ks`, `t_at`, `novel_basis_evals`, `query_point`, `PAR_MIN`, `Level` with its fields and methods, `EqFactors` with its fields and methods, `Commitment` with its fields and `row`, `view`, `batched_consistency`, `Context`, `eq_at_residual`, `induced_at_residual`). No behaviour changes |
| `crates/flock-core/Cargo.toml` | the `[[bench]]` entry of `ligerito_three_way` |
| `Cargo.toml` | the workspace members: the two crates that are not copied are removed |
| `Cargo.lock` | rewritten by cargo after that removal |

Nothing else differs from the commit above. In particular the split prover and verifier
(`pcs/ligerito/extension.rs`), the affine prover and verifier, Flock's configurations and its transcript are
those of Flock, and so are its profiles `fast100` and `slim100`, on which Ligerito (Flock) runs at 100 bits.
The variants `affine` and `affine-small` of the comparison run Flock's affine prover and
verifier, unchanged; the second one on a configuration that `affine_ladder_at` builds with Flock's own rules at a
smaller slack. The variants `anfref`, `anfref-small` run the same prover and verifier on a configuration with
no out of domain sample on the first commitment (`ood_samples[0] = 0`, a value that Flock's code accepts), and
`afast`, `anf` and their `-small` forms run our prover with Flock's verifier. At the
rates 1/8 and 1/16, for which Flock ships no configuration, the variant "Ligerito (Flock)" runs Flock's split
prover and verifier, unchanged, on the configuration that `derive_profile_ladder_at_rate` returns for the
profile `slim` at that rate.

To see the changes on a fresh clone:

```sh
git clone https://github.com/succinctlabs/flock && cd flock && git checkout 14b78c09b182fdbf0c88fbbf999adbc0ea394fe0
patch -p1 < <this folder>/beep.patch      # Cargo.toml and Cargo.lock will not apply on the full workspace: skip them
```

## What is not Flock's

The BEEP ladder, its parameters and its numbers are ours, and Flock's authors have not seen them. The same holds
for our prover of the affine ladder, and for the affine configurations with no sample on the first commitment:
their fold grinding at the first level follows an accounting of ours (`eps_aff + 2L/|F|` per fold round), which
is not in Flock's note. Most of the
affine ladders are also ours: Flock registers affine ladders for 2^25 words at rate 1/2 and for 2^22 words at
rate 1/4 (among the shapes we run), and for the others (2^16 to 2^24 words at rate 1/2, 2^24 words at rate 1/4,
and the rates 1/8 and 1/16) we ran Flock's script ourselves (`affine_certificates/*.toml` and their `.txt`
outputs). The split configurations at the rates 1/8 and 1/16 are Flock's derivation, but Flock does not ship
them.

The affine ladders at a smaller slack are ours as well (`affine_certificates/*_least_slack.txt`). Flock's script
stops its search at multiplicity 40 and degree 20000, which is too early for a small slack. `scripts/beep_params.py`
searches further, with the formulas of Flock's script, and checks every pair (m, D) that it uses with the function
`lemma31_feasible` of that script. The bound is the finite bound of the affine-combiners paper (its Theorem 4.10 in
the version of November 11, 2026; "Lemma 3.1" in the draft that Flock's note and script follow). The script also
searches the parameter B of the proof, as Flock's script does; the published theorem fixes B, and with that B the
bounds are about one bit weaker (`beep_params.py --print` shows both).
