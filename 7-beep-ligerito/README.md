<!-- [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: the README of the BEEP-Ligerito folder (what it is, how to reproduce it, the run of November 13, 2026); please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-13: the second version of the code and the run 20261113b, after an independent review of the first (binding points in one message, batching with the list of the next code, the affine variant at its least certified slack, proofs of work at the measured cost per search, the parts of a proof per level); please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request: the third version of the code and the run 20261113e (thirteen instances with smaller rates and short messages; BEEP-Ligerito with no sample on its first commitment, one pass per fold round and proofs of work with a threshold), what each of these changes gives, the accounting experiment with the error of the affine fold, and what we know about the timing of the affine prover; the tables are printed by scripts/readme_tables.py; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("Provide numbers for n=2^15 and rate 1/8 for table 4"; "Let's now run experiments for 100 bits of security, same parameter regimes as for 128 bits of security"): a fourteenth instance (2^15 words at rate 1/8, measured on its own with the binary of the run 20261114g), and the run 20261114h of the same cells at 100 bits, whose sizes are final and whose timings of the large instances are not (the machine was short of memory); please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("try to bring the affine version to a similar level of optimization as BEEP", "find out if the affine time anomaly is still relevant", "remove the sample on the first commitment for the affine version ... so as to match beep"): the fourth version of the code and the run 20261114g; the affine variant of the tables now has no sample on its first commitment and a prover of ours (affine_fast.rs); what that sample is and what dropping it costs; what each of the two changes gives; the discarded run 20261114f (a defect in the buffers of the new prover); the state of the timing anomaly; please review] -->
<!-- [AI-revised (claude-fable-5-2), 2026-11-15, for the request on 100 bits of security: the run at 100 bits is now 100bits-3 (at night, with less unused memory than for the run at 128 bits); all its times are used, by a rule that was written before the run was read and that is looser than the guard of the run at 128 bits; the section "The run at 100 bits" says how it was measured, which processes had compressed memory and what this does to single proofs, what the rule does not test, and which two processes were a few percent slow; revised after an independent check against the raw results; the bounds that the text quotes are rounded in the safe direction; please review] -->

<!-- [AI-revised (claude-opus-5-5), 2026-11-16, at the author's request ("Create a new repository called BEEP ... It should contain ... The BEEP-Ligerito variant we worked on"): this folder is copied, as it was in the repository random-domain-ligerito, into the repository BEEP; changed here: the paths to the gate (now `scripts/bench_gate.py`, a copy of the one in `5-implementation/scripts` of that repository), the `cd` lines of "Reproducing", the paragraph on `5-implementation`, and two rows of the layout (`scripts/bench_gate.py`, `WORKLOG.md`); please review] -->

# 7-beep-ligerito: BEEP-Ligerito on Flock's code

**Research code, unaudited.** This folder holds the implementation and the measurements behind the Experiments
section of the BEEP paper (`../typst/deep+.typ`). It compares openings of the same Ligerito commitment over
GF(2^128), at 128 bits (and at 100 bits, see "The run at 100 bits"):

- **Ligerito (Flock)** (`split` in the scripts): Flock's Ligerito as it ships. It commits to words over
  GF(2^128), samples its fold challenges in GF(2^256), and commits to each folded table as two tables over
  GF(2^128) (`pcs/ligerito/extension.rs`). Its folds rest on mutual correlated agreement at the Johnson radius.
- **affine Ligerito**: the variant of Flock's branch `affine-fold-f128`, with affine folds and every challenge in
  GF(2^128) (`pcs/ligerito/affine.rs`, design note `flock/docs/affine-fold-f128.tex`). The tables of the paper
  run it with two changes of ours (see "The affine variant as we run it"): no out of domain sample on the first
  commitment, and a prover of ours that makes one pass per fold round and writes the same proofs as Flock's
  (`pcs/ligerito/affine_fast.rs`, new). The bench runs the four combinations: as Flock ships it (`affine`), with
  our prover (`afast`), without the sample (`anfref`), and with both (`anf`, the affine variant of the tables).
  Each runs at the slack 0.02 of Flock at every level, and with the least slack that we can certify at each
  level (suffix `-small`; the same provers and verifier on another configuration).
- **BEEP-Ligerito** (`beep-<eta>`): the affine variant with its fold round replaced by the BEEP reduction of the
  paper (`pcs/ligerito/beep.rs`, new), at the slacks 0.02 and 0.001. Before every fold challenge the verifier
  samples `m` points and the prover answers the multilinear extensions of the two halves of the current table at
  them. The fold is the scalar fold of a sumcheck round. The commitment, the queries, the consistency checks and
  the final check are those of the affine variant. Like the affine variant as we run it, it has no sample on the
  first commitment. Three more points differ (below): how the binding points are drawn, the list that the
  batching of the queries counts, and proofs of work with a threshold.

This folder was developed in the repository `random-domain-ligerito`, next to its `5-implementation` (the generic
DEEP-Ligerito crate of Notes 3 and 4 of that repository, with its own protocol and accounting, `SPEC.md`). Nothing
here changes that crate, and the two do not share code.

## Layout

| path | contents |
|---|---|
| `flock/` | a pinned copy of Flock (commit `14b78c0`, branch `affine-fold-f128`) with the local changes of `VENDORED.md` |
| `VENDORED.md`, `beep.patch` | the provenance of the copy, and the local changes as a patch |
| `flock/crates/flock-core/src/pcs/ligerito/beep.rs` | the BEEP ladder: its parameters (`beep_ladder`, `BeepConfig`), prover (`prove_beep`), verifier (`verify_beep`) and tests; the proofs of work of every ladder (`Grind`, `PowGrinds`); `affine_ladder_at` (the configuration of the affine ladder at a slack per level). Its module documentation states the protocol, the error of every challenge, the proofs of work with a threshold, and how the prover's fold rounds work |
| `flock/crates/flock-core/src/pcs/ligerito/affine_fast.rs` | our prover for Flock's affine ladder on a dense table (`prove_affine_fast`): one pass per fold round, NEON kernels, buffers from Flock's pool, the same proofs as Flock's prover; `without_first_sample`, the affine configuration with no sample on its first commitment; 3 tests |
| `flock/crates/flock-core/benches/ligerito_three_way.rs` | the bench: the openings on the same witness, basis and commitment, one `RESULT {json}` line per variant. Before it times them, it checks that our affine prover and Flock's write the same proof |
| `flock/crates/flock-core/benches/support/run_counters.rs` | what a prover run used besides its wall time (CPU time, instructions, cycles, the part on performance cores, context switches), from `proc_pid_rusage` |
| `scripts/cells.txt`, `scripts/run_cells.zsh` | the cells of the comparison and their timing driver (through `scripts/bench_gate.py`); `scripts/cells_add_g1.txt` has the two cells of the instance that was added to the run 20261114g |
| `scripts/cells100.txt`, `scripts/make_cells100.py` | the same cells at 100 bits, and the script that writes them from `cells.txt` (Flock's profiles `fast100` and `slim100`, `bits=100`, the fold grinding of the affine ladders for 100 bits) |
| `scripts/bench_gate.py` | the gate of the timed runs: a machine-wide lock (`/tmp/bitz-bench.lock`, shared with the other projects on this machine on purpose) and a wait for a sustained idle CPU; a verbatim copy of `5-implementation/scripts/bench_gate.py` of the repository `random-domain-ligerito` |
| `WORKLOG.md` | the phases of the work on this folder, copied from `5-implementation/WORKLOG.md` of the repository `random-domain-ligerito` |
| `scripts/when_memory_is_free.zsh` | waits for unused memory, then runs a command: for a campaign on a machine that is in use |
| `scripts/collect.py` | a run's folder → `results.json` (one row per cell and variant, proofs of work at their expected cost) |
| `scripts/beep_params.py` | the exact recheck of every BEEP level of a run and of the fold grinding of its affine ladders, with and without the sample on the first commitment (`--check`), the error of one fold under each analysis (`--print`; the paper's fold tables), the affine ladders with their certificates and their fold grinding without the sample (`--affine-ladder`), and the fold grinding of a BEEP ladder under the error of the affine fold (`--beep-affine-charge`) |
| `scripts/readme_tables.py` | the tables of this README, from the tables that the paper reads |
| `affine_certificates/` | the affine ladders that we run: at the slack 0.02 as inputs and outputs of Flock's `affine_fold_params.py` (`*.toml`, `*.txt`), at their least slack as outputs of `beep_params.py --affine-ladder` (`*_least_slack.txt`), the fold grinding of the accounting experiment (`*_beep_affine_charge.txt`), and the cache of the searches (`search_cache.json`) |
| `bench_results/three-way-20261114g/` | **the run that the paper quotes** (November 14, 2026, 03:07 to 04:06): `machine.txt`, `binaries.txt`, `cells.tsv`, `cells/*.{out,err,meta}`, `results.json`; the `*.gate.log` files are the gate's logs |
| `bench_results/three-way-20261114g-add2/`, `three-way-20261114g-add1/`, `three-way-check-20261114g-add1/` | one more instance for that run, 2^15 words at rate 1/8, measured on its own with the same binary (November 14, 09:09 to 09:20). The tables use `-add2`, which waits for an idle machine before each cell; the other two are earlier measurements of the same cells |
| `bench_results/three-way-100bits-3/` | **the run at 100 bits that the paper quotes**: the same cells at 100 bits of security (`scripts/cells100.txt`; November 15, 2026, 01:10 to 02:10, at night, with the idle check before every cell). See "The run at 100 bits" |
| `bench_results/three-way-20261114h/` | the first run of the cells at 100 bits (November 14, 09:43 to 10:48). The machine was in use and short of memory: same proof sizes and parameters, times not used |
| `bench_results/three-way-100bits-2.gate.log` | the log of a watcher that waited 14 hours for 9 GB of unused memory to start that run again, and gave up (no run) |
| `bench_results/smoke-100bits-20261115/` | two cells of the run at 100 bits, run by hand a few minutes before the campaign 100bits-3 (see its `INDEX.md`): what the limit on page faults of that run was chosen after |
| `bench_results/three-way-20261114f/` | the same cells one hour earlier (01:53 to 02:54), with a defect in the buffers of our affine prover: discarded, see "Earlier runs" |
| `bench_results/three-way-20261113e/`, `three-way-20261113e-rerun1/` | the run that the paper quoted before, with the affine variant as Flock ships it (November 13, 2026, 23:30, to November 14, 00:28), and a rerun of two of its processes (00:45) |
| `bench_results/three-way-20261113d/` | the same cells one hour earlier, with proofs of work of a whole number of bits (22:26 to 23:23) |
| `bench_results/three-way-20261113c/` | ten instances with the prover of the second version (20:53 to 21:32); the machine was in use during this run |
| `bench_results/three-way-20261113b/`, `three-way-20261113b-check1/`, `diagnostics-20261113b/` | the run of the second version (five instances), a second run of its four shared shapes, and 43 runs by hand around the anomaly of the affine prover |
| `bench_results/three-way-diag-20261113-{old-q1,oldc-q1,new-q1}/`, `scripts/cells_diag_affine.txt` | three more runs of two shapes through the gate, on a quiet machine, for the same anomaly: with the binary of the run 20261113b rebuilt from its sources, with the same plus the counters, and with the binary of the working tree at that time (between the runs 20261113c and 20261113d) |
| `bench_results/three-way-20261113/`, `three-way-20261113-rerun25/` | the run of the first version of the code. Superseded: see "What changed after the review" |

The tables and the numbers of the paper are written by `../typst/scripts/make_tables.py`, which reads
`results.json` and imports `scripts/beep_params.py`.

## What BEEP changes

One fold round of `beep.rs`, for a table of `2^dim` words:

1. the verifier samples `m` points of `F^(dim-1)`;
2. the prover sends the `2m` answers `<f_0, eq(z_i)>`, `<f_1, eq(z_i)>`;
3. the prover sends the round polynomial of the sumcheck as two elements;
4. the verifier samples the fold challenge `r` and `m` batching coefficients in one squeeze, behind the fold
   grinding;
5. both fold the table and the weight at `r`, and the `m` claims join the claim of the sumcheck.

The affine round sends five elements and samples three challenges instead, and its folded message grows by one
coefficient per round; BEEP has no such overflow.

Outside the fold round, BEEP-Ligerito differs from Flock's affine ladder in four points. The third one (no sample
on the first commitment) is now also a change of the affine variant that we run, see the next section:

- **The binding points of a commitment are drawn in one message.** Flock's ladders draw a point, take its value
  and a batching coefficient, and then draw the next point, while their bound (two list codewords agree on all
  `p` points with probability at most `C(L, 2) (mu/|F|)^p`) is the error of points that are drawn together. Round
  by round we do not know how to give 128 bits to each of two points drawn one after the other (a threshold
  argument gives about 120). `beep.rs` draws the `p` points in one squeeze, takes their values, and draws the `p`
  coefficients in one squeeze behind one proof of work, as in Construction `c:BEEP_codeswitch` of the paper.
- **The coefficients that batch the queries of a level are ground for the list of the next code**
  (`L' ceil(log2 Q) / |F|`, the term `kappa'_3` of `t:beep_codeswitch`), since the candidates at that point are
  the codewords near the new commitment. Flock's rule uses the list of the level itself, which is smaller when
  the rate decreases. This costs one bit of grinding per code switch.
- **No sample on the first commitment** (`BeepConfig::without_first_binding`). Flock's ladders draw one out of
  domain point on the first commitment, and from then on their fold rounds are analyzed for one codeword. In
  `c:BEEP_codeswitch` only the new commitments are sampled, and the errors of `t:beep_soundness` carry the list
  (the terms `2L` and `L`), which the fold squeeze `(t + 3L)/|F|` already pays for. So the sample is not needed,
  and the prover saves an evaluation of the whole message (two passes over the table and its weight). The
  variant `beepb-<eta>` of the bench keeps the sample.
- **Proofs of work with a threshold** (`Grind::Below`, `BeepConfig::with_exact_grinding`). A squeeze whose
  challenge is bad with probability at most `M/|F|` needs a proof of work that a nonce passes with probability
  `p` such that `(M/|F|) p < 2^-128`. With `g` leading zero bits, `p = 2^-g` and the prover tries `2^g` hashes,
  up to `2M`. With a threshold `T = floor((2^64 - 1)/M)` on the first eight bytes of the hash, `p = T/2^64` and
  the prover tries about `M` hashes. Flock's transcript already has this search
  (`grind_pow_below_and_sample_f128`), so its code is unchanged. BEEP-Ligerito uses it for the fold squeezes
  (`M = t + 3L`), the claim batching (`M = L + 2`) and the batching of the queries (`M = L' ceil(log2 Q)`); the
  queries keep their 16 bits. Flock's two ladders grind in whole bits, as they ship: their proofs of work are
  mostly those of the queries, and a threshold would save them at most 4 % of the opening. The variant
  `beepbits-<eta>` of the bench grinds in whole bits. On Flock's chained transcript (the one that its recursion
  replays in a circuit) a threshold falls back to bits; the bench does not use that transcript.

**Parameters** (`beep_ladder`, and the module documentation of `beep.rs`). A level with block length `n` and rate
`rho` is analyzed at agreement `s = ceil((sqrt(rho) + eta) n)` with the Johnson list bound
`L = floor(1/(2 eta sqrt(rho)))`. With `N = n - s + 1`, `m` points and an integer threshold `t >= N + 1`, the
points have error `(|F| L)^3 (mu/|F|)^m / (t (t-1) (t-N))` and the fold squeeze `(t + 3L)/|F|` (bad fold
challenges, the sumcheck round, the batching, and the points of the next round, which are drawn right after it).
For each `m <= 8` the selection takes the least `t` whose points reach 128 bits with no grinding, then the `m`
with the least fold grinding, then the fewest points. The queries (16 bits of grinding) and the challenges that
batch claims follow Flock's `JohnsonOod` accounting over GF(2^128). `beep_params.py --check` rechecks every
level in exact arithmetic: the agreement, the list, the points, the threshold, the fold grinding, the queries,
the batching, the binding samples, and every proof of work with a threshold (the largest `T` with `M T < 2^64`).
In the run below: 168 distinct levels, 88 levels of the accounting experiment and 107 levels of the affine
ladders (their fold grinding, with and without the sample on the first commitment), no failure.

**The prover's fold rounds** (`rounds_fast`, `first_pass`, `fold_pass`, `kernels`). A direct prover
(`rounds_reference`, the one of the first two versions) makes three passes per round: the answers, the round
message, and the fold, which also adds the `m` new claims to the weight. The prover now makes one pass per
round:

- the points of round `j + 1` come from the same squeeze as the fold challenge of round `j`, so the pass that
  folds the table and the weight at `r_j` also computes the round message of round `j + 1` and, for each new
  point, the inner product of every row of the folded table with the column factor of `eq(z)`;
- a claim at a point has the weight `eq(z)`, a product of a factor on the rows and a factor on the columns. The
  prover keeps the claims in this form (`Term`): the answers and the part of the claims in the later round
  messages of the level are sums over the rows of those inner products. The claims are added to the weight only
  when the table has one row left (`materialize_terms`);
- the inner loops are NEON kernels (three carry-less multiplications per product, reduction once per block),
  with portable versions that the tests compare against.

`fast_rounds_match_reference` checks that the two provers write the same proof, byte for byte. The variant
`beepref-<eta>` of the bench runs the direct prover.

**The affine ladders.** At the slack 0.02 the fold grinding of every round is the output of Flock's script
(`affine_certificates/*.txt`). That script stops its search at multiplicity 40 and degree 20000, which is too
early for a smaller slack: it reports no bound where one exists. `beep_params.py` searches further (multiplicity
up to 8064), with the formulas of Flock's script, and checks every pair that it uses with the function of that
script. `beep_params.py --affine-ladder log_n=24 k0=6 ks=4,4,4 rates=1,3,5,7` prints, per level, the least slack
of 0.001, 0.0015, 0.002, 0.003, 0.005, 0.01, 0.02 at which every fold round has a certificate, the certificates,
and the arguments of the bench (`affine_eta=`, `affine_fold=`). For 2^24 words at rate 1/2 these are the slacks
0.001, 0.002, 0.005, 0.02 with 8, 8, 7, 5 bits of fold grinding (11, 8, 7, 5 without the sample on the first
commitment, which the same command prints as `affine_fold_nf=`). A small slack needs a long code: at 0.001 only
the codes with 2^18 points or more have certificates. For 2^16 words the least slack is 0.02 at both levels (the
two affine rows coincide), and for 2^17 and 2^18 words it is 0.01 at the first level. For 2^15 words at rate 1/8
the ladder has the rates 1/8 and 1/128 (at 1/32 and 1/64 its last level has no certificate), and the least slack
is 0.02 at both levels.

**Smaller rates.** Flock ships configurations at rate 1/2 (`fast`) and 1/4 (`slim`). For the rates 1/8 and 1/16
the bench runs Ligerito (Flock) on the configuration that Flock's own derivation gives for `slim` when it starts
from that rate (`derive_profile_ladder_at_rate`, a local addition: the body of Flock's `derive_profile_ladder`
with the rate of the first level as an argument). The affine and BEEP ladders at those rates are ours.

## The affine variant as we run it

The author asked for the affine variant "at a similar level of optimization as BEEP", and without the sample on
its first commitment "so as to match beep". Both are changes of ours to Flock's affine variant. The tables of the
paper use the variant with both (`anf`), and one table has the four combinations.

### The sample on the first commitment

**What it is.** Right after the first commitment, i.e. on the input of the opening and before any fold round,
the verifier of Flock's ladders draws one random point `z` of `F^(log2 n)`, and the prover answers with the
value at `z` of the multilinear extension of the committed message. The claim "the message has this value at
`z`" is then batched with the claim that is being opened, with a random coefficient behind a proof of work, and
the fold rounds prove both.

**Why Flock has it.** The committed word is only known to be close to the code, and at a slack `eta` from the
Johnson radius up to `L = floor(1/(2 eta sqrt(rho)))` codewords can be that close (35 at rate 1/2 and slack
0.02). Two of them have the same value at a random point with probability at most `mu/|F|`, so the answer is
consistent with at most one of the `L` candidates, except with probability `C(L, 2) mu/|F|`. Flock's note then
charges each fold round `eps_aff + 2/|F|`: the bound of the affine fold, plus the two challenges per round at
which a false claim of that one candidate can become true.

**What dropping it means** (`affine_fast::without_first_sample`, which sets `ood_samples[0] = 0`). The `L`
candidates stay through the fold rounds of the first level, and each of them can have a false claim become true.
So each fold round of the first level is charged `eps_aff + 2L/|F|`, a union bound over the candidates, as in
WHIR and as in the error `kappa_2` of the paper's `t:beep_soundness`. `beep_params.py` computes the grinding
(`affine_no_first_sample`; `L` is the larger of the bound above and of the exact Johnson bound for the code of
the level, whose dimension grows by one coefficient per fold round) and `--check` redoes it for every row of a
run. It is 3 bits more per fold round at slack 0.02 (7 or 8 bits in place of 4 or 5) and 3 or 4 bits more at
the least slack (7 to 13 in place of 4 to 9). These searches run on one thread and take microseconds. The later
levels keep their samples, which bind the new commitments. Flock's prover and verifier run such a configuration
unchanged, since the number of samples per commitment is a parameter of the ladder.

**What it saves.** The prover skips the evaluation of the whole message at `z` and the addition of `eq(z)` to
the weight, i.e. two passes over tables of the size of the message, and the proof is 24 bytes smaller (the
answer and one nonce).

**Status.** This accounting is ours. It is not in Flock's note or in the affine-combiners paper, we did not
write a proof for it, and nobody has reviewed it. BEEP-Ligerito has worked without this sample since the run
20261113e, because the errors of `t:beep_soundness` carry the list.

### Our prover for the affine ladder (`affine_fast.rs`)

A fold round of the affine ladder, on a table with halves `f_0, f_1` and a weight `W`, sends the grid
`G[u][b] = <u, W_b>` for `u` in `{f_0, f_1, T f_1}` (five of its six entries; `T` multiplies each row, seen as a
polynomial in the novel basis, by `X`), and then folds `f' = f_0 + alpha f_1 + beta T f_1` and
`W' = W_0 + r (W_0 + W_1)`. Flock's dense prover (`prove_affine`) makes three passes per round (`T f_1`, the grid,
the fold), reduces every product, and allocates two tables per round. `prove_affine_fast`:

- **one pass per round**: the pass that folds the table and the weight at the challenges of a round also computes
  the grid of the next round, block by block on the folded table while the block is in cache (`fold_pass`); the
  first round of a level has a pass of its own, which only reads (`first_grid`);
- **`T` on the fly**: `(T g)_c` is `g_(c-1) + g_c` at an odd column and `P_z (g_(c-1) + g_(c + 2^z - 1))` at an
  even one (`z` the trailing zeros of `c`), so `T f_1` is never stored: the fold reads two columns, and the grid
  accumulates the sums per value of `z` and multiplies by `P_z` at the end of the pass;
- **five grid entries**, the sixth from the claim; **deferred reduction** and **NEON kernels** (three carry-less
  multiplications per product, as in `beep.rs`); **buffers from Flock's pool**; and a cache hint for the output
  blocks that the pass overwrites (`DC ZVA`), which `beep.rs` now has as well.

It writes the same proof as `prove_affine`, byte for byte: `affine_fast::tests::fast_matches_flock` checks eight
small ladders, and the bench checks every cell before it times it. Flock's `verify_affine` is the verifier.

**A defect that the run 20261114f had.** The first version of this prover gave its last table and its last
weight back to Flock's buffer pool. The bench hands every proof a fresh copy of the message and of the basis,
which the prover gives to the pool in its first round, so the pool grew by two buffers per proof, up to its
limit of 48 buffers of the size of the message: 12 GiB for 2^24 words and 24 GiB for 2^25. The processes with
the four affine provers of the large instances ran short of memory (peak footprints of 13 to 26 GiB on a
24 GB machine) and their times are useless: thousands of page faults per proof. The prover now ends as
`beep.rs` does (the last table goes into the proof, the last weight is dropped), and the same processes take
2.6 GiB at 2^24 words and 5.1 GiB at 2^25 (the run 20261114g). `make_tables.py` now warns when a prover of ours
takes more than a hundred page faults per proof.

**The variants of the bench** (`variants=`):

| variant | what it is |
|---|---|
| `split` | Flock's Ligerito as it ships |
| `affine`, `affine-small` | Flock's affine variant as it ships (its prover, a sample on the first commitment), at slack 0.02 and at its least slack |
| `afast`, `afast-small` | the same configurations and the same proofs, with our prover |
| `anfref`, `anfref-small` | no sample on the first commitment, with Flock's prover |
| `anf`, `anf-small` | no sample on the first commitment, with our prover: the affine variant of the paper's tables |
| `beep-<eta>` | BEEP-Ligerito: no sample on the first commitment, one pass per round, proofs of work with a threshold |
| `beepb-<eta>` | the same with the sample on the first commitment |
| `beepref-<eta>` | the same configuration as `beep`, with the direct prover |
| `beepbits-<eta>` | the same as `beep`, with proofs of work of a whole number of bits |
| `beepold-<eta>` | the three undone: BEEP-Ligerito as in the runs 20261113b and 20261113c |
| `control-<eta>` | `beep` with no points per fold round: a timing control, not a sound configuration |
| `beepaff-<eta>` | `beep` with its fold challenges ground for the error of the affine fold (`beepaff=<eta>:<bits per level>`): an accounting experiment, not a sound configuration |

## Reproducing

Every cargo command sets this folder's own target directory: the shell exports a `CARGO_TARGET_DIR` that belongs
to another project (see the root `README.md`).

```sh
cd ~/BEEP/7-beep-ligerito/flock
export CARGO_TARGET_DIR=$PWD/../target RUSTFLAGS="-C target-cpu=native"
cargo test --offline --release -p flock-core --lib beep            # the 13 tests of beep.rs
cargo test --offline --release -p flock-core --lib affine_fast     # the 3 tests of affine_fast.rs
cargo test --offline --release -p flock-core --lib pcs::ligerito   # 97 tests (1 ignored): Flock's own Ligerito tests and ours
cargo bench --offline -p flock-core --bench ligerito_three_way --no-run
# one cell by hand (a smoke run, not a measurement):
$CARGO_TARGET_DIR/release/deps/ligerito_three_way-* log_n=20 rates=1,3,6 fold=4,5,5 fold_nf=7,5,5 \
  affine_eta=0.003,0.01,0.02 affine_fold=6,6,5 affine_fold_nf=10,6,5 eta=0.02,0.001 \
  variants=split,affine,afast,anfref,anf,anf-small,beep,control reps=3
```

The timed run, from a terminal outside any sandbox, on AC power, with a new label (the driver refuses an existing
folder). It takes about an hour once the machine is idle (66 processes). Check first that the machine has
about 10 GB of unused memory (`top -l 1 -n 0 | grep PhysMem`): a machine that is short of memory gives proofs
with bursts of page faults (see "The timing of Flock's affine prover"):

```sh
cd ~/BEEP/7-beep-ligerito
python3 scripts/bench_gate.py run --label beep-three-way-<label> --min-idle 80 --hold-seconds 60 -- \
  zsh scripts/run_cells.zsh <label>
python3 scripts/collect.py bench_results/three-way-<label>
python3 scripts/beep_params.py --check bench_results/three-way-<label>/results.json
(cd ../typst && python3 scripts/make_tables.py --results ../7-beep-ligerito/bench_results/three-way-<label>/results.json)
python3 scripts/readme_tables.py        # the tables of this file
```

The same at 100 bits: `python3 scripts/make_cells100.py` writes `scripts/cells100.txt` from `scripts/cells.txt`,
and the driver takes it as its second argument (`zsh scripts/run_cells.zsh <label> $PWD/scripts/cells100.txt`).
`make_tables.py` reads that run as its second run (`--results100`), for the tables `params100` and `main100`.
On a machine that is in use, `zsh scripts/when_memory_is_free.zsh 9 50000 -- <the gate command>` starts the
campaign once 9 GB of memory are unused, and `CAMPAIGN_IDLE_EACH=1` checks the idle CPU before every cell.
(On November 14 this watcher never saw 9 GB. The run 100bits-3 was started by hand at night, with 3 to 5.5 GB
unused, after a smoke run of two large cells showed the median times of the run at 128 bits, in one of them
with part of its memory compressed; `make_tables.py` then decides which of its times can be used, with a rule
that is looser than the guard of the run at 128 bits. See "The run at 100 bits".)

One more shape for a run that exists takes its own cells file and the label `<label>-add<k>` (for example
`scripts/cells_add_g1.txt`), with the same bench binary: `make_tables.py` adds the rows of such a folder for the
shapes that the run does not have, and a later folder replaces an earlier one. With `CAMPAIGN_IDLE_EACH=1` the
driver waits for the idle condition of the gate before every cell, for a run while the machine is in use.

A rerun of some cells takes its own cells file and the label `<label>-rerun<something>` (for example
`scripts/cells_rerun_e1.txt`). `make_tables.py` reads every such folder next to a run that used the same bench
binary, and it takes a process of the rerun (with or without proofs of work) where the process of the run had
part of its memory compressed and that of the rerun did not.

## The run 20261114g (November 14, 2026)

Apple M5 (4 performance and 6 efficiency cores), 24 GB, 10 threads, AC power, through the gate (80 % idle CPU for
60 s before the first cell), 45 s of cool-down before each cell, 9 timed repetitions after a warm-up, medians;
03:07 to 04:06. Fourteen instances: 2^16, 2^17, 2^18, 2^20, 2^22, 2^24 and 2^25 words at rate 1/2, 2^22 and
2^24 words at the rates 1/4, 1/8 and 1/16, and 2^15 words at rate 1/8 (added later, see below). For each
instance up to 2^22 words, one process runs all the provers
one after the other on the same commitment (23 variants), and a second process runs them with
`FLOCK_NO_GRIND=1`. For 2^24 and 2^25 words the variants are split over five pairs
of processes (split; the four affine provers at 0.02; the four at their least slack; the BEEP variants at 0.02;
the BEEP variants at 0.001), since for the largest instances the provers do not fit together in 24 GB.

No process had part of its memory compressed (the largest peak footprint is 7.2 GiB), and no
rerun is used. The exact recheck passes: 168 distinct BEEP levels, 88 of the accounting experiment, and 107
levels of the affine ladders (with and without the sample on the first commitment), no failure.

**The instance with 2^15 words at rate 1/8** was asked for after the run ("numbers for n=2^15 and rate 1/8 for
table 4"; we read `n` as the number of words of the message) and measured on its own the same morning, with the
same bench binary and the same driver (`scripts/cells_add_g1.txt`). The machine was in use, so the measurement
that the tables use, `three-way-20261114g-add2` (09:18), waits for the idle condition of the gate before each of
its two cells (`CAMPAIGN_IDLE_EACH=1`). `three-way-20261114g-add1` (09:09) and `three-way-check-20261114g-add1`
(09:13) are two earlier measurements of the same cells without that condition. The three agree within 0.2 ms on
"prove" for every row of the tables, except the affine row at slack 0.02 of the check run (1.91 ms, against 1.66
and 1.73), whose process without proofs of work started on a machine that was 53 % idle. Its exact recheck
passes as well (10 BEEP levels, 4 of the accounting experiment, 3 of the affine ladder). `make_tables.py` adds
the rows of a folder `<run>-add*` with the binary of the run for the shapes that the run does not have; a later
folder replaces an earlier one.

"prove" is the time without proofs of work plus the proofs of work at their expected cost: for each search, the
mean time of 128 to 4096 searches of the same difficulty that the bench times in the process with proofs of
work, corrected to its expected number of hashes. The commitment is the same for all the variants and is not
included (1.0 ms at 2^16 words, 95.2 ms at 2^24 words and rate 1/2,
712 ms at 2^24 words and rate 1/16).

In the tables, "affine" is the affine variant as we run it (`anf`, `anf-small`): no sample on the first
commitment, our prover. Flock's affine variant as it ships is in the table of the next subsection.

<!-- main: scripts/readme_tables.py main, from 7-beep-ligerito/bench_results/three-way-20261114g/results.json -->
| words | rate | variant | proof (KiB) | prove (ms) | no grinding (ms) | grinding (10^6 hashes) | verify (ms) |
|---|---|---|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | Ligerito (Flock) | 347.6 | 2.9 | 1.8 | 0.20 | 0.73 |
| 2^16 | 1/2 | affine, eta = 0.02 | 304.2 | 1.8 | 1.0 | 0.13 | 0.49 |
| 2^16 | 1/2 | affine, least eta | 304.2 | 1.8 | 1.0 | 0.13 | 0.50 |
| 2^16 | 1/2 | BEEP, eta = 0.02 | 301.6 | 2.6 | 1.3 | 0.16 | 0.48 |
| 2^16 | 1/2 | BEEP, eta = 0.001 | 279.0 | 3.2 | 1.2 | 0.25 | 0.45 |
| 2^17 | 1/2 | Ligerito (Flock) | 361.9 | 3.5 | 2.4 | 0.20 | 0.92 |
| 2^17 | 1/2 | affine, eta = 0.02 | 315.0 | 2.1 | 1.3 | 0.13 | 0.56 |
| 2^17 | 1/2 | affine, least eta | 302.3 | 2.1 | 1.3 | 0.13 | 0.54 |
| 2^17 | 1/2 | BEEP, eta = 0.02 | 313.5 | 2.8 | 1.5 | 0.16 | 0.55 |
| 2^17 | 1/2 | BEEP, eta = 0.001 | 290.3 | 3.5 | 1.6 | 0.23 | 0.52 |
| 2^18 | 1/2 | Ligerito (Flock) | 395.3 | 5.5 | 4.1 | 0.27 | 0.86 |
| 2^18 | 1/2 | affine, eta = 0.02 | 325.0 | 3.0 | 2.3 | 0.13 | 0.64 |
| 2^18 | 1/2 | affine, least eta | 312.7 | 3.1 | 2.3 | 0.14 | 0.62 |
| 2^18 | 1/2 | BEEP, eta = 0.02 | 324.5 | 4.3 | 2.6 | 0.18 | 0.64 |
| 2^18 | 1/2 | BEEP, eta = 0.001 | 300.7 | 4.8 | 2.7 | 0.25 | 0.61 |
| 2^20 | 1/2 | Ligerito (Flock) | 427.4 | 9.9 | 8.4 | 0.27 | 1.19 |
| 2^20 | 1/2 | affine, eta = 0.02 | 370.8 | 5.7 | 4.6 | 0.20 | 0.76 |
| 2^20 | 1/2 | affine, least eta | 348.6 | 6.0 | 4.7 | 0.21 | 0.74 |
| 2^20 | 1/2 | BEEP, eta = 0.02 | 371.7 | 8.0 | 5.3 | 0.30 | 0.75 |
| 2^20 | 1/2 | BEEP, eta = 0.001 | 345.1 | 8.9 | 5.7 | 0.42 | 0.72 |
| 2^22 | 1/2 | Ligerito (Flock) | 373.4 | 26.3 | 24.4 | 0.33 | 1.30 |
| 2^22 | 1/2 | affine, eta = 0.02 | 303.1 | 14.8 | 13.3 | 0.27 | 0.78 |
| 2^22 | 1/2 | affine, least eta | 284.9 | 15.2 | 13.2 | 0.29 | 0.76 |
| 2^22 | 1/2 | BEEP, eta = 0.02 | 303.7 | 20.9 | 15.1 | 0.87 | 0.75 |
| 2^22 | 1/2 | BEEP, eta = 0.001 | 283.3 | 22.3 | 15.2 | 1.14 | 0.74 |
| 2^24 | 1/2 | Ligerito (Flock) | 528.8 | 71.5 | 69.2 | 0.40 | 1.33 |
| 2^24 | 1/2 | affine, eta = 0.02 | 438.5 | 34.1 | 32.5 | 0.27 | 0.96 |
| 2^24 | 1/2 | affine, least eta | 409.4 | 34.3 | 32.1 | 0.30 | 0.92 |
| 2^24 | 1/2 | BEEP, eta = 0.02 | 439.2 | 48.2 | 39.0 | 1.59 | 0.95 |
| 2^24 | 1/2 | BEEP, eta = 0.001 | 408.1 | 50.4 | 39.0 | 1.98 | 0.90 |
| 2^25 | 1/2 | Ligerito (Flock) | 547.5 | 134 | 132 | 0.40 | 1.46 |
| 2^25 | 1/2 | affine, eta = 0.02 | 451.6 | 60.5 | 58.9 | 0.27 | 1.07 |
| 2^25 | 1/2 | affine, least eta | 420.7 | 62.0 | 59.8 | 0.31 | 1.03 |
| 2^25 | 1/2 | BEEP, eta = 0.02 | 452.9 | 88.8 | 73.3 | 2.92 | 1.05 |
| 2^25 | 1/2 | BEEP, eta = 0.001 | 420.9 | 91.5 | 73.2 | 3.31 | 1.00 |
| 2^22 | 1/4 | Ligerito (Flock) | 216.8 | 43.9 | 41.8 | 0.34 | 0.93 |
| 2^22 | 1/4 | affine, eta = 0.02 | 191.9 | 18.3 | 16.7 | 0.27 | 0.57 |
| 2^22 | 1/4 | affine, least eta | 183.4 | 19.2 | 16.8 | 0.31 | 0.55 |
| 2^22 | 1/4 | BEEP, eta = 0.02 | 192.9 | 29.9 | 18.6 | 2.07 | 0.57 |
| 2^22 | 1/4 | BEEP, eta = 0.001 | 183.2 | 33.0 | 18.9 | 2.42 | 0.55 |
| 2^24 | 1/4 | Ligerito (Flock) | 299.6 | 101 | 98.4 | 0.43 | 1.00 |
| 2^24 | 1/4 | affine, eta = 0.02 | 259.8 | 40.3 | 38.7 | 0.27 | 0.68 |
| 2^24 | 1/4 | affine, least eta | 247.4 | 40.8 | 38.2 | 0.33 | 0.64 |
| 2^24 | 1/4 | BEEP, eta = 0.02 | 261.1 | 67.4 | 45.2 | 4.35 | 0.66 |
| 2^24 | 1/4 | BEEP, eta = 0.001 | 247.6 | 71.8 | 45.4 | 4.84 | 0.65 |
| 2^15 | 1/8 | Ligerito (Flock)* | 134.8 | 3.0 | 1.7 | 0.20 | 0.39 |
| 2^15 | 1/8 | affine, eta = 0.02 | 116.5 | 1.7 | 0.9 | 0.13 | 0.26 |
| 2^15 | 1/8 | affine, least eta | 116.5 | 1.7 | 0.9 | 0.13 | 0.26 |
| 2^15 | 1/8 | BEEP, eta = 0.02 | 115.4 | 2.8 | 0.9 | 0.18 | 0.25 |
| 2^15 | 1/8 | BEEP, eta = 0.001 | 110.1 | 3.8 | 1.0 | 0.31 | 0.24 |
| 2^22 | 1/8 | Ligerito (Flock)* | 173.1 | 63.1 | 60.9 | 0.36 | 0.79 |
| 2^22 | 1/8 | affine, eta = 0.02 | 149.6 | 25.1 | 23.5 | 0.27 | 0.48 |
| 2^22 | 1/8 | affine, least eta | 142.2 | 26.1 | 23.3 | 0.35 | 0.46 |
| 2^22 | 1/8 | BEEP, eta = 0.02 | 150.6 | 51.4 | 25.5 | 4.71 | 0.50 |
| 2^22 | 1/8 | BEEP, eta = 0.001 | 142.3 | 55.3 | 25.7 | 5.34 | 0.49 |
| 2^24 | 1/8 | Ligerito (Flock)* | 234.1 | 148 | 145 | 0.45 | 0.84 |
| 2^24 | 1/8 | affine, eta = 0.02 | 195.7 | 55.0 | 53.4 | 0.27 | 0.58 |
| 2^24 | 1/8 | affine, least eta | 186.0 | 56.5 | 53.6 | 0.36 | 0.55 |
| 2^24 | 1/8 | BEEP, eta = 0.02 | 196.9 | 110 | 60.7 | 10.44 | 0.59 |
| 2^24 | 1/8 | BEEP, eta = 0.001 | 185.9 | 117 | 60.1 | 11.59 | 0.55 |
| 2^22 | 1/16 | Ligerito (Flock)* | 153.2 | 94.2 | 91.9 | 0.36 | 0.77 |
| 2^22 | 1/16 | affine, eta = 0.02 | 130.2 | 35.9 | 34.2 | 0.27 | 0.46 |
| 2^22 | 1/16 | affine, least eta | 122.4 | 37.3 | 34.3 | 0.39 | 0.43 |
| 2^22 | 1/16 | BEEP, eta = 0.02 | 131.2 | 88.0 | 36.1 | 10.35 | 0.48 |
| 2^22 | 1/16 | BEEP, eta = 0.001 | 122.5 | 93.7 | 36.2 | 11.22 | 0.44 |
| 2^24 | 1/16 | Ligerito (Flock)* | 203.7 | 216 | 213 | 0.46 | 0.79 |
| 2^24 | 1/16 | affine, eta = 0.02 | 165.8 | 88.3 | 86.6 | 0.27 | 0.52 |
| 2^24 | 1/16 | affine, least eta | 155.6 | 86.2 | 82.7 | 0.43 | 0.49 |
| 2^24 | 1/16 | BEEP, eta = 0.02 | 166.9 | 202 | 91.2 | 23.46 | 0.52 |
| 2^24 | 1/16 | BEEP, eta = 0.001 | 156.2 | 218 | 90.0 | 25.07 | 0.51 |

In short:

- **Proof size.** At the same slack 0.02 the proofs of BEEP-Ligerito and of the affine variant differ by at
  most 2.6 KiB. A smaller slack saves 5 to 8 %, and for
  long messages this is available to both: for 2^20 words and more, BEEP-Ligerito at 0.001 is
  0.99 to 1.00 times the affine variant at its least slack. The first level makes
  39 to 91 % of a proof, it is the longest code, and there the affine fold also has a bound at a small
  slack. For short messages it has not: at 2^16, 2^17 and 2^18 words BEEP-Ligerito at 0.001 is
  8 %, 4 % and
  4 % smaller than the affine variant at its least slack. Both are
  11 to 19 % smaller than Flock's Ligerito at slack 0.02, whose ladder has more levels and
  more queries after the first level.
- **Prover.** With the proofs of work at their expected cost, BEEP-Ligerito is slower than the affine variant
  in every instance: 1.37 to 1.47 times as long at rate 1/2 and slack 0.02
  (1.47 to 1.76 at the small slacks), and 1.61 to 2.45 times
  at the rates 1/4 to 1/16 (1.72 to 2.53). For 2^24 words at rate 1/2:
  48.2 ms against 34.1 ms.
- **Two reasons.** The samples: without proofs of work BEEP-Ligerito takes 1.00 to 1.25 times
  as long as the affine variant, because its fold rounds take 1.33 to 1.46 times as
  long for 2^20 words and more (27.4 ms against 20.7 ms
  at 2^24 words and rate 1/2; 18.7 ms for the control with no samples). And the grinding:
  its proofs of work try 1.2 to 10.9 times as many hashes at rate 1/2 and
  1.4 to 85.5 times as many at the smaller rates (a fold challenge needs about
  `log2(delta n)` bits: 9.4 to 21.5 against 5 to 8 for the affine fold at 0.02).
- **Against Flock's affine variant as it ships** (the comparison of the run 20261113e): BEEP-Ligerito at 0.02
  takes 0.89 to 0.90 times as long for 2^24 and 2^25 words at rate 1/2, and
  0.89 to 2.19 times over all the instances. So the "parity" of that run for long messages at
  rate 1/2 came from the unequal optimization and from the sample on the first commitment, as its README
  warned. With our prover and with the sample (`afast`), the affine variant takes about as long as
  BEEP-Ligerito without proofs of work (BEEP takes 0.92 to 1.10 times as long) and less with
  them (1.19 to 2.35).
- **With the sample on the first commitment in both variants** (`beepb` against `afast`): BEEP-Ligerito takes
  1.37 to 2.42 times as long at 0.02. So the conclusion does not rest on our accounting for
  the first level of the affine variant.
- **Against Flock's Ligerito**: BEEP-Ligerito takes 0.66 to 0.94 times as long at 0.02, and the
  affine variant 0.37 to 0.62 times (Flock's affine variant as it ships:
  0.43 to 0.75 times). Ligerito (Flock) runs Flock's prover with a sample on its first commitment,
  so this is not like for like either.
- **The shortest instance, 2^15 words at rate 1/8.** Its ladder has two levels, at the rates 1/8 and 1/128, both
  with codes of 2^12 points. The affine fold has no certificate below the slack 0.02 at either level, so its two
  rows coincide, and BEEP-Ligerito at 0.001 is 6 % smaller
  (110.1 KiB against 116.5 KiB). Its prover takes
  1.61 times as long as the affine one at 0.02 and
  2.25 times at 0.001 (2.8 and
  3.8 ms against 1.7 ms), and this is all proofs of work: without
  them the two take the same time (0.9 and 0.9 ms at 0.02).
- **Verifier.** 0.97 to 1.04 times the affine one at 0.02.
- **Where the bytes go.** Merkle leaves (the opened columns) are 40 to 85 % of a proof and inner paths
  13 to 55 %; everything else is 4.6 to 14.5 KiB. The answers to the samples of BEEP are
  1.2 to 2.5 KiB. The paper's Tables 5 and 6 have the split per level and per variant.

### What our two changes give the affine variant

The prover time (ms, proofs of work at their expected cost) of Flock's affine variant as it ships (`affine`),
with our prover (`afast`; the same proofs), without the sample on the first commitment (`anfref`; Flock's
prover), and with both (`anf`, the affine variant of the other tables); at slack 0.02 and at the least slack of
each level. The last column is BEEP-Ligerito, at 0.02 in the rows of 0.02 and at 0.001 in the others.

<!-- asteps: scripts/readme_tables.py asteps, from 7-beep-ligerito/bench_results/three-way-20261114g/results.json -->
| words | rate | eta | affine as Flock ships it | our prover | no first sample | both (the tables) | BEEP |
|---|---|---|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | 0.02 | 2.1 | 1.9 | 2.0 | 1.8 | 2.6 |
| 2^16 | 1/2 | least | 2.1 | 1.9 | 2.0 | 1.8 | 3.2 |
| 2^17 | 1/2 | 0.02 | 2.5 | 2.1 | 2.4 | 2.1 | 2.8 |
| 2^17 | 1/2 | least | 2.5 | 2.2 | 2.4 | 2.1 | 3.5 |
| 2^18 | 1/2 | 0.02 | 3.6 | 3.1 | 3.4 | 3.0 | 4.3 |
| 2^18 | 1/2 | least | 3.5 | 3.2 | 3.4 | 3.1 | 4.8 |
| 2^20 | 1/2 | 0.02 | 7.2 | 6.1 | 6.8 | 5.7 | 8.0 |
| 2^20 | 1/2 | least | 7.1 | 6.1 | 6.9 | 6.0 | 8.9 |
| 2^22 | 1/2 | 0.02 | 19.7 | 16.5 | 18.0 | 14.8 | 20.9 |
| 2^22 | 1/2 | least | 19.6 | 16.4 | 18.2 | 15.2 | 22.3 |
| 2^24 | 1/2 | 0.02 | 53.4 | 40.4 | 47.2 | 34.1 | 48.2 |
| 2^24 | 1/2 | least | 53.0 | 40.3 | 47.2 | 34.3 | 50.4 |
| 2^25 | 1/2 | 0.02 | 99.2 | 72.7 | 86.8 | 60.5 | 88.8 |
| 2^25 | 1/2 | least | 101 | 73.6 | 89.5 | 62.0 | 91.5 |
| 2^22 | 1/4 | 0.02 | 23.2 | 19.7 | 21.3 | 18.3 | 29.9 |
| 2^22 | 1/4 | least | 23.3 | 20.3 | 22.0 | 19.2 | 33.0 |
| 2^24 | 1/4 | 0.02 | 59.4 | 45.8 | 53.0 | 40.3 | 67.4 |
| 2^24 | 1/4 | least | 59.1 | 46.8 | 53.8 | 40.8 | 71.8 |
| 2^15 | 1/8 | 0.02 | 1.9 | 1.8 | 1.8 | 1.7 | 2.8 |
| 2^15 | 1/8 | least | 1.9 | 1.8 | 1.8 | 1.7 | 3.8 |
| 2^22 | 1/8 | 0.02 | 29.7 | 26.5 | 28.2 | 25.1 | 51.4 |
| 2^22 | 1/8 | least | 30.4 | 27.2 | 29.1 | 26.1 | 55.3 |
| 2^24 | 1/8 | 0.02 | 74.1 | 61.3 | 67.7 | 55.0 | 110 |
| 2^24 | 1/8 | least | 75.9 | 62.9 | 69.3 | 56.5 | 117 |
| 2^22 | 1/16 | 0.02 | 40.2 | 37.5 | 38.6 | 35.9 | 88.0 |
| 2^22 | 1/16 | least | 41.3 | 38.5 | 40.1 | 37.3 | 93.7 |
| 2^24 | 1/16 | 0.02 | 107 | 96.2 | 100 | 88.3 | 202 |
| 2^24 | 1/16 | least | 105 | 93.4 | 99.6 | 86.2 | 218 |

For 2^24 words at rate 1/2 and slack 0.02: 53.4 ms as it ships,
40.4 ms with our prover, 47.2 ms without the sample,
34.1 ms with both. Our prover is worth 13.0 ms there: its
fold rounds take 20.9 ms, against about 33.9 ms
for Flock's (Flock's prover does not time its phases; this is ours plus the difference of the two openings).
The sample is worth 6.3 ms. Over all the instances the opening takes
6 to 27 % less time with our prover, a further 3 to 17 % less
without the sample, and 8 to 39 % less with both (36 to 39 % for
2^24 and 2^25 words at rate 1/2). Both changes act on the first level, so they matter less at small rates,
where the commitments of the next levels take most of the opening. Without the sample the proofs of work try
0 to 1 % more hashes at slack 0.02 (rounded) and 0 to 11 % more at the least slack.

### What each change gives BEEP-Ligerito

The prover time of BEEP-Ligerito (ms, proofs of work at their expected cost), and the same with one of its three
choices undone: with the sample on the first commitment (`beepb`), with the direct prover (`beepref`), with
proofs of work of a whole number of bits (`beepbits`); with all three undone (`beepold`); and the affine variant
(at 0.02 in the rows with 0.02, at its least slack in the others).

<!-- steps: scripts/readme_tables.py steps, from 7-beep-ligerito/bench_results/three-way-20261114g/results.json -->
| words | rate | eta | BEEP | first sample | three passes | whole bits | all three | affine |
|---|---|---|---:|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | 0.02 | 2.6 | 2.6 | 2.8 | 2.5 | 2.8 | 1.8 |
| 2^16 | 1/2 | 0.001 | 3.2 | 3.3 | 3.3 | 3.4 | 3.7 | 1.8 |
| 2^17 | 1/2 | 0.02 | 2.8 | 3.0 | 3.2 | 2.9 | 3.4 | 2.1 |
| 2^17 | 1/2 | 0.001 | 3.5 | 3.7 | 3.8 | 3.7 | 4.2 | 2.1 |
| 2^18 | 1/2 | 0.02 | 4.3 | 4.5 | 4.9 | 4.1 | 4.9 | 3.0 |
| 2^18 | 1/2 | 0.001 | 4.8 | 5.1 | 5.4 | 4.9 | 5.7 | 3.1 |
| 2^20 | 1/2 | 0.02 | 8.0 | 8.5 | 9.7 | 7.9 | 10.3 | 5.7 |
| 2^20 | 1/2 | 0.001 | 8.9 | 9.5 | 10.9 | 9.2 | 11.8 | 6.0 |
| 2^22 | 1/2 | 0.02 | 20.9 | 23.6 | 27.3 | 21.7 | 30.2 | 14.8 |
| 2^22 | 1/2 | 0.001 | 22.3 | 24.7 | 28.6 | 23.6 | 32.0 | 15.2 |
| 2^24 | 1/2 | 0.02 | 48.2 | 56.7 | 74.0 | 50.8 | 84.9 | 34.1 |
| 2^24 | 1/2 | 0.001 | 50.4 | 58.7 | 75.5 | 52.8 | 86.8 | 34.3 |
| 2^25 | 1/2 | 0.02 | 88.8 | 106 | 141 | 93.5 | 163 | 60.5 |
| 2^25 | 1/2 | 0.001 | 91.5 | 108 | 143 | 95.0 | 164 | 62.0 |
| 2^22 | 1/4 | 0.02 | 29.9 | 32.2 | 36.5 | 30.1 | 38.8 | 18.3 |
| 2^22 | 1/4 | 0.001 | 33.0 | 35.2 | 39.2 | 36.9 | 45.5 | 19.2 |
| 2^24 | 1/4 | 0.02 | 67.4 | 76.4 | 92.7 | 68.1 | 103 | 40.3 |
| 2^24 | 1/4 | 0.001 | 71.8 | 80.6 | 97.2 | 83.0 | 118 | 40.8 |
| 2^15 | 1/8 | 0.02 | 2.8 | 2.8 | 3.0 | 2.6 | 2.9 | 1.7 |
| 2^15 | 1/8 | 0.001 | 3.8 | 3.9 | 4.0 | 3.6 | 4.0 | 1.7 |
| 2^22 | 1/8 | 0.02 | 51.4 | 54.0 | 57.9 | 58.4 | 66.8 | 25.1 |
| 2^22 | 1/8 | 0.001 | 55.3 | 57.7 | 62.1 | 61.9 | 70.4 | 26.1 |
| 2^24 | 1/8 | 0.02 | 110 | 118 | 135 | 126 | 159 | 55.0 |
| 2^24 | 1/8 | 0.001 | 117 | 125 | 143 | 132 | 166 | 56.5 |
| 2^22 | 1/16 | 0.02 | 88.0 | 90.8 | 94.4 | 95.7 | 105 | 35.9 |
| 2^22 | 1/16 | 0.001 | 93.7 | 96.2 | 100 | 100 | 109 | 37.3 |
| 2^24 | 1/16 | 0.02 | 202 | 211 | 228 | 222 | 256 | 88.3 |
| 2^24 | 1/16 | 0.001 | 218 | 227 | 245 | 234 | 269 | 86.2 |

For 2^24 words at rate 1/2 and slack 0.02: 84.9 ms with the three undone
(1.59 times Flock's affine variant as it ships, which has none of the three
either), 48.2 ms now. The one pass is worth 25.7 ms there, the
sample on the first commitment 8.5 ms, the threshold 2.6 ms.
The threshold matters at the rates 1/8 and 1/16 (9 to 15 % at slack 0.02;
19.6 ms for 2^24 words at rate 1/16). For the short messages the direct prover is
7 to 13 % slower, and the other two choices change the time by a few tenths of a
millisecond at most, within the noise of the measurements. The column "affine" is the affine variant as we run
it, which compares with the column "BEEP".

Where the time goes without proofs of work (ms). "samples" is the time of the fold rounds of BEEP-Ligerito
minus that of the control with no points; "affine" has the fold rounds and the whole opening of the affine
variant (at 0.02 in the rows with 0.02, at its least slack in the others):

<!-- time: scripts/readme_tables.py time, from 7-beep-ligerito/bench_results/three-way-20261114g/results.json -->
| words | rate | eta | samples | folds | rest | total | control | affine: folds | affine: total | fold grinding (10^6 hashes) | all grinding (ms) |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | 0.02 | 0.4 | 0.3 | 0.6 | 1.3 | 0.8 | 0.3 | 1.0 | 0.03 | 1.3 |
| 2^16 | 1/2 | 0.001 | 0.3 | 0.3 | 0.6 | 1.2 | 0.9 | 0.3 | 1.0 | 0.08 | 2.0 |
| 2^17 | 1/2 | 0.02 | 0.4 | 0.4 | 0.7 | 1.5 | 1.1 | 0.5 | 1.3 | 0.03 | 1.3 |
| 2^17 | 1/2 | 0.001 | 0.5 | 0.4 | 0.7 | 1.6 | 1.1 | 0.5 | 1.3 | 0.07 | 1.9 |
| 2^18 | 1/2 | 0.02 | 0.6 | 0.6 | 1.4 | 2.6 | 2.0 | 0.7 | 2.3 | 0.05 | 1.7 |
| 2^18 | 1/2 | 0.001 | 0.7 | 0.6 | 1.4 | 2.7 | 2.0 | 0.7 | 2.3 | 0.09 | 2.1 |
| 2^20 | 1/2 | 0.02 | 1.2 | 1.5 | 2.6 | 5.3 | 4.1 | 1.8 | 4.6 | 0.10 | 2.7 |
| 2^20 | 1/2 | 0.001 | 1.6 | 1.5 | 2.6 | 5.7 | 4.1 | 1.8 | 4.7 | 0.17 | 3.2 |
| 2^22 | 1/2 | 0.02 | 2.8 | 5.0 | 7.3 | 15.1 | 12.2 | 5.8 | 13.3 | 0.61 | 5.8 |
| 2^22 | 1/2 | 0.001 | 3.0 | 5.0 | 7.3 | 15.2 | 12.0 | 5.8 | 13.2 | 0.80 | 7.1 |
| 2^24 | 1/2 | 0.02 | 8.8 | 18.7 | 11.5 | 39.0 | 29.9 | 20.7 | 32.5 | 1.33 | 9.2 |
| 2^24 | 1/2 | 0.001 | 9.0 | 18.5 | 11.5 | 39.0 | 29.7 | 20.6 | 32.1 | 1.63 | 11.4 |
| 2^25 | 1/2 | 0.02 | 17.1 | 36.7 | 19.5 | 73.3 | 55.7 | 39.5 | 58.9 | 2.65 | 15.4 |
| 2^25 | 1/2 | 0.001 | 17.4 | 36.6 | 19.2 | 73.2 | 55.6 | 40.0 | 59.8 | 2.96 | 18.3 |
| 2^22 | 1/4 | 0.02 | 3.1 | 5.0 | 10.5 | 18.6 | 15.3 | 6.0 | 16.7 | 1.80 | 11.4 |
| 2^22 | 1/4 | 0.001 | 3.3 | 5.1 | 10.5 | 18.9 | 15.5 | 6.1 | 16.8 | 2.04 | 14.1 |
| 2^24 | 1/4 | 0.02 | 9.0 | 18.4 | 17.7 | 45.2 | 37.3 | 20.4 | 38.7 | 4.08 | 22.2 |
| 2^24 | 1/4 | 0.001 | 9.1 | 18.5 | 17.8 | 45.4 | 36.0 | 20.4 | 38.2 | 4.47 | 26.4 |
| 2^15 | 1/8 | 0.02 | 0.2 | 0.2 | 0.5 | 0.9 | 0.7 | 0.2 | 0.9 | 0.05 | 1.9 |
| 2^15 | 1/8 | 0.001 | 0.3 | 0.2 | 0.5 | 1.0 | 0.7 | 0.3 | 0.9 | 0.12 | 2.8 |
| 2^22 | 1/8 | 0.02 | 3.4 | 5.0 | 17.2 | 25.5 | 22.1 | 6.0 | 23.5 | 4.44 | 25.8 |
| 2^22 | 1/8 | 0.001 | 3.3 | 5.1 | 17.3 | 25.7 | 22.0 | 5.9 | 23.3 | 4.91 | 29.5 |
| 2^24 | 1/8 | 0.02 | 8.9 | 18.8 | 32.9 | 60.7 | 51.6 | 20.6 | 53.4 | 10.17 | 49.0 |
| 2^24 | 1/8 | 0.001 | 8.8 | 18.5 | 32.7 | 60.1 | 50.8 | 20.5 | 53.6 | 11.17 | 56.6 |
| 2^22 | 1/16 | 0.02 | 3.0 | 5.0 | 28.1 | 36.1 | 33.5 | 5.9 | 34.2 | 10.08 | 51.9 |
| 2^22 | 1/16 | 0.001 | 3.1 | 5.0 | 28.1 | 36.2 | 32.8 | 6.0 | 34.3 | 10.75 | 57.5 |
| 2^24 | 1/16 | 0.02 | 9.1 | 18.7 | 63.4 | 91.2 | 81.8 | 20.8 | 86.6 | 23.19 | 111 |
| 2^24 | 1/16 | 0.001 | 9.0 | 18.6 | 62.4 | 90.0 | 80.5 | 20.6 | 82.7 | 24.60 | 128 |

The samples cost 8 to 31 % of the opening without proofs of work
(2.4 to 4.1 times as much with the direct prover, for 2^20 words and more). The
fold rounds of the affine variant take 1.07 to 1.25 times as long as those of
the control for 2^20 words and more, and those of BEEP-Ligerito 1.33 to 1.46 times
as long as those of the affine variant. The proofs of work are the larger cost of BEEP-Ligerito in most
instances: 17 to 68 % of the opening at slack 0.02, against 2 to 20 %
for the affine variant for 2^20 words and more.

### The fold challenge at the error of the affine fold (an accounting experiment)

The author's question: what if the fold challenge of BEEP-Ligerito were charged the error of the affine fold
(plus `2L`) in place of `delta n + 1` (plus `2L`)? `beep_params.py --beep-affine-charge` gives the fold grinding
of each level under that charge, i.e. for `(E_aff + 3L + 1)/|F|` with `E_aff` from the certified affine bound,
at the levels where every fold round has a certificate at the level's slack (elsewhere the level keeps BEEP's own
grinding, in whole bits). The variant `beepaff-<eta>` runs the BEEP ladder with that grinding. **This is not a
sound configuration**: the affine bound is a statement about the affine fold, under which the samples would not
be needed, and that protocol is the affine variant. The column "affine" is the affine variant as we run it.

<!-- hybrid: scripts/readme_tables.py hybrid, from 7-beep-ligerito/bench_results/three-way-20261114g/results.json -->
| words | rate | eta | fold bits, BEEP | fold bits, affine charge | hashes, BEEP (10^6) | hashes, affine charge (10^6) | prove, BEEP (ms) | prove, affine charge (ms) | the same from BEEP's time without grinding (ms) | BEEP without grinding (ms) | affine (ms) | proof (KiB) |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | 0.02 | 10, 13 | 7, 10 | 0.16 | 0.14 | 2.6 | 2.0 | 2.1 | 1.3 | 1.8 | 301.6 |
| 2^16 | 1/2 | 0.001 | 12, 14 | 12, 14 | 0.25 | 0.26 | 3.2 | 3.3 | 3.3 | 1.2 | 1.8 | 279.0 |
| 2^17 | 1/2 | 0.02 | 11, 12 | 7, 9 | 0.16 | 0.14 | 2.8 | 2.3 | 2.3 | 1.5 | 2.1 | 313.5 |
| 2^17 | 1/2 | 0.001 | 12, 14 | 12, 14 | 0.23 | 0.25 | 3.5 | 3.7 | 3.7 | 1.6 | 2.1 | 290.3 |
| 2^18 | 1/2 | 0.02 | 12, 13 | 7, 9 | 0.18 | 0.14 | 4.3 | 3.3 | 3.4 | 2.6 | 3.0 | 324.5 |
| 2^18 | 1/2 | 0.001 | 13, 14 | 13, 14 | 0.25 | 0.27 | 4.8 | 4.9 | 4.8 | 2.7 | 3.1 | 300.7 |
| 2^20 | 1/2 | 0.02 | 14, 13, 13 | 7, 8, 10 | 0.30 | 0.21 | 8.0 | 6.5 | 6.5 | 5.3 | 5.7 | 371.7 |
| 2^20 | 1/2 | 0.001 | 14, 14, 14 | 14, 14, 14 | 0.42 | 0.48 | 8.9 | 9.2 | 9.1 | 5.7 | 6.0 | 345.1 |
| 2^22 | 1/2 | 0.02 | 17, 16, 14, 13 | 7, 8, 9, 10 | 0.87 | 0.27 | 20.9 | 16.9 | 16.7 | 15.1 | 14.8 | 303.7 |
| 2^22 | 1/2 | 0.001 | 17, 16, 15, 15 | 12, 16, 15, 15 | 1.14 | 0.89 | 22.3 | 20.9 | 21.1 | 15.2 | 15.2 | 283.3 |
| 2^24 | 1/2 | 0.02 | 18, 17, 15, 13 | 7, 8, 9, 10 | 1.59 | 0.27 | 48.2 | 40.4 | 40.6 | 39.0 | 34.1 | 439.2 |
| 2^24 | 1/2 | 0.001 | 18, 17, 16, 15 | 12, 17, 16, 15 | 1.98 | 1.29 | 50.4 | 46.0 | 46.4 | 39.0 | 34.3 | 408.1 |
| 2^25 | 1/2 | 0.02 | 19, 18, 16, 14 | 7, 8, 9, 10 | 2.92 | 0.27 | 88.8 | 74.1 | 75.0 | 73.3 | 60.5 | 452.9 |
| 2^25 | 1/2 | 0.001 | 19, 18, 16, 15 | 12, 18, 16, 15 | 3.31 | 1.81 | 91.5 | 82.7 | 83.0 | 73.2 | 62.0 | 420.9 |
| 2^22 | 1/4 | 0.02 | 18, 17, 15, 14 | 8, 9, 10, 11 | 2.07 | 0.28 | 29.9 | 20.6 | 20.5 | 18.6 | 18.3 | 192.9 |
| 2^22 | 1/4 | 0.001 | 19, 17, 16, 15 | 12, 17, 16, 15 | 2.42 | 1.31 | 33.0 | 26.7 | 26.6 | 18.9 | 19.2 | 183.2 |
| 2^24 | 1/4 | 0.02 | 19, 18, 16, 14 | 8, 9, 10, 11 | 4.35 | 0.28 | 67.4 | 46.8 | 47.1 | 45.2 | 40.3 | 261.1 |
| 2^24 | 1/4 | 0.001 | 20, 18, 17, 16 | 12, 18, 17, 16 | 4.84 | 2.24 | 71.8 | 56.5 | 56.8 | 45.4 | 40.8 | 247.6 |
| 2^15 | 1/8 | 0.02 | 12, 13 | 8, 10 | 0.18 | 0.14 | 2.8 | 1.8 | 1.8 | 0.9 | 1.7 | 115.4 |
| 2^15 | 1/8 | 0.001 | 13, 15 | 13, 15 | 0.31 | 0.36 | 3.8 | 3.6 | 3.7 | 1.0 | 1.7 | 110.1 |
| 2^22 | 1/8 | 0.02 | 20, 18, 16, 15 | 8, 9, 10, 11 | 4.71 | 0.29 | 51.4 | 27.3 | 27.4 | 25.5 | 25.1 | 150.6 |
| 2^22 | 1/8 | 0.001 | 20, 18, 17, 16 | 13, 18, 17, 16 | 5.34 | 2.30 | 55.3 | 37.5 | 37.7 | 25.7 | 26.1 | 142.3 |
| 2^24 | 1/8 | 0.02 | 21, 19, 17, 15 | 8, 9, 10, 11 | 10.44 | 0.29 | 110 | 63.1 | 62.6 | 60.7 | 55.0 | 196.9 |
| 2^24 | 1/8 | 0.001 | 21, 19, 18, 16 | 13, 19, 18, 16 | 11.59 | 3.88 | 117 | 78.6 | 78.3 | 60.1 | 56.5 | 185.9 |
| 2^22 | 1/16 | 0.02 | 21, 19, 17, 16 | 9, 10, 11, 12 | 10.35 | 0.30 | 88.0 | 38.7 | 38.4 | 36.1 | 35.9 | 131.2 |
| 2^22 | 1/16 | 0.001 | 21, 19, 18, 17 | 13, 19, 18, 17 | 11.22 | 4.18 | 93.7 | 56.1 | 55.9 | 36.2 | 37.3 | 122.5 |
| 2^24 | 1/16 | 0.02 | 22, 20, 18, 16 | 9, 10, 11, 12 | 23.46 | 0.30 | 202 | 93.3 | 93.5 | 91.2 | 88.3 | 166.9 |
| 2^24 | 1/16 | 0.001 | 22, 20, 19, 17 | 13, 14, 19, 17 | 25.07 | 3.21 | 218 | 106 | 106 | 90.0 | 86.2 | 156.2 |

At slack 0.02, where every level has an affine certificate, the fold grinding drops to
7 to 12 bits and the prover would take 0.44 to 0.84 times the time of
BEEP-Ligerito, i.e. 1.04 to 1.22 times the time of the affine variant. At slack 0.001 only the
first level of the long codes has a certificate (and the second level for 2^24 words at rate 1/16), and the
prover would take 1.23 to 2.15 times the time of the affine variant at its least slack. The
sizes do not change. So the grinding of the fold challenge is most of what separates BEEP-Ligerito from the
affine variant, and the samples are the rest: with the same grinding BEEP-Ligerito would still be slower.

### Flags that travel with these numbers

- **The affine variant of the tables is ours in two respects.** Its prover is ours, and it has no sample on its
  first commitment under an accounting of ours (`eps_aff + 2L/|F|` per fold round of the first level). Flock's
  variant as it ships is in the table above. The accounting has no written proof and no review.
- **A doubt on Flock's rule after a sample.** With a sample on a commitment, Flock's note charges `2/|F|` per
  fold round for the claims ("one candidate"). It is unclear to us that the sample removes the other candidates
  of the list from that union bound: their claims are false after the sample, but a false claim of any of them
  can still become true at a fold challenge. If it does not, every level of the affine variant needs the `2L`
  charge that we use at its first level: 3 to 6 more bits of grinding per fold round
  at the levels after the first at slack 0.02 (2 to 6 at the least slack), i.e.
  at most 5 % more prover time (5 % at the least slack;
  an estimate from the hashes of those searches). We kept Flock's rule at the levels that have a sample. The
  paper states the doubt after its limitations. Not checked with Flock's authors.
- **Two provers of ours, one of Flock's.** The fold rounds of the affine variant and of BEEP-Ligerito are our
  code, with the same techniques (one pass per round, the same kernels, the same buffers), and the two provers
  share everything else. We believe that they are at a comparable level, but one of them may have more room
  left than the other. Ligerito (Flock) runs Flock's code, on its dense path.
- **The quoted times of BEEP-Ligerito may be slightly too low.** As a check, we compare "prove" with the time
  measured with the proofs of work, corrected for the hashes that those repetitions tried. For Ligerito (Flock)
  and the affine variant they agree within 6 % (over all the affine provers:
  within 10 % for Flock's and 8 % for
  ours). For BEEP-Ligerito the measured time is longer in 19 of
  28 cases, by 2 % in the median and at most
  14 % (where the proofs of work are about half of the opening).
- **Noise of a few percent between processes.** The machine was not fully idle: load averages of 0.9 to 4.2
  before the cells, and at least 74 % idle CPU when each process started. Two processes that should
  take the same time differ by up to 5 %: for 2^24 words at rate 1/16 the four affine provers at slack 0.02 are
  3 to 5 % slower without proofs of work than the same provers at the least slack
  (and slower than their own runs with proofs of work), so that row of the affine variant is slightly
  pessimistic. In the other instances with several processes the two agree within
  3 %.
- **Dense path only.** The provers work on a materialized table and basis, as in Flock's
  `benches/affine_vs_f256.rs` without `lanes`. Flock's production opening is lane-major, and there the first
  rounds of the split and affine variants work on per-lane statistics. Our affine prover does not have that
  path, and BEEP's points need the folded table at every round, so we do not know how to carry that
  optimization over.
- **Analyses of different status.** Flock's follows its paper (BCHKS25-based). The affine variant's design note
  follows a draft of the affine-combiners paper and lists open points (the interleaved bound, which the paper of
  November 11, 2026 now has, and the round-by-round accounting of the agreement loss). Both of Flock's ladders
  draw their binding points one at a time (above). Ours rests on the paper's theorems (`t:main_thm`,
  `t:beep_codeswitch`) with grinding counted as bits (`log2(2^64/T)` for a threshold), and its transcript-level
  accounting (the squeezes that follow each other without a prover message) is in the documentation of
  `beep.rs`. Nobody outside this project has reviewed it.
- **The affine bounds.** The fold grinding of the affine ladders uses the bound in the form of Flock's script,
  which also searches the parameter `B` of the proof. With `B` as the published theorem fixes it (Theorem 4.10 of
  the version of November 11, 2026), the bounds are 0.7 to 1.1 bits weaker, which would cost one more bit of
  grinding in some rounds. Flock registers the affine ladders for 2^25 words at rate 1/2 and for 2^22 words at
  rate 1/4 (with the sample on the first commitment); the others are ours. At 2^20 words the ladder with rates
  1/2, 1/8, 1/32 has no certificate at its last level (`fast_n20_r135.txt`), so the affine and BEEP ladders use
  1/2, 1/8, 1/64 there.
- **The list bound is loose.** `L = floor(1/(2 eta sqrt(rho)))` is what Flock and Note 2 use. The Johnson bound
  in the form `(a - b)/(a^2 - b)` is about five times smaller at rate 1/2 (7 against 35 at slack 0.02), and it
  would save a few bits of grinding on the batching challenges and some samples at the small levels. Not done.

## The run at 100 bits (100bits-3, November 15, 2026)

The author asked for the same experiments at 100 bits of security, "same parameter regimes as for 128 bits".
`scripts/cells100.txt` has the same 68 cells with `bits=100` (`scripts/make_cells100.py` writes it from
`cells.txt`: the same shapes, ladders, slacks and variants, without `beepaff`):

- **Ligerito (Flock)** runs on Flock's 100-bit profiles: `fast100` at rate 1/2 and `slim100` at rate 1/4, which
  Flock ships, and Flock's derivation of `slim100` at the rates 1/8 and 1/16. In these profiles only the query
  term targets 100 bits: the fold challenges are still in GF(2^256) and the batching challenges keep their
  grinding for 128 bits. `fast100` has no grinding on its queries, and `slim100` has 16 bits.
- **The affine variant and BEEP-Ligerito** run on ladders built for a round-by-round target of 100 bits
  (`beep::affine_ladder_target`, `beep::beep_ladder_at`, `Grind::exact_at`), with the same shapes, rates and
  slacks as at 128 bits. As at 128 bits, they take the grinding of the queries and the binding samples from
  Flock's configuration of the instance, so they have no query grinding at rate 1/2.
- **What 100 bits changes.** The field still has 2^128 elements, so every challenge has 28 bits to spare. The
  fold squeeze of BEEP has error `(t + 3L)/|F|` with `t + 3L < 2^21.6` on every
  code of the instances: no fold grinding, with 4 points in every fold round (4 to 5 at 128 bits) and the least
  threshold `t = N + 1` at every level. The affine fold needs no grinding either (with or without the sample on
  the first commitment), nor do the batching challenges. So at rate 1/2 the affine variant and BEEP-Ligerito have
  no proof of work at all, and at the other rates only the 16 bits on the queries of each level. A fold analyzed
  with MCA would still need 4 to 13 bits of grinding at slack 0.02 with the bound of BCHKS25
  (23 to 35 at 0.001), over this field.
- **The exact recheck** (`beep_params.py --check`, which reads the target of every ladder from its
  configuration): 122 distinct BEEP levels and 109 levels of the affine ladders, no failure.

**How it was measured.** November 15, 01:10 to 02:10, at night, through the gate, with the idle check before
every cell (`CAMPAIGN_IDLE_EACH=1`), 68 processes, bench binary `80c4da9a5f673136`. This is
the second run of these cells. The first one, 20261114h (November 14, 09:43 to 10:48), ran while the machine was
in use and short of memory. Its proof sizes and parameters are the same. For 2^22 words and more the provers of
its tables took up to 20 % longer without proofs of work than in this run
(10 % in the median), and its times are not used. After it, a watcher waited
for 9 GB of unused memory (`scripts/when_memory_is_free.zsh`) and gave up after 14 hours: with about twenty
sessions of an assistant and a browser open, the machine never had more than 6.4 GB unused.

So this run was started with less unused memory than the largest cells take: 3.0 to 5.5 GB before
each process (7.7 to 10.0 GB during the run 20261114g), with 4.4 to 6.6 GB in the
compressor. The CPU was at least 76 % idle before a process.

**Compressed memory.** 12 of the processes have a peak footprint above their resident
memory by more than 2 % and 32 MiB (the flag of the campaign reports; here 10 to 31 %), i.e. a
large part of their memory was compressed: the 10 of 2^24 words at rate 1/16, and
the 2 of Ligerito (Flock) for 2^25 words. Three more are just below the flag
(1.5 to 2.0 %): `eighth24.split`, `fast25.affine` and `sixteenth22`. All three are processes
with proofs of work, so they matter for the verifier times and for the check of "prove" against the measured
times, not for "prove".

This shows in single proofs:

- in the four of them that run Ligerito (Flock), its first proof takes
  2.3 to 9.2 times as long as the median of the nine (at most
  1.3 times in the run 20261114g);
- the affine variant and BEEP-Ligerito take 196 to 229 page faults per proof for 2^24
  words at rate 1/16 (our provers take at most 17 in the run 20261114g);
- over the rows of 5 ms and more, 3.3 % of the repetitions of these processes take
  more than 1.2 times the median of their row, against 0.8 % in the other processes
  and 1.3 % in the run 20261114g.

We do not see it in the medians, which are what the tables report. For the rows of the tables in these
processes the median without proofs of work is at most 4 % above the
fastest of the nine proofs, and it is 0.94 to 1.02 times the median at 128 bits
(0.92 to 1.02 over all 21 provers of these
processes with a comparable ladder, see below).

**Which times are used.** The rule was written into `../typst/scripts/make_tables.py` while the campaign ran,
before its results were read (`FAULTS_BURST`, `SLOW_VS_128`). The times of an instance are not used if one of
its provers took a burst of page faults (more than 1000 per proof in the median; for
Flock's provers, which allocate their tables in every proof, twice the pages of a message more), or if a prover
is more than 8 % slower without proofs of work than in the run 20261114g. The flag for compressed memory alone does not decide.

The second test compares a row with the same row at 128 bits when its ladder is the same at the two targets.
There the prover does at least the same work at 128 bits: it makes more queries, and BEEP-Ligerito takes
4 to 5 samples per fold round against 4. So the test is one-sided.

**All 14 instances pass**: no row fails. Without proofs of work the provers of the tables
take 0.84 to 1.07 times as long as at 128 bits. Four things about this rule should be said plainly:

1. *It is looser than the guard of the run at 128 bits.* There a prover of ours may take
   100 page faults per proof (`FAULTS_PER_PROOF_MAX`). Under that guard 9 sides of rows of the tables
   would be flagged: our four provers for 2^24 words at rate 1/16 in both of their processes, and the affine
   variant at 0.02 for 2^25 words in its process with proofs of work.
2. *The limit of 1000 was chosen after a smoke run* (`bench_results/smoke-100bits-20261115/`, 01:08: the four
   affine provers at slack 0.02 without proofs of work, by hand, 5 repetitions). For 2^24 words at rate 1/2 the
   flag was not set, and the provers took 0.99 to 1.03 times their times at 128 bits. At rate
   1/16 it was set (peak footprint 6.6 GB, resident
   4.7 GB): 0.96 to 0.99 times, with up to
   250 page faults per proof.
3. *One change after the run was read.* As fixed, the second test left out every row of Ligerito (Flock). It
   now covers its rows at rate 1/2, whose ladder is the same at the two targets. This can only reject more rows.
4. *For Ligerito (Flock) below rate 1/2 the rule tests nothing in practice.* Its ladder differs from the one at
   128 bits (`slim100` halves the rate from one level to the next, `slim` divides it by four), so the second
   test does not apply. The limit of the first test is thousands of page faults at 2^22 words and more, where
   Ligerito (Flock) takes at most 429 here. What we have for these seven rows is
   the check below, and the first proofs above.

**Noise.** "prove" and the time measured with the proofs of work agree within
10 % for Ligerito (Flock) and the affine variant and within
7 % for BEEP-Ligerito (6 % and
4 % for the proofs of 2 ms or more). Two processes without proofs of work
were a few percent slow, inside the rule:

- `slim24.affine-nopow` (the four affine provers at slack 0.02, 2^24 words at rate 1/4): they take
  4 to 5 % longer than what their twin process with proofs of work gives, and
  4 to 5 % longer than the same provers at the least slack;
- `eighth24.affsmall-nopow` (the four at the least slack, 2^24 words at rate 1/8):
  3 to 7 % and 2 to 7 %.

So the row "affine, 0.02" of the first instance and the row "affine, least" of the second are a few percent
pessimistic, and the ratio of BEEP-Ligerito to them is a few percent optimistic: with the time that the twin
process gives for the affine prover it is 1.19 in place of
1.13, and 1.13 in place
of 1.06. Neither is at an end of the ranges below. We did not run
these two processes again: the rule was fixed in advance and they pass it, the second one narrowly (its row of
the tables is the high end of the range against 128 bits: 1.07 times, against a limit of
1.08). In the other instances with several processes the affine provers at the two slacks
agree within 3 %.

<!-- main100: scripts/readme_tables.py main100, from 7-beep-ligerito/bench_results/three-way-100bits-3/results.json -->
| words | rate | variant | proof (KiB) | prove (ms) | no grinding (ms) | grinding (10^6 hashes) | verify (ms) |
|---|---|---|---:|---:|---:|---:|---:|
| 2^16 | 1/2 | Ligerito (Flock) | 311.7 | 1.7 | 1.7 | 0.00 | 0.67 |
| 2^16 | 1/2 | affine, eta = 0.02 | 273.1 | 1.1 | 1.1 | 0.00 | 0.45 |
| 2^16 | 1/2 | affine, least eta | 273.1 | 1.0 | 1.0 | 0.00 | 0.46 |
| 2^16 | 1/2 | BEEP, eta = 0.02 | 269.8 | 1.1 | 1.1 | 0.00 | 0.43 |
| 2^16 | 1/2 | BEEP, eta = 0.001 | 249.8 | 1.2 | 1.2 | 0.00 | 0.41 |
| 2^17 | 1/2 | Ligerito (Flock) | 324.5 | 2.6 | 2.5 | 0.00 | 0.83 |
| 2^17 | 1/2 | affine, eta = 0.02 | 281.5 | 1.3 | 1.3 | 0.00 | 0.54 |
| 2^17 | 1/2 | affine, least eta | 271.1 | 1.3 | 1.3 | 0.00 | 0.52 |
| 2^17 | 1/2 | BEEP, eta = 0.02 | 280.9 | 1.5 | 1.5 | 0.00 | 0.52 |
| 2^17 | 1/2 | BEEP, eta = 0.001 | 260.3 | 1.5 | 1.5 | 0.00 | 0.48 |
| 2^18 | 1/2 | Ligerito (Flock) | 354.2 | 4.1 | 4.0 | 0.00 | 0.79 |
| 2^18 | 1/2 | affine, eta = 0.02 | 291.7 | 2.3 | 2.3 | 0.00 | 0.62 |
| 2^18 | 1/2 | affine, least eta | 280.5 | 2.2 | 2.2 | 0.00 | 0.59 |
| 2^18 | 1/2 | BEEP, eta = 0.02 | 291.1 | 2.6 | 2.6 | 0.00 | 0.61 |
| 2^18 | 1/2 | BEEP, eta = 0.001 | 269.9 | 2.5 | 2.5 | 0.00 | 0.57 |
| 2^20 | 1/2 | Ligerito (Flock) | 382.9 | 8.8 | 8.7 | 0.00 | 1.14 |
| 2^20 | 1/2 | affine, eta = 0.02 | 332.7 | 4.8 | 4.8 | 0.00 | 0.72 |
| 2^20 | 1/2 | affine, least eta | 313.0 | 4.7 | 4.7 | 0.00 | 0.69 |
| 2^20 | 1/2 | BEEP, eta = 0.02 | 333.1 | 5.3 | 5.3 | 0.00 | 0.71 |
| 2^20 | 1/2 | BEEP, eta = 0.001 | 309.0 | 5.2 | 5.2 | 0.00 | 0.67 |
| 2^22 | 1/2 | Ligerito (Flock) | 334.8 | 24.6 | 24.5 | 0.01 | 1.21 |
| 2^22 | 1/2 | affine, eta = 0.02 | 272.2 | 13.5 | 13.5 | 0.00 | 0.72 |
| 2^22 | 1/2 | affine, least eta | 255.6 | 13.3 | 13.3 | 0.00 | 0.70 |
| 2^22 | 1/2 | BEEP, eta = 0.02 | 273.2 | 15.4 | 15.4 | 0.00 | 0.69 |
| 2^22 | 1/2 | BEEP, eta = 0.001 | 254.5 | 15.3 | 15.3 | 0.00 | 0.67 |
| 2^24 | 1/2 | Ligerito (Flock) | 473.5 | 71.1 | 70.9 | 0.01 | 1.26 |
| 2^24 | 1/2 | affine, eta = 0.02 | 393.1 | 32.4 | 32.4 | 0.00 | 0.91 |
| 2^24 | 1/2 | affine, least eta | 366.9 | 32.4 | 32.4 | 0.00 | 0.85 |
| 2^24 | 1/2 | BEEP, eta = 0.02 | 394.2 | 39.2 | 39.2 | 0.00 | 0.87 |
| 2^24 | 1/2 | BEEP, eta = 0.001 | 366.3 | 39.1 | 39.1 | 0.00 | 0.82 |
| 2^25 | 1/2 | Ligerito (Flock) | 490.2 | 134 | 134 | 0.01 | 1.36 |
| 2^25 | 1/2 | affine, eta = 0.02 | 405.5 | 59.8 | 59.8 | 0.00 | 0.99 |
| 2^25 | 1/2 | affine, least eta | 377.3 | 59.3 | 59.3 | 0.00 | 0.93 |
| 2^25 | 1/2 | BEEP, eta = 0.02 | 406.6 | 73.8 | 73.8 | 0.00 | 0.99 |
| 2^25 | 1/2 | BEEP, eta = 0.001 | 377.8 | 74.0 | 74.0 | 0.00 | 0.91 |
| 2^22 | 1/4 | Ligerito (Flock) | 185.9 | 30.8 | 28.9 | 0.33 | 0.87 |
| 2^22 | 1/4 | affine, eta = 0.02 | 147.3 | 17.6 | 16.2 | 0.26 | 0.48 |
| 2^22 | 1/4 | affine, least eta | 140.3 | 17.4 | 16.0 | 0.26 | 0.47 |
| 2^22 | 1/4 | BEEP, eta = 0.02 | 148.3 | 19.2 | 17.8 | 0.26 | 0.48 |
| 2^22 | 1/4 | BEEP, eta = 0.001 | 140.3 | 19.3 | 18.0 | 0.26 | 0.45 |
| 2^24 | 1/4 | Ligerito (Flock) | 251.2 | 78.2 | 75.7 | 0.40 | 0.88 |
| 2^24 | 1/4 | affine, eta = 0.02 | 198.8 | 41.9 | 40.4 | 0.26 | 0.55 |
| 2^24 | 1/4 | affine, least eta | 188.5 | 40.1 | 38.6 | 0.26 | 0.53 |
| 2^24 | 1/4 | BEEP, eta = 0.02 | 199.9 | 47.3 | 45.8 | 0.26 | 0.56 |
| 2^24 | 1/4 | BEEP, eta = 0.001 | 189.1 | 47.0 | 45.5 | 0.26 | 0.54 |
| 2^15 | 1/8 | Ligerito (Flock)* | 108.5 | 2.6 | 1.4 | 0.20 | 0.34 |
| 2^15 | 1/8 | affine, eta = 0.02 | 89.7 | 1.5 | 0.8 | 0.13 | 0.22 |
| 2^15 | 1/8 | affine, least eta | 89.7 | 1.5 | 0.8 | 0.13 | 0.22 |
| 2^15 | 1/8 | BEEP, eta = 0.02 | 90.3 | 1.6 | 0.9 | 0.13 | 0.22 |
| 2^15 | 1/8 | BEEP, eta = 0.001 | 85.7 | 1.5 | 0.8 | 0.13 | 0.21 |
| 2^22 | 1/8 | Ligerito (Flock)* | 147.4 | 36.9 | 34.9 | 0.34 | 0.77 |
| 2^22 | 1/8 | affine, eta = 0.02 | 116.4 | 23.7 | 22.3 | 0.26 | 0.40 |
| 2^22 | 1/8 | affine, least eta | 110.4 | 23.9 | 22.4 | 0.26 | 0.39 |
| 2^22 | 1/8 | BEEP, eta = 0.02 | 117.5 | 26.0 | 24.5 | 0.26 | 0.41 |
| 2^22 | 1/8 | BEEP, eta = 0.001 | 110.3 | 25.6 | 24.2 | 0.26 | 0.40 |
| 2^24 | 1/8 | Ligerito (Flock)* | 195.2 | 93.0 | 90.6 | 0.41 | 0.78 |
| 2^24 | 1/8 | affine, eta = 0.02 | 151.6 | 55.3 | 53.7 | 0.26 | 0.47 |
| 2^24 | 1/8 | affine, least eta | 143.2 | 58.6 | 57.1 | 0.26 | 0.47 |
| 2^24 | 1/8 | BEEP, eta = 0.02 | 152.7 | 62.5 | 61.1 | 0.26 | 0.47 |
| 2^24 | 1/8 | BEEP, eta = 0.001 | 143.7 | 62.2 | 60.7 | 0.26 | 0.48 |
| 2^22 | 1/16 | Ligerito (Flock)* | 125.8 | 50.5 | 48.4 | 0.34 | 0.70 |
| 2^22 | 1/16 | affine, eta = 0.02 | 99.9 | 35.5 | 34.1 | 0.26 | 0.38 |
| 2^22 | 1/16 | affine, least eta | 94.5 | 35.4 | 34.0 | 0.26 | 0.37 |
| 2^22 | 1/16 | BEEP, eta = 0.02 | 100.9 | 37.5 | 36.2 | 0.26 | 0.41 |
| 2^22 | 1/16 | BEEP, eta = 0.001 | 94.4 | 37.2 | 35.9 | 0.26 | 0.38 |
| 2^24 | 1/16 | Ligerito (Flock)* | 164.7 | 122 | 119 | 0.41 | 0.72 |
| 2^24 | 1/16 | affine, eta = 0.02 | 126.7 | 82.8 | 81.4 | 0.26 | 0.42 |
| 2^24 | 1/16 | affine, least eta | 119.5 | 84.5 | 83.0 | 0.26 | 0.40 |
| 2^24 | 1/16 | BEEP, eta = 0.02 | 127.8 | 90.1 | 88.7 | 0.26 | 0.43 |
| 2^24 | 1/16 | BEEP, eta = 0.001 | 120.0 | 91.7 | 90.3 | 0.26 | 0.42 |

In short:

- **Proof size.** Smaller than at 128 bits, since every level makes fewer queries. At slack 0.02 the affine
  variant saves 10 to 11 % at rate 1/2 and 22 to 24 % at the
  other rates, and BEEP-Ligerito 10 to 11 % and
  22 to 23 %. The saving is smaller at rate 1/2 because there the queries are
  ground at 128 bits (16 bits) and not at 100 bits, so their number decreases less. Between the variants the
  picture is the same as at 128 bits: at the same slack they differ by at most
  3.3 KiB; BEEP-Ligerito at 0.001 is 5 to 9 % smaller than the affine variant at 0.02, and
  0.99 to 1.00 times the affine variant at its least slack for 2^20 words and
  more. For the short messages it is smaller: 9 %,
  4 % and 4 % at 2^16, 2^17 and
  2^18 words, and 5 % at 2^15 words and rate 1/8 (the least slack of
  the affine ladder does not depend on the target).
- **Prover.** BEEP-Ligerito takes 1.05 to 1.23 times as long as the affine variant at slack
  0.02 (1.00 to 1.25 at the small slacks), against 1.37 to 2.45
  (1.47 to 2.53) at 128 bits. The grinding of the fold challenges is gone, and what is left is the cost of the samples. The ratio is
  largest for 2^24 and 2^25 words at rate 1/2 (1.21 and
  1.23 at slack 0.02): 39.2 ms against
  32.4 ms for 2^24 words.
- **The small slack of BEEP-Ligerito against the affine variant at 0.02.** Proofs
  5 to 9 % smaller, for 1.01 to 1.24 times the prover time.
- **Verifier.** BEEP-Ligerito takes 0.96 to 1.10 times as long as the affine variant at slack
  0.02.
- **Against Ligerito (Flock)** on its 100-bit profiles: BEEP-Ligerito takes 0.55 to 0.74
  times as long, and the affine variant 0.44 to 0.70 times. Not like for like, as at 128 bits.

## The timing of Flock's affine prover in two early runs (not explained, not seen since)

In the runs 20261113b and 20261113b-check1, in the processes with proofs of work that it shared with the other
provers, Flock's affine prover took 11 to 42 % longer than "prove", and the other provers of the same
processes did not (20 to 39 % above them). The author asked whether this is still relevant.

**It is not relevant for the numbers.** The quoted times never used the affected measurement (they are the time
without proofs of work plus a model of the proofs of work), and it has not come back:

- the four later campaigns (c, d, e, g) have 29 shared processes with Flock's
  affine prover: at most 8 % above the other provers of the process;
- they have 36 processes with affine provers alone: one is slow (below);
- in the run 20261114g, over all the affine provers (56 rows of Flock's prover
  and 56 of ours), "prove" and the measured time agree within
  10 % and 8 %, and the largest
  differences are tenths of a millisecond on the short messages;
- the three diagnostic runs through the gate and 28 repetitions by hand
  (`bench_results/diagnostics-20261113b/INDEX.md`) do not show it. One of the diagnostic runs used the binary
  of the run 20261113b, rebuilt from its exact sources. So it is not the binary, the launch method or a busy
  terminal.

**What the two affected runs look like**, against a normal run of the same binary:

- for 2^24 words: the same number of instructions over the process (675 G), 5 % more cycles and 6 % more user
  CPU time (3.3 s) at the same average clock rate, for 0.3 to 1.0 s more wall time; in the check run, the same
  page reclaims and the same system time. So during the extra time the cores were busy and executed the same
  instructions more slowly, which is what passes that wait for memory look like, and the process did not fault
  memory in again;
- the slowdown is the same in every repetition, it grows with the message (about 1.7, 5.5 and 21 ms for 2^20,
  2^22 and 2^24 words), and it hits Flock's affine prover with proofs of work and no other variant of the same
  process, although the repetitions of the variants are interleaved;
- it is not the proofs of work themselves: the fold searches of the affine prover are 4 to 9 bits, on one
  thread, 1 to 12 microseconds each.

**What we tested on November 14, without reproducing it:**

- the scheduling policy of the process (`taskpolicy` with a latency tier, a throughput tier, and the utility
  class): no effect;
- the order in which the pages of the tables are first touched, i.e. whether the physical memory behind a table
  is contiguous: no effect on the speed of the passes;
- a second thread pool or threads left behind by an earlier phase: there are none on this machine (Flock sizes
  one pool with all ten cores, and the two helper threads of its first commitment are scoped);
- the SME state after a proof of work: the searches use the NEON code of BLAKE3, not SME;
- workers that sleep during the short searches on one thread and wake up late: the searches of 7 to 13 bits of
  the affine variant without its first sample leave no gap.

**One later process looks like it, and looks like outside load.** In the run 20261113d the affine prover alone,
for 2^24 words with proofs of work, took 63.7 ms in all nine repetitions against 52.6 ms quoted
(21 %). The machine was 79 % idle when that process started
(89 % for the median process), and the counters of the prover show the same
instructions (5.82 G), 12 % more cycles, 70 % more involuntary context switches, more time waiting for a core,
and 37.5 % of its CPU time on performance cores against 41 %. That is what competing for cores looks like. We
did not have these counters in the two affected runs, so we cannot say that it is the same thing: there, the
slowdown hit the affine variants of eight processes in a row and no other variant, which outside load does not
explain.

**A different hazard that we did find: memory.** When the machine is short of free memory, proofs take bursts of
page faults and run up to twice as long. We saw it twice on November 14: in smoke runs with other applications
holding the memory (3.7 GB unused; hundreds to tens of thousands of page faults per proof), and in the run
20261114f, where a defect of our affine prover filled Flock's buffer pool (see "Our prover for the affine
ladder"). It does not explain the two affected runs, whose page reclaims and system time are normal. Guards:
we check for 10 GB of unused memory before a campaign; `collect.py` flags a process whose peak footprint exceeds
its resident memory; every row keeps the counters of its prover in both processes (`counters`, with the page
faults per proof) and the idle share of the machine when each process started (`memory.*.idle_before_pct`); and
`make_tables.py` warns on a prover of ours that takes more than a hundred page faults per proof, and on an affine
prover that is 10 % slower with proofs of work than "prove".

## Earlier runs

- **20261114f** (01:53 to 02:54; the cells of the run 20261114g, with the first version of `affine_fast.rs`).
  Discarded: the twenty processes with the four affine provers of 2^24 and 2^25 words ran short of memory (13
  to 26 GiB of peak footprint), and the cells after them ran on a machine that was swapping. Its sixteen shared
  processes (the instances up to 2^22 words) were not affected, and their affine rows agree with those of the
  run 20261114g.
- **20261113e** (the run that the paper quoted before; `-rerun1` is a rerun of two of its processes). The affine
  variant was Flock's as it ships. BEEP-Ligerito took 0.89 to 0.92 times as long at 2^24 and 2^25 words and rate
  1/2, 1.07 to 1.17 times for the shorter messages, and 1.14 to 2.12 times at the rates 1/4 to 1/16. Its BEEP
  rows agree with those of the run 20261114g within the noise (48.7 and 48.2 ms for 2^24 words at rate 1/2).
- **20261113d** (the thirteen instances and the variants of the run 20261113e, before the thresholds: `beep`
  there is `beepbits` here). Its exact recheck passes (116 levels and 88 of the accounting experiment).
- **20261113c** (ten instances, rates 1/2 to 1/16; the prover of the second version, with the sample on the
  first commitment, three passes and whole bits). At 2^24 words and slack 0.02, BEEP-Ligerito took 87.7, 103.0,
  167.1 and 263.1 ms at the rates 1/2 to 1/16, against 54.4, 60.2, 74.8 and 103.0 ms for the affine variant. The
  machine was in use during this run, so its times are less clean than those of the later runs.
- **20261113b** (five instances; the run of the second version): BEEP-Ligerito took 1.39 to 1.70 times as long
  as the affine variant at slack 0.02. This is the `beepold` column above, on the same code.

## What changed after the review

The first version (`bench_results/three-way-20261113`, with its rerun of 2^25 words) was reviewed by an
independent agent the same day. Its findings that we confirmed, and what we did:

1. *The affine fold has bounds at a small slack on the long codes*; the "no bound" entries came from the limits
   of Flock's search. Done: the wider search in `beep_params.py`, the affine variant at its least slack in the
   run, and the conclusion of the section rewritten (the first draft said that only BEEP allows a small slack).
2. *Binding points drawn one at a time but accounted together* (inherited from Flock). Done for BEEP-Ligerito:
   one message. Flock's two ladders are unchanged, and the README and the paper say so.
3. *The batching of the queries used the list of the wrong level.* Done: the list of the next code (one more bit).
4. *The cost of the proofs of work missed a fixed cost per search*, which favoured BEEP. Done: the bench times
   searches of every difficulty that a variant uses, and `collect.py` uses those times.
5. *The list of searches missed two searches of the split prover.* Done: the searches of every ladder in
   `beep.rs` (`PowGrinds`), checked in the bench against the nonces of every proof.
6. *Wrong pointers and wording in the section* (the lemma of the affine paper, the rate-1/4 row, the kernels, the
   verifier ratio). Done.

## Open

- Why Flock's affine prover was slow in the two early runs.
- A proof for the accounting of the affine variant without its first sample, and whether Flock's rule after a
  sample needs the list as well (see the flags).
- The two costs of BEEP-Ligerito against the affine variant. The grinding of the fold challenge: an analysis of
  BEEP with the affine weights (a sketch suggests that pretenders on the plane of the fold cost about
  `n^2/|F|^2` with one coordinate of agreement loss; not proved). The samples: four per round are needed because
  the bound of `t:main_thm` has the cube of `|F| L`, and each costs a pass over the folded table.
- The sharper Johnson list bound (`n (s - k + 1) / (s^2 - n (k - 1))`, about `(1 - sqrt(rho))` times `L`), which
  matters on short codes at a small slack. Not done.
- A code that is not known to have MCA up to the Johnson radius (the placeholder of the paper's Experiments
  section): nothing here runs on anything but Reed-Solomon codes.
- One thread; sizes beyond 2^25 words; the lane-major path (for both of our provers).
- The `-nopow` cells' proofs do not verify (no proof of work), so the verify times come from the cells with
  proofs of work.
- At 100 bits, the two processes without proofs of work that were about 5 % slow (`slim24.affine-nopow`,
  `eighth24.affsmall-nopow`, see "The run at 100 bits") were not measured again. A rerun with the same binary
  would need `load_run` of `make_tables.py` to take reruns of processes that are not memory-limited.
