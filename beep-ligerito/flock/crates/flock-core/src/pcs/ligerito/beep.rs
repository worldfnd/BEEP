// [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: BEEP folds on Flock's
// native Ligerito ladder, for the experiments of the BEEP paper (`typst/deep+.typ` of the
// repository `random-domain-ligerito`). Research, unaudited. Not part of upstream Flock: this
// file and the changes listed in `7-beep-ligerito/VENDORED.md` are local. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-13, after an independent review: the binding points of a
// level are drawn in one squeeze; the coefficients that batch the queries are ground for the list of
// the next level; `pow_searches` lists every proof-of-work search of the three ladders;
// `affine_ladder_at` builds the affine ladder at a slack per level; per-level byte counts]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: `BeepConfig::with_fold_grinding`,
// for the accounting experiment "a fold challenge charged the error of the affine fold" of the bench;
// `BeepConfig::without_first_binding`, the ladder with no out-of-domain binding sample on the first
// commitment, whose binding rests on the samples of the first fold round]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request ("work heavily in optimizing the
// sampling step"): the fold rounds of the prover take one pass over the table per round (`rounds_fast`: the
// pass that folds also computes the next round message and the row evaluations of the next points; the
// claims of the answers stay in factored form until the level has one row; PMULL kernels with three
// products per multiplication). `rounds_reference` keeps the previous rounds; the two write the same proof]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request ("research and implement" a proof of
// work whose threshold is not a power of two): `Grind`, the numerators of the ground squeezes in `BeepLevel`,
// and `BeepConfig::with_exact_grinding`, which grinds the fold, claim-batching and consistency-batching
// squeezes of the BEEP ladder with Flock's threshold search (`grind_pow_below_and_sample_f128`)]
// [AI-revised (claude-fable-5-2), 2026-11-14, with the prover of `affine_fast.rs`: the fold pass of
// `rounds_fast` tells the cache that it overwrites its output blocks (`affine_fast::will_overwrite`), as the
// pass of that prover does, so that the two are at the same level. No effect on the proof]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("run experiments for 100 bits of security,
// same parameter regimes as for 128 bits"): the round-by-round target is a parameter (`beep_ladder_at`,
// `affine_ladder_target`, `Grind::exact_at`, `BeepConfig::target_bits`); `beep_ladder`, `affine_ladder_at` and
// `Grind::exact` keep 128 bits. Two tests at 100 bits]
// [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request (a minimal Experiments section: "a comparison
// of runtimes and proof sizes of Ligerito and BEEP-Ligerito [...] at 100 bits of security over a field of size
// GF(2^128)"): `mca_ladder_at`, the ladder with no out-of-domain points and with its folds analyzed with mutual
// correlated agreement over GF(2^128), as the baseline "Ligerito over GF(2^128)" (Flock's Ligerito samples its
// fold challenges in GF(2^256), also in its profiles at 100 bits); `NO_POINTS_BITS`; one test. Nothing else of
// this file changed, so the ladders of the earlier runs are built as before]
// [AI-revised (claude-fable-5-2), 2026-11-16, same request: `mca_ladder_no_first_sample_at`, that baseline with no
// out-of-domain sample on its first commitment, as the BEEP ladder of the comparison has none, so that the two
// differ in their fold rounds only (the baseline of the paper's table at 100 bits); one test]
// [AI-revised (claude-fable-5-2), 2026-11-16, after an independent check of the section: the two MCA ladders grind
// the fold challenge of every round for the error of that round (`BeepConfig::fold_round_numerators`,
// `fold_rounds`, `fold_grind`), where they ground every round of a level for its first, worst round, as Flock's
// convention does: three times the hashes that a level with 2^6 rows needs. The BEEP ladders are unchanged (one
// numerator per level, `fold_rounds = None`), and so are their proofs]
// [AI-revised (claude-fable-5-2), 2026-11-17, at the author's request ("Can you run a comparison for 100 and 128 bits
// at this error bound?", the bound being Theorem 4.4 of Dao, Kominers and Thaler, ePrint 2026/2056, with no row
// union): `dkt_exceptional_count`, `mca_dkt_ladder_at` and `mca_dkt_ladder_no_first_sample_at`, the baseline
// "Ligerito over GF(2^128)" with that bound in place of Flock's; two tests. Additions only: no other function of
// this file changed, so every earlier ladder is built as before. Please review]

//! BEEP folds for the Ligerito ladder.
//!
//! The ladder is the one of [`super::affine`] on a dense L0
//! ([`super::affine::AffineL0::Dense`]): the same commitment, out-of-domain
//! binding of every committed table, queries, consistency glue and final
//! check, with every challenge in `F128`. Only the fold round differs. In
//! place of the affine fold `f' = f_0 + α f_1 + β X f_1` a round runs the
//! scalar fold of a sumcheck round, with out-of-domain answers BEFORE the
//! fold challenge:
//!
//! 1. the verifier samples `m` points `z_1, …, z_m`, each in `F^{dim-1}` for a
//!    table of `2^dim` words;
//! 2. the prover answers `b_{i,0} = <f_0, eq(z_i)>` and `b_{i,1} = <f_1,
//!    eq(z_i)>`, the multilinear extensions of the two halves at `z_i`;
//! 3. the prover sends the round polynomial `h(X) = <f_0 + X (f_0 + f_1),
//!    W_0 + X (W_0 + W_1)>` as `[h(0), h_2]` (the claim `v = h(0) + h(1)` gives
//!    its middle coefficient);
//! 4. the verifier samples the fold challenge `r` and the batching
//!    coefficients `ζ_1, …, ζ_m` from one squeeze, behind the fold grinding;
//! 5. both move to `f' = f_0 + r (f_0 + f_1)`, `W' = W_0 + r (W_0 + W_1) +
//!    Σ_i ζ_i eq(z_i)` and `v' = h(r) + Σ_i ζ_i ((1 + r) b_{i,0} + r b_{i,1})`.
//!
//! This is the BEEP reduction of the paper (its Section 4) with the
//! multilinear evader, applied to the two halves of the level's interleaved
//! word. With the answers, a fold is sound at every agreement at which the
//! code is list decodable, so a level only needs a list bound, here the
//! Johnson bound at agreement `√ρ + η`, and no mutual correlated agreement.
//!
//! ## Errors per challenge ([`beep_ladder`])
//!
//! For a level with block length `n`, agreement `s = ⌈(√ρ + η) n⌉`, list size
//! `L = ⌊1 / (2 η √ρ)⌋`, `N = max(n − s + 1, 2)`, messages of at most `μ`
//! variables and an integer threshold `t ≥ N + 1` (analysis only):
//!
//! * the points: `(|F| L)^3 (μ / |F|)^m / (t (t − 1) (t − N))`, which the
//!   selection keeps at most `2^-128` with no grinding;
//! * the fold squeeze `(r, ζ)`: `(t − 1 + 3 L) / |F|` (bad fold challenges,
//!   the sumcheck round `2L`, the batching `L`). The points of the next round
//!   are drawn right after it, from the same transcript state, so their error
//!   is added: the fold grinding covers `(t + 3 L) / |F|`.
//!
//! The out-of-domain binding, query, consistency-batching and claim-batching
//! terms follow Flock's `JohnsonOod` regime over `F128`, with the same strict
//! `2^-128` floor per challenge, and with two differences from
//! [`super::affine`]:
//!
//! * the binding points of a committed table are drawn in ONE squeeze, and
//!   their values are batched with coefficients from one squeeze behind one
//!   proof of work. The affine ladder draws a point, takes its value and a
//!   coefficient, and only then draws the next point. Flock's formula
//!   ([`paper_ood_bits`]: two list codewords agree at all `p` points with
//!   probability at most `C(L, 2) (μ / |F|)^p`) is the error of `p` points
//!   that are drawn together;
//! * the coefficients that batch the queries of level `i` are ground for
//!   `L_{i+1} ⌈log2 Q_i⌉ / |F|`, with the list bound `L_{i+1}` of the NEXT
//!   level, since the candidates at that point are the codewords near the new
//!   commitment. The affine ladder uses the list of level `i`, which is
//!   smaller when the rate decreases.
//!
//! A claim-batching squeeze that is followed by the points of a first fold
//! round covers `(L + 1) / |F|`.
//!
//! [`beep_ladder`] keeps the binding sample that Flock's ladders draw on the
//! first commitment. [`BeepConfig::without_first_binding`] removes it: the
//! construction of the paper has none, and the points of the first fold round
//! bind the commitment. The comparison runs the ladder without it.
//!
//! ## Proofs of work with a threshold
//!
//! A squeeze whose challenge is bad with probability at most `M / |F|`, for
//! an integer numerator `M`, needs a proof of work that a nonce passes with
//! probability `p` such that `(M / |F|) p < 2^-128`. With `g` leading zero
//! bits `p = 2^-g`, so `g` is the least integer with `M < 2^g`, and the
//! prover tries `2^g` hashes on average, up to twice `M`. Flock's transcript
//! also has a search against a 64-bit threshold
//! (`Challenger::grind_pow_below_and_sample_f128`): a nonce passes when the
//! first eight bytes of its hash, read big-endian, are below `target`, i.e.
//! with probability `target / 2^64`. With `target = ⌊(2^64 − 1) / M⌋`
//! (`grinding_target_for_degree` of flock-transcript) the bound holds, since
//! `M · target < 2^64`, and the prover tries about `M` hashes.
//! [`BeepConfig::with_exact_grinding`] grinds the fold squeeze (`M = t + 3L`),
//! the squeezes that batch claims (`M = L + 2`) and the one that batches the
//! queries (`M = L' ⌈log2 Q⌉`) in this way; the queries keep their 16 bits,
//! which stand for queries and not for a numerator. On Flock's chained
//! transcript (the one that its recursion replays in a circuit) a threshold
//! falls back to the covering number of bits, so nothing is gained there.
//!
//! ## The prover's fold rounds
//!
//! [`prove_beep`] runs the rounds of a level with one pass over the table per
//! round ([`rounds_fast`]). The pass that folds the table and the weight at
//! the challenge of a round also computes, on the folded table, the round
//! message of the next round and, for each of its points, the evaluations of
//! the rows at the column coordinates of the point; the two answers of a
//! point are sums over the rows. The claims that the answers add to the
//! sumcheck stay in factored form during the level and enter the dense weight
//! when one row is left. [`prove_beep_reference_timed`] runs the rounds as
//! the list above states them (a pass for the answers, one for the round
//! message, one for the fold, which also adds the claims to the weight). The
//! two write the same proof.
//!
//! Layout, as in [`super::affine`]: a level's table has `2^k` rows of `2^c`
//! coefficients, stored `f[row + rows * col]`; a round binds the lowest row
//! bit. There are no overflow coefficients: the scalar fold keeps the degree.

use std::{
    env::var,
    time::{Duration, Instant},
};

use rayon::prelude::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
    ParallelSlice, ParallelSliceMut,
};
use serde::{Deserialize, Serialize};

use crate::{
    merkle::cap_layer,
    pcs::{
        ligerito::{
            AdditiveNttF128, Challenger, F128, F256, F256Unreduced, Hash, LigeritoProof,
            ProverConfig, RecursiveProof, VerifierConfig,
            affine::{
                Commitment, Context, EqFactors, PAR_MIN, affine_ladder, eq_at_residual,
                induced_at_residual, level_shapes, native_ks, novel_basis_evals, query_point,
                view,
            },
            affine_fast::will_overwrite,
            algebraic_grinding_schedule, build_eq_table, ceil_log2, eval_sk_at_vks,
            extension::recursive_verifier_with_basis_succinct,
            fold_pairs, grind_and_sample_queries, induce_sumcheck_poly_auto, ligero_commit,
            merkle_paths_for, paper_ood_bits, strict_grinding_bits, strict_query_count,
            verify_and_sample_queries, verify_level_opens,
        },
        ring_switch::build_eq_split,
    },
    scratch::{give_f128, take_f128},
};

/// The BEEP opening's transcript domain label.
pub const LABEL: &[u8] = b"flock-ligerito-beep-f128-v1";

/// `log2 |F|` of every challenge and answer.
const LOG_Q: f64 = 128.0;
/// Round-by-round target of every challenge, as in the `Fast` profile: the
/// target of [`beep_ladder`] and [`affine_ladder_at`]. [`beep_ladder_at`] and
/// [`affine_ladder_target`] take another one (100 bits, for the profiles
/// `Fast100` and `Slim100`).
pub const TARGET_BITS: f64 = 128.0;
/// Most out-of-domain points per fold round that the selection tries.
pub const MAX_SAMPLES: usize = 8;
/// Largest fold grinding the selection accepts.
const MAX_FOLD_GRINDING_BITS: usize = 40;
/// Margin on float comparisons of bits. The script
/// `7-beep-ligerito/scripts/beep_params.py` rechecks every selected level
/// in exact integer arithmetic.
const MARGIN_BITS: f64 = 1e-9;
/// Low index bits of the eq tables of the fold rounds: blocks of `2^10`
/// pairs (32 KiB of table) stay in the first-level cache.
const EQ_LO_BITS: usize = 10;
/// Chunk of the sequential kernels inside a parallel pass.
const CHUNK: usize = 1 << 12;

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------

/// How a squeeze of the ladder is ground.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Grind {
    /// Leading zero bits: a nonce passes with probability `2^-bits`.
    Bits(u32),
    /// A hash below a 64-bit threshold: a nonce passes with probability
    /// `target / 2^64` (module docs).
    Below(u64),
}

impl Grind {
    /// The threshold for a squeeze of numerator `numerator`:
    /// `⌊(2^64 − 1) / numerator⌋`, or no proof of work for a numerator of at
    /// most one.
    pub fn exact(numerator: u64) -> Self {
        Self::exact_at(numerator, TARGET_BITS)
    }

    /// [`Self::exact`] when every challenge must have error below
    /// `2^-target_bits`, for a whole `target_bits ≤ 128`: the largest
    /// threshold `T` with `numerator · T < 2^(64 + 128 − target_bits)`, since
    /// a squeeze of error `numerator / 2^128` behind a proof of work that a
    /// nonce passes with probability `T / 2^64` then has error below
    /// `2^-target_bits`. No proof of work if every nonce may pass, i.e. if
    /// `numerator < 2^(128 − target_bits)`.
    pub fn exact_at(numerator: u64, target_bits: f64) -> Self {
        let slack = LOG_Q - target_bits;
        assert!(
            (0.0..64.0).contains(&slack) && slack.fract() == 0.0,
            "a target of {target_bits} bits over a field of 2^128 elements"
        );
        if numerator <= 1 {
            return Self::Bits(0);
        }
        let threshold = ((1u128 << (64 + slack as u32)) - 1) / u128::from(numerator);
        match u64::try_from(threshold) {
            Ok(threshold) => Self::Below(threshold),
            Err(_) => Self::Bits(0),
        }
    }

    /// Expected hashes of a search: `1 / p` for the pass probability `p`
    /// (zero if there is no proof of work).
    pub fn work(self) -> f64 {
        match self {
            Self::Bits(0) => 0.0,
            Self::Bits(bits) => f64::from(bits).exp2(),
            Self::Below(target) => 64f64.exp2() / target as f64,
        }
    }

    /// `log2` of the work: the bits that the proof of work adds.
    pub fn bits(self) -> f64 {
        match self {
            Self::Bits(bits) => f64::from(bits),
            Self::Below(target) => 64.0 - (target as f64).log2(),
        }
    }
}

/// Proof of work and a squeeze of `n ≥ 1` challenges behind it.
fn grind_vec<Ch: Challenger>(challenger: &mut Ch, grind: Grind, n: usize) -> (u64, Vec<F128>) {
    match grind {
        Grind::Bits(bits) => challenger.grind_pow_and_sample_f128_vec(bits, n),
        Grind::Below(target) => {
            let (nonce, first) = challenger.grind_pow_below_and_sample_f128(target);
            let mut out = Vec::with_capacity(n);
            out.push(first);
            out.extend(challenger.sample_f128_vec(n - 1));
            (nonce, out)
        }
    }
}

/// Verifier mirror of [`grind_vec`].
fn verify_vec<Ch: Challenger>(
    challenger: &mut Ch,
    grind: Grind,
    nonce: u64,
    n: usize,
) -> Option<Vec<F128>> {
    match grind {
        Grind::Bits(bits) => challenger.verify_pow_and_sample_f128_vec(nonce, bits, n),
        Grind::Below(target) => {
            let first = challenger.verify_pow_below_and_sample_f128(nonce, target)?;
            let mut out = Vec::with_capacity(n);
            out.push(first);
            out.extend(challenger.sample_f128_vec(n - 1));
            Some(out)
        }
    }
}

/// The analysis of one BEEP level: what [`beep_ladder`] selected, and the
/// bits of each of its challenges before grinding.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BeepLevel {
    pub log_inv_rate: usize,
    pub log_msg_cols: usize,
    /// Fold rounds of the level (`k`): its table has `2^k` rows.
    pub folds: usize,
    /// Slack above the Johnson agreement `√ρ`.
    pub eta: f64,
    /// Agreement threshold `s = ⌈(√ρ + η) n⌉`.
    pub agreement: u64,
    /// `N = max(n − s + 1, 2)`: the most bad fold challenges on one line.
    pub line_bound: u64,
    /// Integer Johnson list bound `⌊1 / (2 η √ρ)⌋`.
    pub list_size: u64,
    /// Variables of the largest message the level's points evaluate.
    pub max_variables: usize,
    /// Out-of-domain points per fold round (`m`).
    pub samples: usize,
    /// Threshold `t ≥ N + 1` of the analysis (not in the transcript).
    pub threshold: u64,
    /// `−log2` of the error of the points.
    pub sample_bits: f64,
    /// `−log2((t + 3L) / |F|)`: the fold squeeze with the next round's points.
    pub fold_bits: f64,
    pub fold_grinding_bits: usize,
    /// The numerators of the ground squeezes of the level, for a proof of
    /// work with a threshold ([`Grind::exact`]): `t + 3L` for a fold squeeze,
    /// `L + 2` for a squeeze that batches claims, and `L' ⌈log2 Q⌉` for the
    /// one that batches the queries (zero at the last level).
    pub fold_numerator: u64,
    pub claim_numerator: u64,
    pub consistency_numerator: u64,
    pub queries: usize,
    /// `queries · log2(1 / (√ρ + η))`.
    pub query_bits: f64,
    pub query_grinding_bits: usize,
    /// `−log2((L + 1) / |F|)` and its grinding.
    pub claim_batch_bits: f64,
    pub claim_batch_grinding_bits: usize,
    /// `−log2(L' ⌈log2 Q⌉ / |F|)` and its grinding, for the coefficients that
    /// batch the level's queries, with the list bound `L'` of the next level.
    /// The last level batches nothing: `128` and `0`.
    pub consistency_batch_bits: f64,
    pub consistency_batch_grinding_bits: usize,
    pub ood_samples: usize,
    /// Out-of-domain binding of the level's commitment (Flock's formula).
    pub ood_bits: f64,
}

impl BeepLevel {
    /// The least bits, after grinding, over the level's challenges.
    pub fn min_bits(&self) -> f64 {
        [
            self.sample_bits,
            self.fold_bits + self.fold_grinding_bits as f64,
            self.query_bits + self.query_grinding_bits as f64,
            self.claim_batch_bits + self.claim_batch_grinding_bits as f64,
            self.consistency_batch_bits + self.consistency_batch_grinding_bits as f64,
            self.ood_bits,
        ]
        .into_iter()
        .fold(f64::INFINITY, f64::min)
    }

    /// Expected proof-of-work hashes of the level's fold rounds.
    pub fn expected_fold_hashes(&self) -> f64 {
        self.folds as f64 * (self.fold_grinding_bits as f64).exp2()
    }
}

/// A BEEP ladder: Flock's prover and verifier configs, the points per fold
/// round of every level, and the analysis.
#[derive(Clone, Debug)]
pub struct BeepConfig {
    pub prover: ProverConfig,
    pub verifier: VerifierConfig,
    /// Out-of-domain points per fold round, per level (L0, …, L_r).
    pub samples: Vec<usize>,
    pub levels: Vec<BeepLevel>,
    /// How the ladder grinds, per level: the fold squeezes, the squeezes
    /// that batch claims (the binding of the level's commitment and the glue
    /// into the level), and the squeeze that batches the queries of the
    /// level. [`beep_ladder`] fills them with the bits of `prover`;
    /// [`Self::with_exact_grinding`] with thresholds.
    pub fold: Vec<Grind>,
    pub claim: Vec<Grind>,
    pub consistency: Vec<Grind>,
    /// The numerators of the fold squeezes per level and per ROUND, for a
    /// ladder whose fold challenges do not have the same error in every
    /// round of a level ([`mca_ladder_at`]: under mutual correlated
    /// agreement the row union halves from one round to the next). `None`
    /// for the BEEP ladder, whose rounds all have the numerator
    /// [`BeepLevel::fold_numerator`].
    pub fold_round_numerators: Option<Vec<Vec<u64>>>,
    /// The grinds of those squeezes, per level and per round. `None`: every
    /// round of level `li` grinds [`Self::fold`]`[li]`. Read through
    /// [`Self::fold_grind`].
    pub fold_rounds: Option<Vec<Vec<Grind>>>,
    /// The round-by-round target of the ladder ([`TARGET_BITS`], or the one
    /// that [`beep_ladder_at`] was given).
    pub target_bits: f64,
}

impl BeepConfig {
    /// The least bits over all challenges of the ladder, after its proofs of
    /// work ([`Self::fold`], [`Self::claim`], [`Self::consistency`], and the
    /// bits of the queries).
    pub fn min_bits(&self) -> f64 {
        self.levels
            .iter()
            .enumerate()
            .map(|(li, lv)| {
                [
                    lv.sample_bits,
                    self.fold_bits_after_grinding(li),
                    lv.query_bits + lv.query_grinding_bits as f64,
                    lv.claim_batch_bits + self.claim[li].bits(),
                    lv.consistency_batch_bits + self.consistency[li].bits(),
                    lv.ood_bits,
                ]
                .into_iter()
                .fold(f64::INFINITY, f64::min)
            })
            .fold(f64::INFINITY, f64::min)
    }

    /// The grind of the fold squeeze of round `round` (from 0) of level `li`.
    pub fn fold_grind(&self, li: usize, round: usize) -> Grind {
        self.fold_rounds.as_ref().map_or(self.fold[li], |rounds| rounds[li][round])
    }

    /// The least bits, after its proof of work, over the fold squeezes of
    /// level `li`.
    fn fold_bits_after_grinding(&self, li: usize) -> f64 {
        match (&self.fold_round_numerators, &self.fold_rounds) {
            (Some(numerators), Some(grinds)) => numerators[li]
                .iter()
                .zip(&grinds[li])
                .map(|(&numerator, grind)| LOG_Q - (numerator.max(1) as f64).log2() + grind.bits())
                .fold(f64::INFINITY, f64::min),
            _ => self.levels[li].fold_bits + self.fold[li].bits(),
        }
    }

    /// Expected proof-of-work hashes of one proof.
    pub fn expected_pow_hashes(&self) -> f64 {
        self.pow_grinds().expected_hashes()
    }

    /// Set the grinds of the ladder from the bits of `prover` (what
    /// [`beep_ladder`] does; also for a ladder whose bits were changed).
    pub fn sync_bit_grinding(&mut self) {
        let bits = |v: &[usize]| v.iter().map(|&b| Grind::Bits(b as u32)).collect::<Vec<_>>();
        self.fold = bits(&self.prover.fold_grinding_bits);
        self.claim = bits(&self.prover.claim_batch_grinding_bits);
        self.consistency = bits(&self.prover.consistency_batch_grinding_bits);
        // A ladder with a numerator per round: the least whole number of
        // bits for each of them.
        let slack = LOG_Q - self.target_bits;
        self.fold_rounds = self.fold_round_numerators.as_ref().map(|levels| {
            levels
                .iter()
                .map(|rounds| {
                    rounds
                        .iter()
                        .map(|&n| Grind::Bits(strict_grinding_bits((n.max(1) as f64).log2() - slack) as u32))
                        .collect()
                })
                .collect()
        });
    }

    /// The same ladder with every fold, claim-batching and
    /// consistency-batching squeeze ground against a threshold (module
    /// docs): the expected work of a search is about the numerator of its
    /// squeeze, where the bits of [`beep_ladder`] round it up to a power of
    /// two. The transcript and the nonces of a proof change; its size does
    /// not.
    pub fn with_exact_grinding(&self) -> Self {
        let mut out = self.clone();
        let last = self.levels.len() - 1;
        for (li, lv) in self.levels.iter().enumerate() {
            out.fold[li] = Grind::exact_at(lv.fold_numerator, self.target_bits);
            out.claim[li] = Grind::exact_at(lv.claim_numerator, self.target_bits);
            out.consistency[li] = if li < last {
                Grind::exact_at(lv.consistency_numerator, self.target_bits)
            } else {
                Grind::Bits(0)
            };
        }
        out.fold_rounds = self.fold_round_numerators.as_ref().map(|levels| {
            levels
                .iter()
                .map(|rounds| rounds.iter().map(|&n| Grind::exact_at(n, self.target_bits)).collect())
                .collect()
        });
        out
    }

    /// The proof-of-work searches of one proof, in transcript order per
    /// kind, as [`pow_searches`] lists them for the bits of a configuration.
    pub fn pow_grinds(&self) -> PowGrinds {
        let config = &self.prover;
        let levels = config.recursive_steps + 1;
        let folds = |li: usize| {
            if li == 0 {
                config.initial_k
            } else {
                config.recursive_ks[li - 1]
            }
        };
        let mut out = PowGrinds::default();
        for li in 0..levels {
            out.fold.extend((0..folds(li)).map(|round| self.fold_grind(li, round)));
            if config.ood_samples[li] > 0 {
                out.claim.push(self.claim[li]);
            }
            out.queries.push(Grind::Bits(config.grinding_bits[li] as u32));
            if li + 1 < levels {
                out.consistency.push(self.consistency[li]);
                out.claim.push(self.claim[li + 1]);
            }
        }
        out
    }

    /// The same ladder with other fold grinding bits per level. This is an
    /// accounting experiment and NOT a configuration that the analysis of
    /// this module supports: the points, the samples and the transcript are
    /// unchanged, and only the proof of work of the fold challenges differs.
    /// `levels` keeps the analysis of [`beep_ladder`], so [`Self::min_bits`]
    /// does not describe the result. The bench uses it for the question
    /// "what if a fold challenge were charged the error of the affine fold"
    /// (`7-beep-ligerito/scripts/beep_params.py --beep-affine-charge`).
    pub fn with_fold_grinding(&self, bits: &[usize]) -> Result<Self, String> {
        if bits.len() != self.levels.len() {
            return Err(format!(
                "{} fold grindings for {} levels",
                bits.len(),
                self.levels.len()
            ));
        }
        if bits.iter().any(|&b| b > MAX_FOLD_GRINDING_BITS) {
            return Err(format!("fold grinding above {MAX_FOLD_GRINDING_BITS} bits"));
        }
        let mut out = self.clone();
        out.prover.fold_grinding_bits = bits.to_vec();
        out.verifier.fold_grinding_bits = bits.to_vec();
        out.fold = bits.iter().map(|&b| Grind::Bits(b as u32)).collect();
        out.fold_rounds = None;
        out.fold_round_numerators = None;
        Ok(out)
    }

    /// The same ladder with no out-of-domain binding sample on the first
    /// commitment (level 0).
    ///
    /// The ladder of [`beep_ladder`] keeps the binding sample that Flock's
    /// ladders draw right after the L0 root. The construction of the paper
    /// (BEEP folds, then a code switch whose out-of-domain samples bind the
    /// NEW commitment) has no such sample on its input oracle: its theorem
    /// carries the list of the first code through the fold rounds, which is
    /// what the terms `2L` and `L` of the fold squeeze are. Under Flock's
    /// own convention the sample is not needed either: the `m` points of the
    /// first fold round are drawn in one message right after the root, the
    /// prover answers the two halves of the committed table at them before
    /// any other challenge, and the sumcheck enforces the answers, so two
    /// codewords of the list survive them with probability at most
    /// `C(L, 2) (μ / |F|)^m`, where `μ` is the number of variables of a half.
    /// This function removes the sample and records that bound as the
    /// binding of level 0. The later levels keep their samples: there the
    /// binding must come before the queries of the code switch.
    pub fn without_first_binding(&self) -> Result<Self, String> {
        let mut out = self.clone();
        let l0 = &mut out.levels[0];
        let list = l0.list_size as f64;
        // Two distinct codewords of the list differ on one half, whose
        // multilinear extension has `max_variables` variables.
        let pairs = (list * (list - 1.0) / 2.0).max(1.0);
        let bits = l0.samples as f64 * (LOG_Q - (l0.max_variables.max(1) as f64).log2()) - pairs.log2();
        if l0.samples == 0 || bits < self.target_bits {
            return Err(format!(
                "the {} points of the first fold round bind the first commitment with {bits:.1} bits",
                l0.samples
            ));
        }
        l0.ood_samples = 0;
        l0.ood_bits = bits;
        out.prover.ood_samples[0] = 0;
        out.verifier.ood_samples[0] = 0;
        Ok(out)
    }
}

/// The proof-of-work searches of one proof of a BEEP ladder
/// ([`BeepConfig::pow_grinds`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PowGrinds {
    /// One per fold round.
    pub fold: Vec<Grind>,
    /// The coefficients that batch claims.
    pub claim: Vec<Grind>,
    /// The coefficients that batch the queries of a level.
    pub consistency: Vec<Grind>,
    /// The query positions of every level.
    pub queries: Vec<Grind>,
}

impl PowGrinds {
    /// Every search, by kind.
    pub fn all(&self) -> impl Iterator<Item = Grind> + '_ {
        self.fold
            .iter()
            .chain(&self.claim)
            .chain(&self.consistency)
            .chain(&self.queries)
            .copied()
    }

    /// Expected hashes of all the searches.
    pub fn expected_hashes(&self) -> f64 {
        self.all().map(Grind::work).sum()
    }

    /// The searches of the bits of a configuration ([`pow_searches`]).
    pub fn from_bits(searches: &PowSearches) -> Self {
        let bits = |v: &[usize]| v.iter().map(|&b| Grind::Bits(b as u32)).collect::<Vec<_>>();
        Self {
            fold: bits(&searches.fold),
            claim: bits(&searches.claim),
            consistency: bits(&searches.consistency),
            queries: bits(&searches.queries),
        }
    }
}

/// The opening that a configuration belongs to, for [`pow_searches`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ladder {
    /// Flock's Ligerito with fold challenges in `F256` (`extension.rs`).
    Split,
    /// The affine ladder on a dense L0 (`affine.rs`).
    Affine,
    /// The BEEP ladder of this module.
    Beep,
}

/// The proof-of-work searches of one proof: the bits of each search, grouped
/// by the vector of the proof that holds its nonce, in transcript order. A
/// search of 0 bits hashes nothing, but it has a nonce.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PowSearches {
    /// One per fold round.
    pub fold: Vec<usize>,
    /// The coefficients that batch claims: the binding values of every
    /// commitment, and one glue per code switch.
    pub claim: Vec<usize>,
    /// The coefficients that batch the queries of a level.
    pub consistency: Vec<usize>,
    /// The query positions of every level.
    pub queries: Vec<usize>,
}

impl PowSearches {
    /// Every search, by kind.
    pub fn all(&self) -> impl Iterator<Item = usize> + '_ {
        self.fold
            .iter()
            .chain(&self.claim)
            .chain(&self.consistency)
            .chain(&self.queries)
            .copied()
    }

    /// Expected hashes: `2^bits` per search of at least one bit.
    pub fn expected_hashes(&self) -> f64 {
        self.all()
            .filter(|&bits| bits > 0)
            .map(|bits| (bits as f64).exp2())
            .sum()
    }
}

/// The proof-of-work searches of one proof under `config`.
///
/// Per level: one search per fold round; the binding of the level's
/// commitment (one search per out-of-domain sample in the split and affine
/// ladders, which draw a coefficient after every sample, and one search in
/// all in the BEEP ladder); the queries; and, at a code switch, the
/// coefficients that batch the queries and the glue coefficient. The split
/// prover also grinds these last two at its final level, where the other two
/// ladders check the final message directly.
///
/// The split configurations at 128 bits have no fold grinding, and this
/// function does not model one that has.
pub fn pow_searches(config: &ProverConfig, ladder: Ladder) -> PowSearches {
    let levels = config.recursive_steps + 1;
    let folds = |li: usize| {
        if li == 0 {
            config.initial_k
        } else {
            config.recursive_ks[li - 1]
        }
    };
    let mut out = PowSearches::default();
    for li in 0..levels {
        if ladder == Ladder::Split {
            assert_eq!(
                config.fold_grinding_bits[li], 0,
                "a split ladder with fold grinding is not modelled"
            );
        } else {
            out.fold
                .extend(std::iter::repeat_n(config.fold_grinding_bits[li], folds(li)));
        }
        let binds = match ladder {
            Ladder::Beep => usize::from(config.ood_samples[li] > 0),
            Ladder::Split | Ladder::Affine => config.ood_samples[li],
        };
        out.claim
            .extend(std::iter::repeat_n(config.claim_batch_grinding_bits[li], binds));
        out.queries.push(config.grinding_bits[li]);
        if li + 1 < levels {
            out.consistency.push(config.consistency_batch_grinding_bits[li]);
            out.claim.push(config.claim_batch_grinding_bits[li + 1]);
        } else if ladder == Ladder::Split {
            out.consistency.push(config.consistency_batch_grinding_bits[li]);
            out.claim.push(config.claim_batch_grinding_bits[li]);
        }
    }
    out
}

/// The affine ladder of [`affine_ladder`] at a slack per level.
///
/// [`affine_ladder`] fixes the slack `η = 0.02` of the `Fast` profile. This
/// function applies the same rules at the slack `etas[level]`: the queries
/// (with the agreement loss of the affine fold), and the grinding of the
/// claim-batching and consistency-batching coefficients, by Flock's
/// [`algebraic_grinding_schedule`]. `fold_grinding_bits` must come from a
/// certificate of every fold round at that slack
/// (`7-beep-ligerito/scripts/beep_params.py --affine-ladder`). The affine
/// prover and verifier are not changed: only their configuration is.
pub fn affine_ladder_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    fold_grinding_bits: &[usize],
) -> Result<(ProverConfig, VerifierConfig), String> {
    affine_ladder_target(split, log_n, rates, etas, fold_grinding_bits, TARGET_BITS)
}

/// [`affine_ladder_at`] for a round-by-round target of `target_bits` bits in
/// place of 128: the queries of a level reach `target_bits` with the query
/// grinding of `split`, and the coefficients that batch claims and queries
/// are ground for `target_bits` (the numerators of Flock's schedule, over
/// the field of `2^128` elements). `fold_grinding_bits` must be the grinding
/// of the certificates for that target
/// (`7-beep-ligerito/scripts/beep_params.py --affine-ladder .. lam=..`). The
/// binding samples are those of `split`.
pub fn affine_ladder_target(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    fold_grinding_bits: &[usize],
    target_bits: f64,
) -> Result<(ProverConfig, VerifierConfig), String> {
    if etas.len() != rates.len() || fold_grinding_bits.len() != rates.len() {
        return Err("an affine ladder needs one slack and one fold grinding per level".into());
    }
    let (mut prover, mut verifier) = affine_ladder(split, log_n, rates, fold_grinding_bits);
    let shapes = level_shapes(log_n, prover.initial_k, &prover.recursive_ks);
    for (li, (&(k, c), (&rate, &eta))) in shapes.iter().zip(rates.iter().zip(etas)).enumerate() {
        let a = (-(rate as f64)).exp2().sqrt() + eta;
        if !(eta > 0.0 && a < 1.0) {
            return Err(format!("level {li}: agreement {a} is not below 1"));
        }
        // The rule of `affine_ladder`, at this slack.
        let per_query = -a.log2();
        let n = ((c + rate) as f64).exp2();
        let loss = (1.0 + k as f64 / (a * n)).log2();
        let need = target_bits - split.grinding_bits[li] as f64;
        prover.queries[li] = (need / (per_query - loss) - 1e-9).ceil() as usize;
        let (claim, _, consistency, claim_bits, _, consistency_bits) =
            algebraic_grinding_schedule(rate, Some(eta), prover.queries[li]);
        // Flock's schedule grinds for 128 bits. For another target: the same
        // errors (`claim_bits`, `consistency_bits` are their bits before
        // grinding), ground for it.
        let (claim, consistency) = if target_bits == TARGET_BITS {
            (claim, consistency)
        } else {
            (
                strict_grinding_bits(target_bits - claim_bits),
                strict_grinding_bits(target_bits - consistency_bits),
            )
        };
        prover.claim_batch_grinding_bits[li] = claim;
        prover.consistency_batch_grinding_bits[li] = consistency;
        let mu = k + c;
        let ood_bits = paper_ood_bits(
            rate,
            eta,
            mu,
            prover.ood_samples[li],
            (li == 0).then_some(mu + crate::pcs::LOG_PACKING),
        );
        if ood_bits < target_bits {
            return Err(format!("level {li}: out-of-domain binding has {ood_bits:.1} bits"));
        }
    }
    prover = prover.with_default_stratified();
    verifier.queries = prover.queries.clone();
    verifier.claim_batch_grinding_bits = prover.claim_batch_grinding_bits.clone();
    verifier.consistency_batch_grinding_bits = prover.consistency_batch_grinding_bits.clone();
    verifier.stratified = prover.stratified.clone();
    Ok((prover, verifier))
}

/// `−log2` of the error of `m` points at threshold `t`:
/// `(|F| L)^3 (μ / |F|)^m / (t (t − 1) (t − N))`.
fn sample_bits(list: u64, variables: usize, samples: usize, line_bound: u64, t: u128) -> f64 {
    debug_assert!(t > u128::from(line_bound));
    samples as f64 * (LOG_Q - (variables as f64).log2()) - 3.0 * (LOG_Q + (list as f64).log2())
        + (t as f64).log2()
        + ((t - 1) as f64).log2()
        + ((t - u128::from(line_bound)) as f64).log2()
}

/// The least threshold `t ≥ N + 1` at which `m` points reach the target, or
/// `None` if none below `2^100` does.
fn least_threshold(
    list: u64,
    variables: usize,
    samples: usize,
    line_bound: u64,
    target_bits: f64,
) -> Option<u128> {
    let reaches =
        |t: u128| sample_bits(list, variables, samples, line_bound, t) >= target_bits + MARGIN_BITS;
    let lo = u128::from(line_bound) + 1;
    let hi = 1u128 << 100;
    if !reaches(hi) {
        return None;
    }
    let (mut lo, mut hi) = (lo, hi);
    if reaches(lo) {
        return Some(lo);
    }
    // Invariant: !reaches(lo), reaches(hi); the bits increase with t.
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if reaches(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    Some(hi)
}

/// The points and the threshold of a level: for every `m ≤ MAX_SAMPLES` the
/// least threshold whose points reach the target with no grinding and the
/// fold grinding that it needs; then the least fold grinding, and among
/// those the fewest points. Returns `(m, t, fold grinding bits)`.
fn select_fold(
    list: u64,
    variables: usize,
    line_bound: u64,
    target_bits: f64,
) -> Result<(usize, u128, usize), String> {
    let mut best: Option<(usize, u128, usize)> = None;
    for m in 1..=MAX_SAMPLES {
        let Some(t) = least_threshold(list, variables, m, line_bound, target_bits) else {
            continue;
        };
        // The fold squeeze has error `(t + 3L) / 2^128`: the bits that bring
        // it below `2^-target_bits`.
        let grind = strict_grinding_bits(
            ((t + 3 * u128::from(list)) as f64).log2() - (LOG_Q - target_bits),
        );
        if grind > MAX_FOLD_GRINDING_BITS {
            continue;
        }
        if best.is_none_or(|(_, _, g)| grind < g) {
            best = Some((m, t, grind));
        }
    }
    best.ok_or_else(|| {
        format!(
            "no m <= {MAX_SAMPLES} reaches {target_bits} bits within {MAX_FOLD_GRINDING_BITS} \
             bits of fold grinding (L = {list}, N = {line_bound}, {variables} variables)"
        )
    })
}

/// A BEEP ladder on the native shapes of `split`: `rates.len()` levels (L0
/// and `rates.len() − 1` recursive levels) at the rates `rates`, each
/// analyzed at agreement `√ρ + etas[level]` with the Johnson list bound.
/// The query grinding and the out-of-domain samples per level are those of
/// `split`; the queries, the points per fold round and every other grinding
/// are derived here (module docs).
pub fn beep_ladder(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
) -> Result<BeepConfig, String> {
    beep_ladder_at(split, log_n, rates, etas, TARGET_BITS)
}

/// [`beep_ladder`] for a round-by-round target of `target_bits` bits in
/// place of 128, over the same field of `2^128` elements: the points and
/// the threshold of every level, its queries, and the grinding of every
/// squeeze are selected for that target. With 100 bits the fold squeeze
/// `(t + 3L) / 2^128` needs no grinding as long as `t + 3L < 2^28`.
pub fn beep_ladder_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    target_bits: f64,
) -> Result<BeepConfig, String> {
    // Bits of every challenge that the target leaves unused.
    let slack = LOG_Q - target_bits;
    if !(0.0..64.0).contains(&slack) || slack.fract() != 0.0 {
        return Err(format!("a target of {target_bits} bits over a field of 2^128 elements"));
    }
    let levels = rates.len();
    if levels < 2 || etas.len() != levels {
        return Err("a BEEP ladder needs one eta per level and at least two levels".into());
    }
    let ks = native_ks(split, log_n, levels - 1);
    if ks.len() + 1 != levels {
        return Err("ladder deeper than the native shapes".into());
    }
    let shapes = level_shapes(log_n, split.initial_k, &ks);
    let mut out = Vec::with_capacity(levels);
    for li in 0..levels {
        let ((k, c), rate, eta) = (shapes[li], rates[li], etas[li]);
        let rho = (-(rate as f64)).exp2();
        let theta = rho.sqrt() + eta;
        if !(eta > 0.0 && theta < 1.0) {
            return Err(format!("level {li}: agreement {theta} is not below 1"));
        }
        let n = 1u64 << (c + rate);
        let agreement = (theta * n as f64).ceil() as u64;
        let line_bound = (n - agreement + 1).max(2);
        let list_real = 1.0 / (2.0 * eta * rho.sqrt());
        let list_size = (list_real.floor() as u64).max(1);
        // Round j of the level evaluates messages of k − j + c variables.
        let max_variables = k + c - 1;
        let (samples, threshold, fold_grinding_bits) =
            select_fold(list_size, max_variables.max(1), line_bound, target_bits)
                .map_err(|e| format!("level {li}: {e}"))?;
        let per_query = -theta.log2();
        let query_grinding_bits = split.grinding_bits[li];
        let queries = strict_query_count(target_bits, query_grinding_bits, per_query);
        // Filled below, once the list of the next level is known.
        let (consistency_batch_grinding_bits, consistency_batch_bits) = (0, LOG_Q);
        let claim_num = (list_real + 1.0).log2();
        let ood_samples = split.ood_samples[li];
        let mu = k + c;
        let ood_bits = paper_ood_bits(
            rate,
            eta,
            mu,
            ood_samples,
            (li == 0).then_some(mu + crate::pcs::LOG_PACKING),
        );
        if ood_bits < target_bits {
            return Err(format!("level {li}: out-of-domain binding has {ood_bits:.1} bits"));
        }
        out.push(BeepLevel {
            log_inv_rate: rate,
            log_msg_cols: c,
            folds: k,
            eta,
            agreement,
            line_bound,
            list_size,
            max_variables,
            samples,
            threshold: u64::try_from(threshold).map_err(|_| "threshold above 2^64")?,
            sample_bits: sample_bits(list_size, max_variables.max(1), samples, line_bound, threshold),
            fold_bits: LOG_Q - ((threshold + 3 * u128::from(list_size)) as f64).log2(),
            fold_grinding_bits,
            fold_numerator: u64::try_from(threshold + 3 * u128::from(list_size))
                .map_err(|_| "fold numerator above 2^64")?,
            // The real list bound is below `list_size + 1`.
            claim_numerator: list_size + 2,
            consistency_numerator: 0,
            queries,
            query_bits: queries as f64 * per_query,
            query_grinding_bits,
            claim_batch_bits: LOG_Q - claim_num,
            claim_batch_grinding_bits: strict_grinding_bits(claim_num - slack),
            consistency_batch_bits,
            consistency_batch_grinding_bits,
            ood_samples,
            ood_bits,
        });
    }
    // The coefficients that batch the queries of level `li`: one wrong
    // candidate of the next commitment passes with probability at most
    // `⌈log2 Q⌉ / |F|`, and there are at most `L_{li+1}` candidates.
    for li in 0..levels - 1 {
        let degree = ceil_log2(out[li].queries).max(1);
        let log_num = (out[li + 1].list_size as f64 * degree as f64).log2();
        out[li].consistency_batch_bits = LOG_Q - log_num;
        out[li].consistency_batch_grinding_bits = strict_grinding_bits(log_num - slack);
        out[li].consistency_numerator = out[li + 1].list_size * degree as u64;
    }
    let field = |f: fn(&BeepLevel) -> usize| out.iter().map(f).collect::<Vec<usize>>();
    let prover = ProverConfig {
        log_inv_rates: rates.to_vec(),
        recursive_steps: ks.len(),
        initial_log_msg_cols: log_n - split.initial_k,
        initial_log_num_interleaved: split.initial_k,
        initial_k: split.initial_k,
        recursive_log_msg_cols: shapes[1..].iter().map(|s| s.1).collect(),
        recursive_ks: ks,
        queries: field(|l| l.queries),
        grinding_bits: field(|l| l.query_grinding_bits),
        fold_grinding_bits: field(|l| l.fold_grinding_bits),
        claim_batch_grinding_bits: field(|l| l.claim_batch_grinding_bits),
        consistency_batch_grinding_bits: field(|l| l.consistency_batch_grinding_bits),
        ood_samples: field(|l| l.ood_samples),
        merkle_hash: split.merkle_hash,
        stratified: vec![],
    }
    .with_default_stratified();
    let verifier = VerifierConfig {
        log_inv_rates: prover.log_inv_rates.clone(),
        recursive_steps: prover.recursive_steps,
        initial_log_msg_cols: prover.initial_log_msg_cols,
        initial_log_num_interleaved: prover.initial_log_num_interleaved,
        initial_k: prover.initial_k,
        recursive_log_msg_cols: prover.recursive_log_msg_cols.clone(),
        recursive_ks: prover.recursive_ks.clone(),
        queries: prover.queries.clone(),
        grinding_bits: prover.grinding_bits.clone(),
        fold_grinding_bits: prover.fold_grinding_bits.clone(),
        claim_batch_grinding_bits: prover.claim_batch_grinding_bits.clone(),
        consistency_batch_grinding_bits: prover.consistency_batch_grinding_bits.clone(),
        ood_samples: prover.ood_samples.clone(),
        merkle_hash: prover.merkle_hash,
        stratified: prover.stratified.clone(),
    };
    let mut config = BeepConfig {
        prover,
        verifier,
        samples: field(|l| l.samples),
        levels: out,
        fold: Vec::new(),
        claim: Vec::new(),
        consistency: Vec::new(),
        fold_round_numerators: None,
        fold_rounds: None,
        target_bits,
    };
    config.sync_bit_grinding();
    if config.min_bits() < target_bits {
        return Err(format!("the ladder reaches only {:.2} bits", config.min_bits()));
    }
    Ok(config)
}

/// [`BeepLevel::sample_bits`] of a level with no out-of-domain points: there
/// is no such challenge, so it never is the least term of a ladder.
pub const NO_POINTS_BITS: f64 = 1e9;

/// "Ligerito over GF(2^128)": the ladder of [`beep_ladder_at`] with NO
/// out-of-domain points in its fold rounds, i.e. the scalar fold of a
/// sumcheck round alone, with every challenge in `F128`, and with its folds
/// analyzed with mutual correlated agreement as Flock analyzes them. The
/// baseline of the comparison at 100 bits (the shapes, the rates, the
/// queries' rule, the binding samples, the batching and the prover are those
/// of the BEEP ladder; only the fold rounds differ).
///
/// The fold challenge of round `j` (from 0) of a level with `2^k` rows is
/// charged `(a_j + 2L) / |F|`:
///
/// * `a_j / |F|` is Flock's bound for a fold under MCA at the agreement `√ρ
///   + η` (its Appendix C.3: BCHKS25, Theorem 4.6, for a fold of two words,
///   times the row union of the round, `2^(k−1−j)`: the round folds that
///   many pairs of rows). `paper_johnson_log_a` of flock-core is `log2 a_0`,
///   the worst round, which Flock evaluates over a field of `2^256` elements
///   and we evaluate over `F128`;
/// * `2L / |F|` is the sumcheck round under the list, as in the BEEP ladder.
///
/// Each fold challenge is ground for the error of ITS round. Flock binds the
/// grinding of a whole level to the worst round, which costs it nothing
/// (over a field of `2^256` elements there is no fold grinding). Here the
/// grinding is real, and with the worst round in every round a level with
/// `2^6` rows would try three times the hashes that it needs. Over `F128`
/// this is only practical below 128 bits: at 128 bits the first round would
/// take `log2 a_0`, i.e. 37 to 45 bits on Flock's shapes. The ladder keeps
/// the binding sample that Flock's ladders draw on the first commitment
/// (there are no points of a first fold round to bind it).
///
/// The analysis fields of the returned levels describe the worst round of
/// this ladder: `samples = 0`, `threshold = 0`, `sample_bits =
/// `[`NO_POINTS_BITS`], `fold_bits = −log2((a_0 + 2L) / |F|)` and
/// `fold_numerator = ⌈a_0 + 2L⌉`. The numerators of all the rounds are in
/// [`BeepConfig::fold_round_numerators`], and their grinds in
/// [`BeepConfig::fold_rounds`].
pub fn mca_ladder_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    target_bits: f64,
) -> Result<BeepConfig, String> {
    let mut config = beep_ladder_at(split, log_n, rates, etas, target_bits)?;
    let slack = LOG_Q - target_bits;
    let mut round_numerators: Vec<Vec<u64>> = Vec::with_capacity(config.levels.len());
    for (li, lv) in config.levels.iter_mut().enumerate() {
        let rho = (-(lv.log_inv_rate as f64)).exp2();
        let list_real = 1.0 / (2.0 * lv.eta * rho.sqrt());
        // `log2 a_0`: the bound of a fold of two words, with the row union
        // `2^(folds − 1)` of the first round. Round `j` folds `2^(folds − 1 − j)`
        // pairs of rows, so `a_j = a_0 / 2^j`.
        assert!(lv.folds >= 1, "a level folds at least two rows");
        let log_a = super::paper_johnson_log_a(lv.log_inv_rate, lv.eta, lv.log_msg_cols, lv.folds);
        let numerators: Vec<f64> = (0..lv.folds)
            .map(|j| ((log_a - j as f64).exp2() + 2.0 * list_real).ceil())
            .collect();
        let numerator = numerators[0];
        if !(numerator.is_finite() && numerator < 2f64.powi(63)) {
            return Err(format!("level {li}: the MCA numerator 2^{log_a:.1} is too large"));
        }
        let grind = strict_grinding_bits(numerator.log2() - slack);
        if grind > MAX_FOLD_GRINDING_BITS {
            return Err(format!(
                "level {li}: a fold under MCA needs {grind} bits of grinding over GF(2^128) \
                 (above {MAX_FOLD_GRINDING_BITS})"
            ));
        }
        lv.samples = 0;
        lv.threshold = 0;
        lv.sample_bits = NO_POINTS_BITS;
        lv.fold_bits = LOG_Q - numerator.log2();
        lv.fold_grinding_bits = grind;
        lv.fold_numerator = numerator as u64;
        round_numerators.push(numerators.iter().map(|&n| n as u64).collect());
    }
    config.samples = vec![0; config.levels.len()];
    let fold: Vec<usize> = config.levels.iter().map(|l| l.fold_grinding_bits).collect();
    config.prover.fold_grinding_bits = fold.clone();
    config.verifier.fold_grinding_bits = fold;
    config.fold_round_numerators = Some(round_numerators);
    config.sync_bit_grinding();
    if config.min_bits() < target_bits {
        return Err(format!("the MCA ladder reaches only {:.2} bits", config.min_bits()));
    }
    Ok(config)
}

/// [`mca_ladder_at`] with no out-of-domain sample on the first commitment:
/// the baseline that differs from the BEEP ladder of the comparison
/// ([`BeepConfig::without_first_binding`]) in its fold rounds only.
///
/// [`mca_ladder_at`] keeps Flock's sample, since under Flock's convention
/// something has to bind the first commitment to one codeword before its
/// fold rounds, and this ladder has no points of a first fold round to do
/// it. Under the convention of the paper (and of WHIR) nothing has to: the
/// list of the first code is carried through its fold rounds, which is what
/// the term `2L` of a fold challenge pays for, and [`mca_ladder_at`] already
/// charges it. So the sample goes and nothing else changes: the fold
/// challenges keep their numerators `⌈a + 2L⌉`, and level 0 has no binding
/// term (`ood_bits = `[`NO_POINTS_BITS`]). The later levels keep their
/// samples, which bind the new commitments before their queries.
pub fn mca_ladder_no_first_sample_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    target_bits: f64,
) -> Result<BeepConfig, String> {
    let mut config = mca_ladder_at(split, log_n, rates, etas, target_bits)?;
    let l0 = &mut config.levels[0];
    l0.ood_samples = 0;
    l0.ood_bits = NO_POINTS_BITS;
    config.prover.ood_samples[0] = 0;
    config.verifier.ood_samples[0] = 0;
    if config.min_bits() < target_bits {
        return Err(format!("the MCA ladder reaches only {:.2} bits", config.min_bits()));
    }
    Ok(config)
}

/// The bound of Dao, Kominers and Thaler (ePrint 2026/2056, Theorem 4.4,
/// "Quantitative Johnson MCA in every characteristic") on the exceptional
/// challenges of a line of two words, for the Reed–Solomon code of length
/// `n` and dimension `dim` at the agreement threshold `agreement`. For every
/// two words `f, g` there is a set of at most this many challenges `z`
/// outside which every codeword that agrees with `f + z g` on at least
/// `agreement` positions is `F_0 + z G_0`, for codewords `F_0, G_0` that
/// agree with `f` and `g` on exactly those positions. The theorem holds
/// over any field (binary fields included) and for any distinct evaluation
/// points.
///
/// In the notation of the theorem: `D = dim − 1`, `A = agreement` and `η_0 =
/// A/n − √(D/n)`, which must be positive. Then `m = max(⌈√(D/n) / (2 η_0)⌉,
/// 3)`, `t = m + 1/2`, `B_jet = ⌈t √(n/D)⌉ − 1`, `B_Z = ⌈t² n / (3D)⌉ − 1`,
/// `Ψ = 1 + (2D − 1)(2 B_jet − 1) + 2 (B_jet − 2D − 1)_+`, and the count is
///
///   `(2 B_jet − 1) B_Z + (n − D)/(A − D) · (B_jet + B_Z Ψ) + (n − D − 1) B_jet`
///
/// (its equations (33), (34), (36), (37) and (39), with `L = D + 1` and a
/// line, `ℓ = 1`), which the theorem also bounds by `(8/3) n t³ / (D/n)`.
/// Everything is computed in integers: `m` is the least integer `≥ 3` with
/// `4 m² A² ≥ (2m + 1)² D n`, `B_jet` the largest integer with `4 D B_jet² <
/// (2m + 1)² n`, `B_Z` the largest one with `12 D B_Z < (2m + 1)² n`, and the
/// quotient is rounded up.
pub fn dkt_exceptional_count(n: u64, dim: u64, agreement: u64) -> Result<u128, String> {
    /// Largest `m` that the search tries: `η_0 n` is then about `√(D n) / 2^21`.
    const MAX_M: u128 = 1 << 20;
    let none = || format!("no bound of DKT26 for n = {n}, dimension {dim}, agreement {agreement}");
    if n > 1 << 32 {
        return Err(none());
    }
    let (n, a) = (u128::from(n), u128::from(agreement));
    let d = u128::from(dim).checked_sub(1).ok_or_else(none)?;
    // The theorem needs 1 ≤ D ≤ n − 2 and an agreement above its Johnson
    // bound, A² > n D (then A > D).
    if d == 0 || d + 2 > n || a > n || a * a <= n * d {
        return Err(none());
    }
    // 2 m η_0 ≥ √(D/n), i.e. 4 m² A² ≥ (2m + 1)² D n: true from some m on.
    let enough = |m: u128| 4 * m * m * a * a >= (2 * m + 1) * (2 * m + 1) * d * n;
    if !enough(MAX_M) {
        return Err(none());
    }
    let m = if enough(3) {
        3
    } else {
        // Invariant: !enough(lo), enough(hi).
        let (mut lo, mut hi) = (3u128, MAX_M);
        while hi - lo > 1 {
            let mid = lo + (hi - lo) / 2;
            if enough(mid) {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        hi
    };
    // (2t)² n, with t = m + 1/2.
    let t2n = (2 * m + 1) * (2 * m + 1) * n;
    // The largest j with 4 D j² < (2t)² n: the integer square root of ⌊((2t)² n − 1) / (4D)⌋.
    let below = (t2n - 1) / (4 * d);
    let mut b_jet = (below as f64).sqrt() as u128;
    while b_jet * b_jet > below {
        b_jet -= 1;
    }
    while (b_jet + 1) * (b_jet + 1) <= below {
        b_jet += 1;
    }
    let b_z = (t2n - 1) / (12 * d);
    let overflow = || "the count of DKT26 does not fit 128 bits".to_string();
    let psi = (2 * d - 1)
        .checked_mul(2 * b_jet - 1)
        .and_then(|x| x.checked_add(1 + 2 * b_jet.saturating_sub(2 * d + 1)))
        .ok_or_else(overflow)?;
    let joint = b_z
        .checked_mul(psi)
        .and_then(|x| x.checked_add(b_jet))
        .and_then(|x| x.checked_mul(n - d))
        .ok_or_else(overflow)?;
    let off_graphs = joint.div_ceil(a - d);
    (2 * b_jet - 1)
        .checked_mul(b_z)
        .and_then(|x| x.checked_add(off_graphs))
        .and_then(|x| x.checked_add((n - d - 1) * b_jet))
        .ok_or_else(overflow)
}

/// "Ligerito over GF(2^128)" with its folds analyzed with the bound of
/// DKT26 in place of Flock's: [`mca_ladder_at`] with the fold challenge of
/// every round charged `(E + 2L) / |F|`, where `E` is
/// [`dkt_exceptional_count`] for the code of the level at the agreement
/// `⌈(√ρ + η) n⌉` of the level, and `2L / |F|` is the sumcheck round under
/// the list, as before. Nothing else differs from [`mca_ladder_at`]: the
/// shapes, the rates, the queries, the binding samples, the batching and the
/// prover are those of the BEEP ladder at the same slacks, with no
/// out-of-domain points in the fold rounds.
///
/// Two things change against Flock's bound (BCHKS25, Theorem 4.6, times a
/// row union):
///
/// * the count of exceptional challenges of a fold of two words: about `(8/3)
///   n (m + 1/2)³ / ρ` in place of `2 (m + 1/2)⁵ n / (3 ρ^(3/2))`, with the
///   same `m ≈ √ρ / (2η)`, so `η^-3` in place of `η^-5`;
/// * no row union: an interleaved code has the exceptional count of the
///   code, at every width (Lemma 6.5 and Corollary 6.6 of DKT26, after Jo,
///   ePrint 2026/891: one combination of the rows keeps every bad challenge
///   bad). A round that folds `2^j` pairs of rows is one line of two words
///   of an interleaved code, so every round of a level has the same
///   numerator, and `fold_round_numerators` is `None` as in the BEEP ladder.
///
/// The analysis fields of the returned levels are those of [`mca_ladder_at`]
/// (`samples = 0`, `threshold = 0`, `sample_bits = `[`NO_POINTS_BITS`]), with
/// `fold_numerator = E + ⌈2L⌉` and `fold_bits = −log2((E + ⌈2L⌉) / |F|)`.
pub fn mca_dkt_ladder_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    target_bits: f64,
) -> Result<BeepConfig, String> {
    let mut config = beep_ladder_at(split, log_n, rates, etas, target_bits)?;
    let slack = LOG_Q - target_bits;
    for (li, lv) in config.levels.iter_mut().enumerate() {
        let rho = (-(lv.log_inv_rate as f64)).exp2();
        let list_real = 1.0 / (2.0 * lv.eta * rho.sqrt());
        let n = 1u64 << (lv.log_msg_cols + lv.log_inv_rate);
        let count = dkt_exceptional_count(n, 1u64 << lv.log_msg_cols, lv.agreement)
            .map_err(|e| format!("level {li}: {e}"))?;
        let numerator = count + (2.0 * list_real).ceil() as u128;
        if numerator >= 1 << 63 {
            return Err(format!("level {li}: the MCA numerator {numerator} is too large"));
        }
        let numerator = numerator as u64;
        let log_num = (numerator as f64).log2();
        let grind = strict_grinding_bits(log_num - slack);
        if grind > MAX_FOLD_GRINDING_BITS {
            return Err(format!(
                "level {li}: a fold under MCA (DKT26) needs {grind} bits of grinding over GF(2^128) \
                 (above {MAX_FOLD_GRINDING_BITS})"
            ));
        }
        lv.samples = 0;
        lv.threshold = 0;
        lv.sample_bits = NO_POINTS_BITS;
        lv.fold_bits = LOG_Q - log_num;
        lv.fold_grinding_bits = grind;
        lv.fold_numerator = numerator;
    }
    config.samples = vec![0; config.levels.len()];
    let fold: Vec<usize> = config.levels.iter().map(|l| l.fold_grinding_bits).collect();
    config.prover.fold_grinding_bits = fold.clone();
    config.verifier.fold_grinding_bits = fold;
    config.sync_bit_grinding();
    if config.min_bits() < target_bits {
        return Err(format!("the MCA ladder (DKT26) reaches only {:.2} bits", config.min_bits()));
    }
    Ok(config)
}

/// [`mca_dkt_ladder_at`] with no out-of-domain sample on the first
/// commitment, as [`mca_ladder_no_first_sample_at`] is to
/// [`mca_ladder_at`]: the baseline that differs from the BEEP ladder of the
/// comparison in its fold rounds only.
pub fn mca_dkt_ladder_no_first_sample_at(
    split: &ProverConfig,
    log_n: usize,
    rates: &[usize],
    etas: &[f64],
    target_bits: f64,
) -> Result<BeepConfig, String> {
    let mut config = mca_dkt_ladder_at(split, log_n, rates, etas, target_bits)?;
    let l0 = &mut config.levels[0];
    l0.ood_samples = 0;
    l0.ood_bits = NO_POINTS_BITS;
    config.prover.ood_samples[0] = 0;
    config.verifier.ood_samples[0] = 0;
    if config.min_bits() < target_bits {
        return Err(format!("the MCA ladder (DKT26) reaches only {:.2} bits", config.min_bits()));
    }
    Ok(config)
}

// ---------------------------------------------------------------------------
// Proof
// ---------------------------------------------------------------------------

/// Proof of the BEEP ladder. Every vector is in transcript order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BeepProof {
    /// L0 cap (`2^c₀` nodes at the schedule's cap depth).
    pub initial_cap: Vec<Hash>,
    /// Caps of the committed tables L1..L_r.
    pub recursive_caps: Vec<Vec<Hash>>,
    /// Opened rows + capped paths for L0..L_r (one entry per level).
    pub openings: Vec<RecursiveProof>,
    /// The out-of-domain answers of the fold rounds: per round `2m` values,
    /// `b_{1,0}, b_{1,1}, …, b_{m,0}, b_{m,1}`.
    pub answers: Vec<F128>,
    /// One round polynomial per fold round, as `[h(0), h_2]`.
    pub rounds: Vec<[F128; 2]>,
    /// The final folded message, `2^{c_r}` coefficients.
    pub yr: Vec<F128>,
    pub ood_values: Vec<F128>,
    pub fold_grinding_nonces: Vec<u64>,
    pub claim_batch_grinding_nonces: Vec<u64>,
    pub consistency_batch_grinding_nonces: Vec<u64>,
    pub grinding_nonces: Vec<u64>,
}

/// The parts of a proof, in bytes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SizeBreakdown {
    pub opened_rows: usize,
    pub merkle_paths: usize,
    pub caps: usize,
    /// Out-of-domain answers of the fold rounds (BEEP only).
    pub fold_answers: usize,
    /// Round messages: round polynomials, or the grids of the affine fold.
    pub round_messages: usize,
    /// Out-of-domain values that bind the committed tables.
    pub binding_answers: usize,
    /// The final message, and the overflow coefficients of the affine fold.
    pub final_message: usize,
    pub nonces: usize,
}

impl SizeBreakdown {
    pub fn total(&self) -> usize {
        self.opened_rows
            + self.merkle_paths
            + self.caps
            + self.fold_answers
            + self.round_messages
            + self.binding_answers
            + self.final_message
            + self.nonces
    }
}

const ELEM: usize = size_of::<F128>();

/// The Merkle parts of one level of a proof, in bytes: the rows that its
/// queries open (the leaves of the level's tree), their capped paths (inner
/// nodes of the tree), and the cap of the tree.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LevelBytes {
    pub queries: usize,
    pub leaves: usize,
    pub paths: usize,
    pub cap: usize,
}

fn level_bytes(rows: &[Vec<F128>], path_nodes: usize, cap: &[Hash]) -> LevelBytes {
    LevelBytes {
        queries: rows.len(),
        leaves: rows.iter().map(Vec::len).sum::<usize>() * ELEM,
        paths: path_nodes * 32,
        cap: cap.len() * 32,
    }
}

fn ladder_level_bytes(
    openings: &[RecursiveProof],
    initial_cap: &[Hash],
    recursive_caps: &[Vec<Hash>],
) -> Vec<LevelBytes> {
    assert_eq!(openings.len(), recursive_caps.len() + 1);
    openings
        .iter()
        .enumerate()
        .map(|(li, p)| {
            let cap = if li == 0 { initial_cap } else { &recursive_caps[li - 1] };
            level_bytes(&p.opened_rows, p.merkle_proof.len(), cap)
        })
        .collect()
}

/// [`LevelBytes`] of every level of an affine proof.
pub fn affine_level_bytes(proof: &super::affine::AffineProof) -> Vec<LevelBytes> {
    ladder_level_bytes(&proof.openings, &proof.initial_cap, &proof.recursive_caps)
}

/// [`LevelBytes`] of every level of a split (F256) proof.
pub fn split_level_bytes(proof: &LigeritoProof) -> Vec<LevelBytes> {
    let caps = &proof.recursive_caps;
    assert_eq!(proof.recursive_proofs.len() + 1, caps.len());
    let mut out = vec![level_bytes(
        &proof.initial_proof.opened_rows,
        proof.initial_proof.merkle_proof.len(),
        &proof.initial_cap,
    )];
    for (p, cap) in proof.recursive_proofs.iter().zip(caps) {
        out.push(level_bytes(&p.opened_rows, p.merkle_proof.len(), cap));
    }
    let last = &proof.final_proof;
    out.push(level_bytes(
        &last.opened_rows,
        last.merkle_proof.len(),
        caps.last().expect("a split proof has a recursive level"),
    ));
    out
}

fn openings_bytes<'a>(openings: impl Iterator<Item = &'a RecursiveProof>) -> (usize, usize) {
    openings.fold((0, 0), |(rows, paths), p| {
        (
            rows + p.opened_rows.iter().map(Vec::len).sum::<usize>() * ELEM,
            paths + p.merkle_proof.len() * 32,
        )
    })
}

impl BeepProof {
    pub fn size_breakdown(&self) -> SizeBreakdown {
        let (opened_rows, merkle_paths) = openings_bytes(self.openings.iter());
        SizeBreakdown {
            opened_rows,
            merkle_paths,
            caps: (self.initial_cap.len() + self.recursive_caps.iter().map(Vec::len).sum::<usize>())
                * 32,
            fold_answers: self.answers.len() * ELEM,
            round_messages: self.rounds.len() * 2 * ELEM,
            binding_answers: self.ood_values.len() * ELEM,
            final_message: self.yr.len() * ELEM,
            nonces: (self.fold_grinding_nonces.len()
                + self.claim_batch_grinding_nonces.len()
                + self.consistency_batch_grinding_nonces.len()
                + self.grinding_nonces.len())
                * 8,
        }
    }

    pub fn size_bytes(&self) -> usize {
        self.size_breakdown().total()
    }

    /// [`LevelBytes`] of every level.
    pub fn level_bytes(&self) -> Vec<LevelBytes> {
        ladder_level_bytes(&self.openings, &self.initial_cap, &self.recursive_caps)
    }

    /// Every proof-of-work nonce of the proof.
    pub fn nonces(&self) -> impl Iterator<Item = u64> + '_ {
        self.fold_grinding_nonces
            .iter()
            .chain(&self.claim_batch_grinding_nonces)
            .chain(&self.consistency_batch_grinding_nonces)
            .chain(&self.grinding_nonces)
            .copied()
    }
}

/// [`SizeBreakdown`] of an affine proof, for the comparison.
pub fn affine_size_breakdown(proof: &super::affine::AffineProof) -> SizeBreakdown {
    let (opened_rows, merkle_paths) = openings_bytes(proof.openings.iter());
    SizeBreakdown {
        opened_rows,
        merkle_paths,
        caps: (proof.initial_cap.len() + proof.recursive_caps.iter().map(Vec::len).sum::<usize>())
            * 32,
        fold_answers: 0,
        round_messages: proof.grids.len() * 5 * ELEM,
        binding_answers: proof.ood_values.len() * ELEM,
        final_message: (proof.yr.len() + proof.overflows.iter().map(Vec::len).sum::<usize>())
            * ELEM,
        nonces: (proof.fold_grinding_nonces.len()
            + proof.claim_batch_grinding_nonces.len()
            + proof.consistency_batch_grinding_nonces.len()
            + proof.grinding_nonces.len())
            * 8,
    }
}

/// [`SizeBreakdown`] of a split (F256) proof, for the comparison.
pub fn split_size_breakdown(proof: &LigeritoProof) -> SizeBreakdown {
    let (rows, paths) = openings_bytes(
        std::iter::once(&proof.initial_proof).chain(proof.recursive_proofs.iter()),
    );
    let last = &proof.final_proof;
    SizeBreakdown {
        opened_rows: rows + last.opened_rows.iter().map(Vec::len).sum::<usize>() * ELEM,
        merkle_paths: paths + last.merkle_proof.len() * 32,
        caps: (proof.initial_cap.len() + proof.recursive_caps.iter().map(Vec::len).sum::<usize>())
            * 32,
        fold_answers: 0,
        round_messages: proof.sumcheck_transcript.len() * 2 * ELEM
            + proof.sumcheck_transcript_f256.len() * 4 * ELEM,
        binding_answers: proof.ood_values.len() * ELEM,
        final_message: last.yr.len() * ELEM,
        nonces: (proof.fold_grinding_nonces.len()
            + proof.claim_batch_grinding_nonces.len()
            + proof.consistency_batch_grinding_nonces.len()
            + proof.grinding_nonces.len())
            * 8,
    }
}

// ---------------------------------------------------------------------------
// Prover state
// ---------------------------------------------------------------------------

/// `eq(z)` as low and high tensor factors, with the low factor capped at
/// `2^EQ_LO_BITS` entries.
fn eq_factors(z: &[F128]) -> EqFactors {
    let (lo, hi) = build_eq_split(z, z.len().min(EQ_LO_BITS));
    EqFactors { lo, hi }
}

struct Level {
    f: Vec<F128>,
    w: Vec<F128>,
    claim: F128,
}

impl Level {
    fn new(f: Vec<F128>, w: Vec<F128>, claim: F128) -> Self {
        assert_eq!(f.len(), w.len());
        assert!(f.len().is_power_of_two() && f.len() >= 2);
        Self { f, w, claim }
    }

    /// `<f, eq(z)>` from the eq tensor's factors.
    fn dot_eq(&self, eq: &EqFactors) -> F128 {
        assert_eq!(eq.len(), self.f.len());
        self.f
            .par_chunks(eq.lo.len())
            .zip(eq.hi.par_iter())
            .map(|(block, &h)| {
                let mut acc = F256Unreduced::ZERO;
                for (&a, &l) in block.iter().zip(&eq.lo) {
                    acc ^= a.mul_unreduced(l);
                }
                acc.reduce().mul_unreduced(h)
            })
            .reduce(|| F256Unreduced::ZERO, |a, b| a ^ b)
            .reduce()
    }

    /// `W += Σ_i coefs[i] eq(z_i)` for eq tensors with the same split.
    fn add_eq_weights(&mut self, eqs: &[EqFactors], coefs: &[F128]) {
        let Some(first) = eqs.first() else {
            return;
        };
        assert_eq!(eqs.len(), coefs.len());
        assert!(eqs.len() <= MAX_SAMPLES);
        assert!(eqs.iter().all(|e| e.lo.len() == first.lo.len() && e.len() == self.w.len()));
        self.w
            .par_chunks_mut(first.lo.len())
            .enumerate()
            .for_each(|(h, block)| {
                let mut scaled = [F128::ZERO; MAX_SAMPLES];
                for (s, (eq, &c)) in scaled.iter_mut().zip(eqs.iter().zip(coefs)) {
                    *s = c * eq.hi[h];
                }
                for (q, dst) in block.iter_mut().enumerate() {
                    let mut acc = F256Unreduced::ZERO;
                    for (eq, &s) in eqs.iter().zip(&scaled) {
                        acc ^= s.mul_unreduced(eq.lo[q]);
                    }
                    *dst += acc.reduce();
                }
            });
    }

    /// `W += β B`, `v += β e`.
    fn add_weight(&mut self, basis: &[F128], beta: F128, value: F128) {
        assert_eq!(basis.len(), self.w.len());
        self.w
            .as_mut_slice()
            .into_par_iter()
            .zip(basis.into_par_iter())
            .with_min_len(PAR_MIN)
            .for_each(|(dst, &b)| *dst += beta * b);
        self.claim += beta * value;
    }

    fn dot(&self, basis: &[F128]) -> F128 {
        self.f
            .par_chunks(CHUNK)
            .zip(basis.par_chunks(CHUNK))
            .map(|(a, b)| {
                a.iter()
                    .zip(b)
                    .fold(F256Unreduced::ZERO, |acc, (&x, &y)| acc ^ x.mul_unreduced(y))
            })
            .reduce(|| F256Unreduced::ZERO, |a, b| a ^ b)
            .reduce()
    }

    /// The out-of-domain answers of a fold round: `<f_0, eq(z_i)>` and
    /// `<f_1, eq(z_i)>` for every point, where `f_b[q] = f[2q + b]`, in one
    /// pass over the table. Flattened `b_{1,0}, b_{1,1}, b_{2,0}, …`.
    fn fold_answers(&self, eqs: &[EqFactors]) -> Vec<F128> {
        let Some(first) = eqs.first() else {
            return Vec::new();
        };
        let lo_len = first.lo.len();
        assert!(eqs.iter().all(|e| e.lo.len() == lo_len && 2 * e.len() == self.f.len()));
        let zero = || vec![F256Unreduced::ZERO; 2 * eqs.len()];
        self.f
            .par_chunks(2 * lo_len)
            .enumerate()
            .fold(zero, |mut acc, (h, block)| {
                for (i, eq) in eqs.iter().enumerate() {
                    let (mut a0, mut a1) = (F256Unreduced::ZERO, F256Unreduced::ZERO);
                    for (pair, &l) in block.chunks_exact(2).zip(&eq.lo) {
                        a0 ^= pair[0].mul_unreduced(l);
                        a1 ^= pair[1].mul_unreduced(l);
                    }
                    let hv = eq.hi[h];
                    acc[2 * i] ^= a0.reduce().mul_unreduced(hv);
                    acc[2 * i + 1] ^= a1.reduce().mul_unreduced(hv);
                }
                acc
            })
            .reduce(zero, |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x ^= y;
                }
                a
            })
            .into_iter()
            .map(F256Unreduced::reduce)
            .collect()
    }

    /// `[h(0), h_2]` of `h(X) = Σ_q (f_0 + X (f_0 + f_1)) (w_0 + X (w_0 + w_1))`.
    fn round_message(&self) -> [F128; 2] {
        let (a, c) = self
            .f
            .par_chunks(CHUNK)
            .zip(self.w.par_chunks(CHUNK))
            .map(|(fc, wc)| {
                let (mut a, mut c) = (F256Unreduced::ZERO, F256Unreduced::ZERO);
                for (fp, wp) in fc.chunks_exact(2).zip(wc.chunks_exact(2)) {
                    a ^= fp[0].mul_unreduced(wp[0]);
                    c ^= (fp[0] + fp[1]).mul_unreduced(wp[0] + wp[1]);
                }
                (a, c)
            })
            .reduce(
                || (F256Unreduced::ZERO, F256Unreduced::ZERO),
                |x, y| (x.0 ^ y.0, x.1 ^ y.1),
            );
        [a.reduce(), c.reduce()]
    }

    /// Fold the lowest row bit at `r`: `f' = f_0 + r (f_0 + f_1)`, `W' = W_0 +
    /// r (W_0 + W_1) + Σ_i coefs[i] eq(z_i)` (the answers' claims, added in the
    /// same pass over `W`), and `v' = h(r)`. The eq tensors are over the folded
    /// table and have the same split.
    fn fold(&mut self, r: F128, msg: [F128; 2], eqs: &[EqFactors], coefs: &[F128]) {
        let half = self.f.len() / 2;
        assert_eq!(eqs.len(), coefs.len());
        assert!(eqs.len() <= MAX_SAMPLES);
        // The outputs come from the buffer pool and the inputs go back to
        // it, so a warm prover does not fault in fresh pages at every round.
        let mut dst = take_f128(half);
        let src: &[F128] = &self.f;
        dst.par_chunks_mut(CHUNK)
            .enumerate()
            .for_each(|(i, d)| fold_pairs(src, i * CHUNK, d, r));
        give_f128(std::mem::replace(&mut self.f, dst));

        // One block per high index of the eq tensors (all of the table if
        // there are none), so that a block reads one entry of every `hi`.
        let lo_len = eqs.first().map_or(CHUNK.min(half), |e| e.lo.len());
        assert!(eqs.iter().all(|e| e.lo.len() == lo_len && e.len() == half));
        let mut dst = take_f128(half);
        let src: &[F128] = &self.w;
        dst.par_chunks_mut(lo_len).enumerate().for_each(|(h, block)| {
            fold_pairs(src, h * lo_len, block, r);
            if eqs.is_empty() {
                return;
            }
            let mut scaled = [F128::ZERO; MAX_SAMPLES];
            for (s, (eq, &c)) in scaled.iter_mut().zip(eqs.iter().zip(coefs)) {
                *s = c * eq.hi[h];
            }
            for (q, out) in block.iter_mut().enumerate() {
                let mut acc = F256Unreduced::ZERO;
                for (eq, &s) in eqs.iter().zip(&scaled) {
                    acc ^= s.mul_unreduced(eq.lo[q]);
                }
                *out += acc.reduce();
            }
        });
        give_f128(std::mem::replace(&mut self.w, dst));
        self.claim = round_value(self.claim, msg, r);
    }
}

/// `h(r)` for the round polynomial `[h(0), h_2]` of a claim `v = h(0) + h(1)`:
/// in characteristic 2 its middle coefficient is `v + h_2`.
pub fn round_value(claim: F128, msg: [F128; 2], r: F128) -> F128 {
    msg[0] + r * (claim + msg[1]) + r * r * msg[1]
}

/// The value of `<f', eq(z)>` after the fold at `r`, from the two answers.
fn folded_answer(b0: F128, b1: F128, r: F128) -> F128 {
    b0 + r * (b0 + b1)
}

/// `Σ_q eq(α)_q · Enc(f')(x_q)`, where the folded leaf at `x_q` is the opened
/// row against `eq(rs)`, the weights of the level's scalar folds.
fn batched_consistency(rows: &[Vec<F128>], rs: &[F128], alpha: &[F128]) -> F128 {
    let weights = build_eq_table(alpha);
    let omega = build_eq_table(rs);
    rows.par_iter()
        .zip(weights.par_iter())
        .map(|(row, &wt)| wt * folded_leaf(row, &omega))
        .reduce(|| F128::ZERO, |a, b| a + b)
}

fn folded_leaf(row: &[F128], omega: &[F128]) -> F128 {
    debug_assert_eq!(row.len(), omega.len());
    row.iter()
        .zip(omega)
        .fold(F256Unreduced::ZERO, |acc, (&v, &w)| acc ^ v.mul_unreduced(w))
        .reduce()
}

// ---------------------------------------------------------------------------
// The fold rounds
// ---------------------------------------------------------------------------

// Indices of the phase timers of the prover.
const T_ANSWERS: usize = 0;
const T_FOLDS: usize = 1;
const T_FOLD_POW: usize = 2;
const T_OTHER_POW: usize = 3;
const T_OOD: usize = 4;
const T_COMMITS: usize = 5;
const T_OPENS: usize = 6;
const T_INDUCE: usize = 7;

/// Entries of the table per block of the passes of [`rounds_fast`]: `2^12`
/// (64 KiB of the table and as much of the weight), so that a block stays in
/// the first cache levels while a pass goes over it once per point.
const BLOCK_LOG: usize = 12;

/// A claim `scale · <f, eq(ρ) ⊗ eq(ζ)>` on the table of a level, in factored
/// form: `eq(ρ)` over the rows that are left and `eq(ζ)` over the columns.
///
/// The answers of a fold round add `m` such claims to the weight of the
/// sumcheck. [`rounds_reference`] adds them to the dense weight right away,
/// which costs `m` multiplications per entry of the folded table.
/// [`rounds_fast`] keeps them in this form until the level has one row left:
/// with `s[row] = <f[row, ·], eq(ζ)>`, which it has from the pass that
/// computed the answers and which folds like a column of the table, the
/// contribution of the claim to every later round message of the level is a
/// sum over the rows.
struct Term {
    /// The batching coefficient times the eq factors, at the fold challenges,
    /// of the row variables bound since the claim was made.
    scale: F128,
    /// The coordinates of the point for the row bits that are left;
    /// `rho[0]` belongs to the bit that the next round binds.
    rho: Vec<F128>,
    /// `eq(ζ)` over the columns.
    cols: EqFactors,
    /// `s[row] = <f[row, ·], eq(ζ)>` for the current table.
    s: Vec<F128>,
}

/// What a pass computes for the round that follows it: the round message of
/// the dense weight, `[h(0), h_2]`, and for every point of that round the
/// evaluations `s[i][row] = <f[row, ·], eq(ζ_i)>` of the rows of the table.
struct Lookahead {
    msg: [F128; 2],
    s: Vec<Vec<F128>>,
}

/// The accumulators of a pass: the two sums of the dense round message and,
/// per point and row, the row evaluations (unreduced).
struct RoundAcc {
    a: F256Unreduced,
    c: F256Unreduced,
    s: Vec<F256Unreduced>,
    scratch: Vec<F256Unreduced>,
}

impl RoundAcc {
    fn new(points: usize, rows: usize) -> Self {
        Self {
            a: F256Unreduced::ZERO,
            c: F256Unreduced::ZERO,
            s: vec![F256Unreduced::ZERO; points * rows],
            scratch: vec![F256Unreduced::ZERO; points],
        }
    }

    /// Add block `h` of a table with `rows` rows (its entries `fb`, and `wb`
    /// of the dense weight): `lo_len` whole columns, where `lo_len` is the
    /// length of the low factor of every point of `cols`.
    fn add_block(&mut self, fb: &[F128], wb: &[F128], rows: usize, h: usize, cols: &PointColumns) {
        let (a, c) = kernels::message_block(fb, wb);
        self.a ^= a;
        self.c ^= c;
        let m = cols.eqs.len();
        if m == 0 {
            return;
        }
        let local = &mut self.scratch[..m];
        for row in 0..rows {
            kernels::row_block(fb, row, rows, cols, local);
            for (i, eq) in cols.eqs.iter().enumerate() {
                self.s[i * rows + row] ^= local[i].reduce().mul_unreduced(eq.hi[h]);
            }
        }
    }

    fn merge(mut self, other: Self) -> Self {
        self.a ^= other.a;
        self.c ^= other.c;
        for (x, y) in self.s.iter_mut().zip(other.s) {
            *x ^= y;
        }
        self
    }

    fn finish(self, points: usize, rows: usize) -> Lookahead {
        Lookahead {
            msg: [self.a.reduce(), self.c.reduce()],
            s: (0..points)
                .map(|i| self.s[i * rows..(i + 1) * rows].iter().map(|x| x.reduce()).collect())
                .collect(),
        }
    }
}

/// Columns per block of a pass over a table with `rows` rows and `width`
/// columns: a power of two, about `2^BLOCK_LOG / rows`.
fn block_columns(rows: usize, width: usize) -> usize {
    ((1usize << BLOCK_LOG) / rows).max(1).min(width)
}

/// The columns of the points of a round: `eq` of the column coordinates of
/// every point, as low and high factors, and the low factors again in the
/// layout of the kernel ([`kernels::row_block`]).
struct PointColumns {
    eqs: Vec<EqFactors>,
    /// Columns per block: the length of every low factor.
    lo_len: usize,
    /// `table[m * col + i]`: entry `col` of the low factor of point `i`.
    table: Vec<F128>,
    /// `fold[m * col + i]`: `lo ^ hi` of that entry (the Karatsuba operand).
    fold: Vec<u64>,
}

/// `eq` of the column coordinates of the `m` points `zs` (each of `dim`
/// coordinates, the first `row_vars` of them for the rows), split for the
/// blocks of a pass over a table with `rows` rows.
fn column_eqs(zs: &[F128], m: usize, dim: usize, row_vars: usize, rows: usize) -> PointColumns {
    let width = 1usize << (dim - row_vars);
    let lo_len = block_columns(rows, width);
    let lo_bits = lo_len.trailing_zeros() as usize;
    let eqs: Vec<EqFactors> = (0..m)
        .map(|i| {
            let (lo, hi) = build_eq_split(&zs[i * dim + row_vars..(i + 1) * dim], lo_bits);
            EqFactors { lo, hi }
        })
        .collect();
    let mut table = Vec::with_capacity(m * lo_len);
    let mut fold = Vec::with_capacity(m * lo_len);
    for col in 0..lo_len {
        for eq in &eqs {
            let l = eq.lo[col];
            table.push(l);
            fold.push(l.lo ^ l.hi);
        }
    }
    PointColumns {
        eqs,
        lo_len,
        table,
        fold,
    }
}

/// The inner loops of the passes: sums of carry-less products, unreduced.
/// With PMULL they keep their accumulators in vector registers and use three
/// products per multiplication (Karatsuba); the portable versions define
/// them.
mod kernels {
    use super::{F128, F256Unreduced, PointColumns};

    /// `(Σ_p f[2p] w[2p], Σ_p (f[2p] + f[2p+1]) (w[2p] + w[2p+1]))`.
    pub(super) fn message_block(fb: &[F128], wb: &[F128]) -> (F256Unreduced, F256Unreduced) {
        debug_assert!(fb.len() == wb.len() && fb.len() % 2 == 0);
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        // SAFETY: the cfg gate guarantees PMULL.
        unsafe {
            neon::message_block(fb, wb)
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        message_block_portable(fb, wb)
    }

    #[cfg_attr(all(target_arch = "aarch64", target_feature = "aes"), allow(dead_code))]
    pub(super) fn message_block_portable(fb: &[F128], wb: &[F128]) -> (F256Unreduced, F256Unreduced) {
        let (mut a, mut c) = (F256Unreduced::ZERO, F256Unreduced::ZERO);
        for (fp, wp) in fb.chunks_exact(2).zip(wb.chunks_exact(2)) {
            a ^= fp[0].mul_unreduced(wp[0]);
            c ^= (fp[0] + fp[1]).mul_unreduced(wp[0] + wp[1]);
        }
        (a, c)
    }

    /// For every point `i`: `out[i] = Σ_col fb[row + rows · col] · lo_i[col]`,
    /// row `row` of a block of `cols.lo_len` columns against the low factors.
    pub(super) fn row_block(fb: &[F128], row: usize, rows: usize, cols: &PointColumns, out: &mut [F256Unreduced]) {
        debug_assert!(row < rows && fb.len() == rows * cols.lo_len && out.len() == cols.eqs.len());
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        // SAFETY: the cfg gate guarantees PMULL; the lengths are checked
        // above and in `neon::row_block`.
        unsafe {
            neon::row_block(fb, row, rows, cols, out);
        }
        #[cfg(not(all(target_arch = "aarch64", target_feature = "aes")))]
        row_block_portable(fb, row, rows, cols, out);
    }

    #[cfg_attr(all(target_arch = "aarch64", target_feature = "aes"), allow(dead_code))]
    pub(super) fn row_block_portable(fb: &[F128], row: usize, rows: usize, cols: &PointColumns, out: &mut [F256Unreduced]) {
        let m = cols.eqs.len();
        out.fill(F256Unreduced::ZERO);
        for col in 0..cols.lo_len {
            let v = fb[row + rows * col];
            for (i, acc) in out.iter_mut().enumerate() {
                *acc ^= v.mul_unreduced(cols.table[m * col + i]);
            }
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    mod neon {
        use core::arch::aarch64::{
            uint64x2_t, vdupq_n_u64, veorq_u64, vextq_u64, vgetq_lane_u64, vld1q_u64, vmull_high_p64,
            vmull_p64, vreinterpretq_p64_u64, vreinterpretq_u64_p128,
        };

        use super::{F128, F256Unreduced, PointColumns};

        /// Most points per call of the row kernel with accumulators in
        /// registers (three per point).
        const GROUP: usize = 4;

        #[inline(always)]
        unsafe fn load(x: &F128) -> uint64x2_t {
            // SAFETY: `F128` is `repr(C)` with two `u64` fields, `lo` first.
            unsafe { vld1q_u64(core::ptr::from_ref(x).cast::<u64>()) }
        }

        /// `lo · lo'`, `hi · hi'` and `(lo ^ hi)(lo' ^ hi')` of two elements,
        /// from their vectors and the two xors (in the low lanes).
        #[inline(always)]
        unsafe fn products(
            a: uint64x2_t,
            ak: uint64x2_t,
            b: uint64x2_t,
            bk: u64,
        ) -> (uint64x2_t, uint64x2_t, uint64x2_t) {
            // SAFETY: PMULL is available (the callers carry the feature).
            unsafe {
                let ll = vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b)));
                let hh = vreinterpretq_u64_p128(vmull_high_p64(
                    vreinterpretq_p64_u64(a),
                    vreinterpretq_p64_u64(b),
                ));
                let kk = vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(ak), bk));
                (ll, hh, kk)
            }
        }

        /// The 256-bit product from the three Karatsuba sums.
        #[inline(always)]
        unsafe fn combine(ll: uint64x2_t, hh: uint64x2_t, kk: uint64x2_t) -> F256Unreduced {
            // SAFETY: plain vector arithmetic.
            unsafe {
                let mid = veorq_u64(kk, veorq_u64(ll, hh));
                F256Unreduced {
                    r0: vgetq_lane_u64::<0>(ll),
                    r1: vgetq_lane_u64::<1>(ll) ^ vgetq_lane_u64::<0>(mid),
                    r2: vgetq_lane_u64::<0>(hh) ^ vgetq_lane_u64::<1>(mid),
                    r3: vgetq_lane_u64::<1>(hh),
                }
            }
        }

        #[target_feature(enable = "aes")]
        pub(super) unsafe fn message_block(fb: &[F128], wb: &[F128]) -> (F256Unreduced, F256Unreduced) {
            // SAFETY: PMULL is enabled; the indices are in range.
            unsafe {
                let zero = vdupq_n_u64(0);
                let (mut a0, mut a1, mut a2) = (zero, zero, zero);
                let (mut c0, mut c1, mut c2) = (zero, zero, zero);
                let pairs = fb.len() / 2;
                for p in 0..pairs {
                    let f0 = load(fb.get_unchecked(2 * p));
                    let f1 = load(fb.get_unchecked(2 * p + 1));
                    let w0 = load(wb.get_unchecked(2 * p));
                    let w1 = load(wb.get_unchecked(2 * p + 1));
                    let fs = veorq_u64(f0, f1);
                    let ws = veorq_u64(w0, w1);
                    // The xor of the two lanes, in the low lane.
                    let f0k = veorq_u64(f0, vextq_u64::<1>(f0, f0));
                    let w0k = veorq_u64(w0, vextq_u64::<1>(w0, w0));
                    let fsk = veorq_u64(fs, vextq_u64::<1>(fs, fs));
                    let wsk = veorq_u64(ws, vextq_u64::<1>(ws, ws));
                    let (ll, hh, kk) = products(f0, f0k, w0, vgetq_lane_u64::<0>(w0k));
                    a0 = veorq_u64(a0, ll);
                    a1 = veorq_u64(a1, hh);
                    a2 = veorq_u64(a2, kk);
                    let (ll, hh, kk) = products(fs, fsk, ws, vgetq_lane_u64::<0>(wsk));
                    c0 = veorq_u64(c0, ll);
                    c1 = veorq_u64(c1, hh);
                    c2 = veorq_u64(c2, kk);
                }
                (combine(a0, a1, a2), combine(c0, c1, c2))
            }
        }

        #[target_feature(enable = "aes")]
        pub(super) unsafe fn row_block(
            fb: &[F128],
            row: usize,
            rows: usize,
            cols: &PointColumns,
            out: &mut [F256Unreduced],
        ) {
            let m = cols.eqs.len();
            let lo_len = cols.lo_len;
            assert!(fb.len() == rows * lo_len && row < rows);
            assert!(cols.table.len() == m * lo_len && cols.fold.len() == m * lo_len && out.len() == m);
            // SAFETY: PMULL is enabled; every index below is in range by the
            // assertions above.
            unsafe {
                let zero = vdupq_n_u64(0);
                let mut first = 0;
                while first < m {
                    let g = (m - first).min(GROUP);
                    let mut acc = [[zero; 3]; GROUP];
                    for col in 0..lo_len {
                        let v = load(fb.get_unchecked(row + rows * col));
                        let vk = veorq_u64(v, vextq_u64::<1>(v, v));
                        let base = m * col + first;
                        for (i, a) in acc.iter_mut().enumerate().take(g) {
                            let t = load(cols.table.get_unchecked(base + i));
                            let tk = *cols.fold.get_unchecked(base + i);
                            let (ll, hh, kk) = products(v, vk, t, tk);
                            a[0] = veorq_u64(a[0], ll);
                            a[1] = veorq_u64(a[1], hh);
                            a[2] = veorq_u64(a[2], kk);
                        }
                    }
                    for (i, a) in acc.iter().enumerate().take(g) {
                        *out.get_unchecked_mut(first + i) = combine(a[0], a[1], a[2]);
                    }
                    first += g;
                }
            }
        }
    }
}

/// The dense round message of `(f, w)`, a table with `rows` rows, and the
/// row evaluations of `f` at the points `cols`, in one pass.
fn first_pass(f: &[F128], w: &[F128], rows: usize, cols: &PointColumns) -> Lookahead {
    let width = f.len() / rows;
    let lo_len = cols.lo_len;
    assert!(lo_len == block_columns(rows, width) && cols.eqs.iter().all(|e| e.len() == width));
    let block = rows * lo_len;
    let m = cols.eqs.len();
    f.par_chunks(block)
        .zip(w.par_chunks(block))
        .enumerate()
        .fold(
            || RoundAcc::new(m, rows),
            |mut acc, (h, (fb, wb))| {
                acc.add_block(fb, wb, rows, h, cols);
                acc
            },
        )
        .reduce(|| RoundAcc::new(m, rows), RoundAcc::merge)
        .finish(m, rows)
}

/// Fold the lowest row bit of `(f, w)`, a table with `rows` rows, at `r`,
/// and, if a round follows (`cols`: the columns of its points), compute what
/// that round needs from the folded table, block by block in the same pass.
fn fold_pass(
    f: &[F128],
    w: &[F128],
    rows: usize,
    r: F128,
    cols: Option<&PointColumns>,
) -> (Vec<F128>, Vec<F128>, Option<Lookahead>) {
    let half = f.len() / 2;
    let half_rows = rows / 2;
    let width = half / half_rows;
    let lo_len = block_columns(half_rows, width);
    let block = half_rows * lo_len;
    let m = cols.map_or(0, |c| c.eqs.len());
    if let Some(cols) = cols {
        assert!(cols.lo_len == lo_len && cols.eqs.iter().all(|e| e.len() == width));
    }
    // The outputs come from the buffer pool and the inputs go back to it.
    let mut dst_f = take_f128(half);
    let mut dst_w = take_f128(half);
    let acc = dst_f
        .par_chunks_mut(block)
        .zip(dst_w.par_chunks_mut(block))
        .enumerate()
        .fold(
            || RoundAcc::new(m, half_rows),
            |mut acc, (h, (fb, wb))| {
                // A cache hint: the two blocks are written in full below
                // (`affine_fast::will_overwrite`; no effect on the proof).
                will_overwrite(fb);
                will_overwrite(wb);
                fold_pairs(f, h * block, fb, r);
                fold_pairs(w, h * block, wb, r);
                if let Some(cols) = cols {
                    acc.add_block(fb, wb, half_rows, h, cols);
                }
                acc
            },
        )
        .reduce(|| RoundAcc::new(m, half_rows), RoundAcc::merge);
    let ahead = cols.map(|_| acc.finish(m, half_rows));
    (dst_f, dst_w, ahead)
}

/// `(Σ_i e[i] s[2i], Σ_i e[i] s[2i + 1])`: the two halves of a vector over
/// the rows, against `eq` of the rows of a half.
fn halves_at(s: &[F128], e: &[F128]) -> (F128, F128) {
    debug_assert_eq!(s.len(), 2 * e.len());
    let (mut a, mut b) = (F256Unreduced::ZERO, F256Unreduced::ZERO);
    for (pair, &x) in s.chunks_exact(2).zip(e) {
        a ^= pair[0].mul_unreduced(x);
        b ^= pair[1].mul_unreduced(x);
    }
    (a.reduce(), b.reduce())
}

/// The fold of a vector over the rows at `r`, as the table folds.
fn fold_rows(s: &[F128], r: F128) -> Vec<F128> {
    s.chunks_exact(2).map(|p| p[0] + r * (p[0] + p[1])).collect()
}

/// `w += Σ_t scale_t · eq(ζ_t)` for the claims of a level that has one row
/// left, a group of claims with the same split of the columns at a time.
fn materialize_terms(w: &mut [F128], terms: &[Term]) {
    let mut done = vec![false; terms.len()];
    for first in 0..terms.len() {
        if done[first] {
            continue;
        }
        let lo_len = terms[first].cols.lo.len();
        let group: Vec<usize> = (first..terms.len())
            .filter(|&i| !done[i] && terms[i].cols.lo.len() == lo_len)
            .take(MAX_SAMPLES)
            .collect();
        for &i in &group {
            done[i] = true;
            assert_eq!(terms[i].cols.len(), w.len());
            debug_assert!(terms[i].rho.is_empty());
        }
        w.par_chunks_mut(lo_len).enumerate().for_each(|(h, block)| {
            let mut scaled = [F128::ZERO; MAX_SAMPLES];
            for (sc, &i) in scaled.iter_mut().zip(&group) {
                *sc = terms[i].scale * terms[i].cols.hi[h];
            }
            for (q, dst) in block.iter_mut().enumerate() {
                let mut acc = F256Unreduced::ZERO;
                for (&sc, &i) in scaled.iter().zip(&group) {
                    acc ^= sc.mul_unreduced(terms[i].cols.lo[q]);
                }
                *dst += acc.reduce();
            }
        });
    }
}

/// The fold rounds of one level, with one pass over the table per round.
///
/// The transcript and the proof are those of [`rounds_reference`]. The work
/// differs in two ways. First, the pass that folds the table and the weight
/// at the challenge of a round also computes, block by block on the folded
/// table, what the next round needs: its round message and, for each of its
/// points, the evaluations of the rows at the column coordinates of the
/// point (the points of the next round come from the same transcript state
/// as the fold challenge, so they are known when the pass starts). The two
/// answers of a point are then two sums over the rows. Second, the claims of
/// the answers are not added to the dense weight during the level: they stay
/// in factored form ([`Term`]) until one row is left.
fn rounds_fast<Ch: Challenger>(
    level: &mut Level,
    (k, c): (usize, usize),
    m: usize,
    fold: &[Grind],
    proof: &mut BeepProof,
    challenger: &mut Ch,
    t: &mut [Duration; 8],
) -> Vec<F128> {
    let mut level_rs = Vec::with_capacity(k);
    let mut terms: Vec<Term> = Vec::with_capacity(k * m);
    // The points of the coming round, the eq of their columns, and what the
    // pass of the previous round computed for it.
    let mut ahead: Option<(Vec<F128>, PointColumns, Lookahead)> = None;
    for j in 0..k {
        let rows = 1usize << (k - j);
        let row_vars = k - j - 1;
        let dim = row_vars + c;
        let (zs, cols, la) = match ahead.take() {
            Some(x) => x,
            None => {
                // First round of the level: one pass that reads the table.
                let ti = Instant::now();
                let zs = challenger.sample_f128_vec(m * dim);
                let cols = column_eqs(&zs, m, dim, row_vars, rows);
                let la = first_pass(&level.f, &level.w, rows, &cols);
                t[T_FOLDS] += ti.elapsed();
                (zs, cols, la)
            }
        };

        let ti = Instant::now();
        let mut answers = Vec::with_capacity(2 * m);
        for i in 0..m {
            let row_eq = build_eq_table(&zs[i * dim..i * dim + row_vars]);
            let (b0, b1) = halves_at(&la.s[i], &row_eq);
            answers.push(b0);
            answers.push(b1);
        }
        challenger.observe_f128_slice(&answers);
        t[T_ANSWERS] += ti.elapsed();

        let ti = Instant::now();
        let mut msg = la.msg;
        for term in &terms {
            let row_eq = build_eq_table(&term.rho[1..]);
            let (e0, e1) = halves_at(&term.s, &row_eq);
            msg[0] += term.scale * (F128::ONE + term.rho[0]) * e0;
            msg[1] += term.scale * (e0 + e1);
        }
        challenger.observe_f128_slice(&msg);
        proof.rounds.push(msg);
        t[T_FOLDS] += ti.elapsed();

        let ti = Instant::now();
        let (nonce, ch) = grind_vec(challenger, fold[j], 1 + m);
        proof.fold_grinding_nonces.push(nonce);
        t[T_FOLD_POW] += ti.elapsed();
        let (rr, zetas) = (ch[0], &ch[1..]);

        let ti = Instant::now();
        // The points of the next round of the level: the same squeeze of the
        // transcript as in `rounds_reference`, which draws them at the top of
        // its next iteration with nothing observed in between.
        let next = (j + 1 < k).then(|| {
            let zs = challenger.sample_f128_vec(m * (dim - 1));
            let cols = column_eqs(&zs, m, dim - 1, row_vars - 1, rows / 2);
            (zs, cols)
        });
        level.claim = round_value(level.claim, msg, rr);
        for (pair, &zeta) in answers.chunks_exact(2).zip(zetas) {
            level.claim += zeta * folded_answer(pair[0], pair[1], rr);
        }
        for term in &mut terms {
            term.scale *= F128::ONE + term.rho[0] + rr;
            term.rho.remove(0);
            term.s = fold_rows(&term.s, rr);
        }
        for (i, (cols, &zeta)) in cols.eqs.into_iter().zip(zetas).enumerate() {
            terms.push(Term {
                scale: zeta,
                rho: zs[i * dim..i * dim + row_vars].to_vec(),
                cols,
                s: fold_rows(&la.s[i], rr),
            });
        }
        let (f, w, la_next) = fold_pass(
            &level.f,
            &level.w,
            rows,
            rr,
            next.as_ref().map(|(_, cols)| cols),
        );
        give_f128(std::mem::replace(&mut level.f, f));
        give_f128(std::mem::replace(&mut level.w, w));
        ahead = next.map(|(zs, cols)| (zs, cols, la_next.expect("a pass with points looks ahead")));
        t[T_FOLDS] += ti.elapsed();
        proof.answers.extend(answers);
        level_rs.push(rr);
    }
    // One row is left: the claims of the level go into the dense weight.
    let ti = Instant::now();
    materialize_terms(&mut level.w, &terms);
    t[T_FOLDS] += ti.elapsed();
    debug_assert_eq!(level.claim, level.dot(&level.w), "the claim must be the inner product");
    level_rs
}

/// The fold rounds of one level, as the protocol states them: per round one
/// pass for the answers, one for the round message, and one that folds the
/// table and the weight and adds the answers' claims to the weight. Kept as
/// the reference of [`rounds_fast`], which must write the same proof.
fn rounds_reference<Ch: Challenger>(
    level: &mut Level,
    (k, c): (usize, usize),
    m: usize,
    fold: &[Grind],
    proof: &mut BeepProof,
    challenger: &mut Ch,
    t: &mut [Duration; 8],
) -> Vec<F128> {
    let mut level_rs = Vec::with_capacity(k);
    for j in 0..k {
        // The two halves of the table have k − j − 1 + c variables.
        let dim = k - j - 1 + c;
        let ti = Instant::now();
        let zs = challenger.sample_f128_vec(m * dim);
        let eqs: Vec<EqFactors> = (0..m).map(|i| eq_factors(&zs[i * dim..(i + 1) * dim])).collect();
        let answers = level.fold_answers(&eqs);
        challenger.observe_f128_slice(&answers);
        t[T_ANSWERS] += ti.elapsed();

        let ti = Instant::now();
        let msg = level.round_message();
        debug_assert_eq!(
            level.claim,
            level.dot(&level.w),
            "the claim must be the inner product"
        );
        challenger.observe_f128_slice(&msg);
        proof.rounds.push(msg);
        t[T_FOLDS] += ti.elapsed();

        let ti = Instant::now();
        let (nonce, ch) = grind_vec(challenger, fold[j], 1 + m);
        proof.fold_grinding_nonces.push(nonce);
        t[T_FOLD_POW] += ti.elapsed();
        let (rr, zetas) = (ch[0], &ch[1..]);

        let ti = Instant::now();
        level.fold(rr, msg, &eqs, zetas);
        for (pair, &zeta) in answers.chunks_exact(2).zip(zetas) {
            level.claim += zeta * folded_answer(pair[0], pair[1], rr);
        }
        t[T_FOLDS] += ti.elapsed();
        proof.answers.extend(answers);
        level_rs.push(rr);
    }
    level_rs
}

// ---------------------------------------------------------------------------
// Prover
// ---------------------------------------------------------------------------

/// Where the prover's time goes, for the cost table of the comparison.
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
pub struct ProveTimings {
    /// Out-of-domain answers of the fold rounds: sampling the points, their
    /// eq tables and the pass over the table.
    pub fold_answers_ms: f64,
    /// Round messages and folds. The fold of the weight also adds the
    /// answers' claims to it, in the same pass.
    pub folds_ms: f64,
    /// Fold squeezes: proof of work and sampling.
    pub fold_grinding_ms: f64,
    /// Every other proof of work (queries, consistency and claim batching).
    pub other_grinding_ms: f64,
    pub ood_ms: f64,
    pub commits_ms: f64,
    pub opens_ms: f64,
    pub induce_ms: f64,
    pub total_ms: f64,
}

/// Prove `Σ_x witness[x] · basis[x] = target` against an L0 commitment of
/// `witness` built by `ligero_commit(witness, log_n - initial_k, initial_k,
/// log_inv_rates[0], …)`. `config` must come from [`beep_ladder`].
pub fn prove_beep<Ch: Challenger>(
    config: &BeepConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
) -> BeepProof {
    prove_beep_timed(config, witness, basis, target, l0_codeword, l0_tree, challenger).0
}

/// [`prove_beep`], also returning where the time went.
pub fn prove_beep_timed<Ch: Challenger>(
    beep: &BeepConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
) -> (BeepProof, ProveTimings) {
    prove_beep_impl(beep, witness, basis, target, l0_codeword, l0_tree, challenger, true)
}

/// The prover with the fold rounds of [`rounds_reference`] (three passes per
/// round, the claims of the answers added to the dense weight). It writes the
/// same proof as [`prove_beep_timed`], more slowly: the tests compare the
/// two, and the bench can time it (`beepref-<eta>`).
pub fn prove_beep_reference_timed<Ch: Challenger>(
    beep: &BeepConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
) -> (BeepProof, ProveTimings) {
    prove_beep_impl(beep, witness, basis, target, l0_codeword, l0_tree, challenger, false)
}

#[allow(clippy::too_many_arguments)]
fn prove_beep_impl<Ch: Challenger>(
    beep: &BeepConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
    fast: bool,
) -> (BeepProof, ProveTimings) {
    let config = &beep.prover;
    let log_n = witness.len().trailing_zeros() as usize;
    let r = config.recursive_steps;
    let shapes = level_shapes(log_n, config.initial_k, &config.recursive_ks);
    assert_eq!(
        config.recursive_log_msg_cols,
        shapes[1..].iter().map(|s| s.1).collect::<Vec<_>>()
    );
    assert_eq!(beep.samples.len(), r + 1);
    assert!(beep.samples.iter().all(|&m| m <= MAX_SAMPLES));
    config
        .validate_stratified()
        .expect("stratified schedules invalid (BEEP prover)");
    let strat = |level: usize| &config.stratified[level];
    let claim_grind = |level: usize| beep.claim[level];
    let consistency_grind = |level: usize| beep.consistency[level];

    let trace = var("LIG_PROVE_TRACE").is_ok();
    let t_total = Instant::now();
    // Phase timers, indexed by the constants `T_*`.
    let mut t = [Duration::ZERO; 8];
    const OTHER_POW: usize = T_OTHER_POW;
    const OOD: usize = T_OOD;
    const COMMITS: usize = T_COMMITS;
    const OPENS: usize = T_OPENS;
    const INDUCE: usize = T_INDUCE;

    challenger.observe_label(LABEL);
    challenger.observe_f128(target);
    let block_len_0 = 1usize << (shapes[0].1 + config.log_inv_rates[0]);
    let lanes_0 = 1usize << shapes[0].0;
    assert_eq!(l0_codeword.len(), block_len_0 * lanes_0);
    let initial_cap = cap_layer(l0_tree, block_len_0, strat(0).cap_depth()).to_vec();
    challenger.observe_bytes(initial_cap.as_flattened());

    let mut proof = BeepProof {
        initial_cap,
        recursive_caps: Vec::new(),
        openings: Vec::new(),
        answers: Vec::new(),
        rounds: Vec::new(),
        yr: Vec::new(),
        ood_values: Vec::new(),
        fold_grinding_nonces: Vec::new(),
        claim_batch_grinding_nonces: Vec::new(),
        consistency_batch_grinding_nonces: Vec::new(),
        grinding_nonces: Vec::new(),
    };

    let mut level = Level::new(witness, basis, target);
    // Out-of-domain binding of a committed table of `dim` variables: all the
    // points from one squeeze, then their values, then the coefficients that
    // batch them from one squeeze behind one proof of work.
    let bind = |level: &mut Level,
                    li: usize,
                    dim: usize,
                    proof: &mut BeepProof,
                    challenger: &mut Ch,
                    t: &mut [Duration; 8]| {
        let points = config.ood_samples[li];
        if points == 0 {
            return;
        }
        let ti = Instant::now();
        let zs = challenger.sample_f128_vec(points * dim);
        let eqs: Vec<EqFactors> = (0..points)
            .map(|i| eq_factors(&zs[i * dim..(i + 1) * dim]))
            .collect();
        let ys: Vec<F128> = eqs.iter().map(|eq| level.dot_eq(eq)).collect();
        challenger.observe_f128_slice(&ys);
        proof.ood_values.extend_from_slice(&ys);
        t[OOD] += ti.elapsed();
        let ti = Instant::now();
        let (nonce, betas) = grind_vec(challenger, claim_grind(li), points);
        proof.claim_batch_grinding_nonces.push(nonce);
        t[OTHER_POW] += ti.elapsed();
        let ti = Instant::now();
        level.add_eq_weights(&eqs, &betas);
        for (&beta, &y) in betas.iter().zip(&ys) {
            level.claim += beta * y;
        }
        t[OOD] += ti.elapsed();
    };
    bind(&mut level, 0, log_n, &mut proof, challenger, &mut t);

    let mut committed = Vec::with_capacity(r);
    for li in 0..=r {
        let (k, c) = shapes[li];
        assert_eq!(level.f.len(), 1usize << (k + c));
        let m = beep.samples[li];
        // One grind per fold round (the same one in every round of a BEEP level).
        let fold: Vec<Grind> = (0..k).map(|j| beep.fold_grind(li, j)).collect();
        let level_rs = if fast {
            rounds_fast(&mut level, (k, c), m, &fold, &mut proof, challenger, &mut t)
        } else {
            rounds_reference(&mut level, (k, c), m, &fold, &mut proof, challenger, &mut t)
        };
        let prev: Commitment<'_> = if li == 0 {
            Commitment {
                mat: l0_codeword,
                tree: l0_tree,
                block_len: block_len_0,
                lanes: lanes_0,
            }
        } else {
            view(&committed[li - 1])
        };

        if li == r {
            proof.yr = std::mem::take(&mut level.f);
            challenger.observe_f128_slice(&proof.yr);
            let ti = Instant::now();
            let (nonce, queries) = grind_and_sample_queries(
                challenger,
                config.grinding_bits[li] as u32,
                prev.block_len,
                config.queries[li],
                strat(li),
            );
            proof.grinding_nonces.push(nonce);
            t[OTHER_POW] += ti.elapsed();
            let ti = Instant::now();
            proof.openings.push(RecursiveProof {
                opened_rows: queries.iter().map(|&q| prev.row(q).to_vec()).collect(),
                merkle_proof: merkle_paths_for(prev.tree, prev.block_len, &queries, strat(li)),
            });
            t[OPENS] += ti.elapsed();
            break;
        }

        // Code switch: commit the folded message at the next level's shape.
        let (k_next, c_next) = shapes[li + 1];
        let rate = config.log_inv_rates[li + 1];
        let ti = Instant::now();
        let ntt = AdditiveNttF128::standard(c_next + rate);
        let next = ligero_commit(&level.f, c_next, k_next, rate, &ntt, config.merkle_hash);
        t[COMMITS] += ti.elapsed();
        let cap = next.cap(strat(li + 1).cap_depth()).to_vec();
        challenger.observe_bytes(cap.as_flattened());
        proof.recursive_caps.push(cap);

        bind(&mut level, li + 1, c, &mut proof, challenger, &mut t);

        let ti = Instant::now();
        let (nonce, queries) = grind_and_sample_queries(
            challenger,
            config.grinding_bits[li] as u32,
            prev.block_len,
            config.queries[li],
            strat(li),
        );
        proof.grinding_nonces.push(nonce);
        let (nonce, alpha) =
            grind_vec(challenger, consistency_grind(li), ceil_log2(config.queries[li]));
        proof.consistency_batch_grinding_nonces.push(nonce);
        t[OTHER_POW] += ti.elapsed();
        let ti = Instant::now();
        let opened_rows: Vec<Vec<F128>> = queries.iter().map(|&q| prev.row(q).to_vec()).collect();
        proof.openings.push(RecursiveProof {
            merkle_proof: merkle_paths_for(prev.tree, prev.block_len, &queries, strat(li)),
            opened_rows,
        });
        t[OPENS] += ti.elapsed();
        let ti = Instant::now();
        let rows = &proof.openings.last().expect("just pushed").opened_rows;
        let enforced = batched_consistency(rows, &level_rs, &alpha);
        let basis = induce_sumcheck_poly_auto(
            c,
            config.log_inv_rates[li],
            &eval_sk_at_vks(c),
            &vec![Vec::new(); queries.len()],
            &[],
            &queries,
            &alpha,
        )
        .0;
        debug_assert_eq!(level.dot(&basis), enforced, "consistency claim must hold");
        t[INDUCE] += ti.elapsed();
        let ti = Instant::now();
        let (nonce, beta) = grind_vec(challenger, claim_grind(li + 1), 1);
        let beta = beta[0];
        proof.claim_batch_grinding_nonces.push(nonce);
        t[OTHER_POW] += ti.elapsed();
        let ti = Instant::now();
        level.add_weight(&basis, beta, enforced);
        t[INDUCE] += ti.elapsed();
        committed.push(next);
    }

    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    let timings = ProveTimings {
        fold_answers_ms: ms(t[T_ANSWERS]),
        folds_ms: ms(t[T_FOLDS]),
        fold_grinding_ms: ms(t[T_FOLD_POW]),
        other_grinding_ms: ms(t[OTHER_POW]),
        ood_ms: ms(t[OOD]),
        commits_ms: ms(t[COMMITS]),
        opens_ms: ms(t[OPENS]),
        induce_ms: ms(t[INDUCE]),
        total_ms: ms(t_total.elapsed()),
    };
    if trace {
        eprintln!("[lig-prove-beep] total = {:.2} ms", timings.total_ms);
        eprintln!("  fold answers (eq build + pass):    {:.2} ms", timings.fold_answers_ms);
        eprintln!("  folds (message + fold + weights):  {:.2} ms", timings.folds_ms);
        eprintln!("  fold grinding:                     {:.2} ms", timings.fold_grinding_ms);
        eprintln!("  other grinding:                    {:.2} ms", timings.other_grinding_ms);
        eprintln!("  OODs (eq build + eval + fold-in):  {:.2} ms", timings.ood_ms);
        eprintln!("  recursive commits (NTT + merkle):  {:.2} ms", timings.commits_ms);
        eprintln!("  opens (rows + merkle paths):       {:.2} ms", timings.opens_ms);
        eprintln!("  induce (basis + enforced + glue):  {:.2} ms", timings.induce_ms);
    }
    (proof, timings)
}

// ---------------------------------------------------------------------------
// Verifier
// ---------------------------------------------------------------------------

/// Verify a [`BeepProof`]. `eval_b_residual(rs, residual_log)` returns the
/// caller's basis bound at the fold challenges `rs` (in binding order), as a
/// table over the `residual_log` remaining variables.
pub fn verify_beep<Ch, F>(
    beep: &BeepConfig,
    proof: &BeepProof,
    log_n: usize,
    target: F128,
    expected_initial_cap: &[Hash],
    eval_b_residual: F,
    challenger: &mut Ch,
) -> bool
where
    Ch: Challenger,
    F: Fn(&[F128], usize) -> Vec<F128>,
{
    verify_beep_core(
        beep,
        proof,
        log_n,
        target,
        expected_initial_cap,
        eval_b_residual,
        challenger,
    )
    .is_some()
}

fn verify_beep_core<Ch, F>(
    beep: &BeepConfig,
    proof: &BeepProof,
    log_n: usize,
    target: F128,
    expected_initial_cap: &[Hash],
    eval_b_residual: F,
    challenger: &mut Ch,
) -> Option<()>
where
    Ch: Challenger,
    F: Fn(&[F128], usize) -> Vec<F128>,
{
    let config = &beep.verifier;
    let r = config.recursive_steps;
    if r < 1
        || config.recursive_ks.len() != r
        || beep.samples.len() != r + 1
        || beep.samples.iter().any(|&m| m > MAX_SAMPLES)
        || proof.initial_cap != expected_initial_cap
        || config.validate_stratified().is_err()
    {
        return None;
    }
    let shapes = level_shapes(log_n, config.initial_k, &config.recursive_ks);
    if config.recursive_log_msg_cols != shapes[1..].iter().map(|s| s.1).collect::<Vec<_>>() {
        return None;
    }
    let strat = |level: usize| &config.stratified[level];
    if beep.fold.len() != r + 1 || beep.claim.len() != r + 1 || beep.consistency.len() != r + 1 {
        return None;
    }
    let claim_grind = |level: usize| beep.claim[level];
    let consistency_grind = |level: usize| beep.consistency[level];

    challenger.observe_label(LABEL);
    challenger.observe_f128(target);
    challenger.observe_bytes(proof.initial_cap.as_flattened());

    let mut claim = target;
    // Every weight added after the start, with the dimension of the table
    // it was added on: it is bound by the fold challenges that follow.
    let mut contexts: Vec<(usize, Context)> = Vec::new();
    let mut all_rs: Vec<F128> = Vec::with_capacity(log_n);
    let (mut ood_i, mut claim_i, mut round_i, mut answer_i) = (0usize, 0usize, 0usize, 0usize);

    macro_rules! next {
        ($v:expr, $i:ident) => {{
            let x = $v.get($i)?;
            $i += 1;
            x
        }};
    }
    // Out-of-domain binding of a committed table of `dim` variables, as in
    // the prover: the points, their values, one proof of work, the coefficients.
    macro_rules! bind {
        ($li:expr, $dim:expr) => {
            let points = config.ood_samples[$li];
            if points > 0 {
                let zs = challenger.sample_f128_vec(points * $dim);
                let ys = proof.ood_values.get(ood_i..ood_i + points)?;
                ood_i += points;
                challenger.observe_f128_slice(ys);
                let nonce = *next!(proof.claim_batch_grinding_nonces, claim_i);
                let betas = verify_vec(challenger, claim_grind($li), nonce, points)?;
                for (i, (&y, &beta)) in ys.iter().zip(&betas).enumerate() {
                    claim += beta * y;
                    contexts.push((
                        $dim,
                        Context::Ood {
                            point: zs[i * $dim..(i + 1) * $dim].to_vec(),
                            beta,
                        },
                    ));
                }
            }
        };
    }
    bind!(0, log_n);

    let mut prev_cap: &[Hash] = &proof.initial_cap;
    for li in 0..=r {
        let (k, c) = shapes[li];
        let m = beep.samples[li];
        let mut level_rs = Vec::with_capacity(k);
        for j in 0..k {
            let dim = k - j - 1 + c;
            let zs = challenger.sample_f128_vec(m * dim);
            let answers = proof.answers.get(answer_i..answer_i + 2 * m)?;
            answer_i += 2 * m;
            challenger.observe_f128_slice(answers);
            let msg = *next!(proof.rounds, round_i);
            challenger.observe_f128_slice(&msg);
            let &nonce = proof.fold_grinding_nonces.get(round_i - 1)?;
            let ch = verify_vec(challenger, beep.fold_grind(li, j), nonce, 1 + m)?;
            let rr = ch[0];
            claim = round_value(claim, msg, rr);
            all_rs.push(rr);
            level_rs.push(rr);
            for (i, (pair, &zeta)) in answers.chunks_exact(2).zip(&ch[1..]).enumerate() {
                claim += zeta * folded_answer(pair[0], pair[1], rr);
                contexts.push((
                    dim,
                    Context::Ood {
                        point: zs[i * dim..(i + 1) * dim].to_vec(),
                        beta: zeta,
                    },
                ));
            }
        }
        let block_len = 1usize << (c + config.log_inv_rates[li]);
        let opening = proof.openings.get(li)?;
        let &query_nonce = proof.grinding_nonces.get(li)?;
        let omega = build_eq_table(&level_rs);

        if li == r {
            if proof.yr.len() != 1usize << c {
                return None;
            }
            challenger.observe_f128_slice(&proof.yr);
            let queries = verify_and_sample_queries(
                challenger,
                query_nonce,
                config.grinding_bits[li] as u32,
                block_len,
                config.queries[li],
                strat(li),
            )?;
            if !verify_level_opens(
                prev_cap,
                block_len,
                &queries,
                &opening.opened_rows,
                1usize << k,
                &opening.merkle_proof,
                config.merkle_hash,
                strat(li),
            ) {
                return None;
            }
            // Direct consistency: Enc(yr)(x) against the folded leaf.
            for (row, &q) in opening.opened_rows.iter().zip(&queries) {
                let enc = proof
                    .yr
                    .iter()
                    .zip(novel_basis_evals(query_point(q), proof.yr.len()))
                    .fold(F128::ZERO, |acc, (&y, b)| acc + y * b);
                if enc != folded_leaf(row, &omega) {
                    return None;
                }
            }
            // Final claim: <yr, W_final> = v.
            let residual_log = c;
            if all_rs.len() + residual_log != log_n {
                return None;
            }
            let mut w = eval_b_residual(&all_rs, residual_log);
            if w.len() != 1usize << residual_log {
                return None;
            }
            for (dim, ctx) in &contexts {
                let fixed = &all_rs[log_n - dim..];
                let values = match ctx {
                    Context::Ood { point, beta } => {
                        eq_at_residual(point, fixed, residual_log, *beta)
                    }
                    Context::Consistency {
                        log_cols,
                        queries,
                        alpha,
                        beta,
                    } => induced_at_residual(*log_cols, queries, alpha, fixed, residual_log, *beta),
                };
                for (dst, v) in w.iter_mut().zip(values) {
                    *dst += v;
                }
            }
            let residual_claim = proof
                .yr
                .iter()
                .zip(&w)
                .fold(F128::ZERO, |acc, (&y, &b)| acc + y * b);
            let accepted = residual_claim == claim
                && ood_i == proof.ood_values.len()
                && claim_i == proof.claim_batch_grinding_nonces.len()
                && round_i == proof.rounds.len()
                && round_i == proof.fold_grinding_nonces.len()
                && answer_i == proof.answers.len()
                && li + 1 == proof.openings.len()
                && li + 1 == proof.grinding_nonces.len()
                && li == proof.recursive_caps.len()
                && li == proof.consistency_batch_grinding_nonces.len();
            return accepted.then_some(());
        }

        let cap = proof.recursive_caps.get(li)?;
        challenger.observe_bytes(cap.as_flattened());
        bind!(li + 1, c);

        let queries = verify_and_sample_queries(
            challenger,
            query_nonce,
            config.grinding_bits[li] as u32,
            block_len,
            config.queries[li],
            strat(li),
        )?;
        let &nonce = proof.consistency_batch_grinding_nonces.get(li)?;
        let alpha = verify_vec(
            challenger,
            consistency_grind(li),
            nonce,
            ceil_log2(config.queries[li]),
        )?;
        if !verify_level_opens(
            prev_cap,
            block_len,
            &queries,
            &opening.opened_rows,
            1usize << k,
            &opening.merkle_proof,
            config.merkle_hash,
            strat(li),
        ) {
            return None;
        }
        let enforced = batched_consistency(&opening.opened_rows, &level_rs, &alpha);
        let nonce = *next!(proof.claim_batch_grinding_nonces, claim_i);
        let beta = verify_vec(challenger, claim_grind(li + 1), nonce, 1)?[0];
        claim += beta * enforced;
        contexts.push((
            c,
            Context::Consistency {
                log_cols: c,
                queries,
                alpha,
                beta,
            },
        ));
        prev_cap = cap;
    }
    None
}

// ---------------------------------------------------------------------------
// The split verifier, for the comparison
// ---------------------------------------------------------------------------

/// Verify a split (F256) proof of `<witness, eq(point)> = target` made by
/// `recursive_prover_with_basis` on a dense LSB-lane L0. The split verifier
/// is crate-private; this entry lets a bench time it next to
/// [`verify_beep`] and `verify_affine`.
pub fn verify_split_eq_point<Ch: Challenger>(
    config: &VerifierConfig,
    proof: &LigeritoProof,
    log_n: usize,
    target: F128,
    expected_initial_cap: &[Hash],
    point: &[F128],
    challenger: &mut Ch,
) -> bool {
    recursive_verifier_with_basis_succinct(
        config,
        proof,
        log_n,
        target,
        expected_initial_cap,
        None,
        |rs, residual_log| {
            // eq(point) bound at rs: a prefix scalar times eq over the rest.
            let prefix = point
                .iter()
                .zip(rs)
                .fold(F256::ONE, |acc, (&z, &ri)| acc * (F256::ONE + F256::from(z) + ri));
            let rest = build_eq_table(&point[rs.len()..]);
            assert_eq!(rest.len(), 1usize << residual_log);
            rest.into_iter().map(|e| prefix * e).collect()
        },
        challenger,
    )
}

#[cfg(test)]
mod tests {
    use super::{
        BeepConfig, BeepProof, EqFactors, F128, Ladder, Level, MAX_SAMPLES, TARGET_BITS,
        affine_ladder, affine_ladder_at, affine_ladder_target, beep_ladder, beep_ladder_at,
        ceil_log2, dkt_exceptional_count, eq_factors, least_threshold, mca_dkt_ladder_at,
        mca_dkt_ladder_no_first_sample_at, mca_ladder_at, mca_ladder_no_first_sample_at, pow_searches,
        prove_beep, sample_bits, verify_beep,
    };
    use crate::{
        challenger::{Challenger, FsChallenger, RandomChallenger},
        lincheck::build_eq_table,
        merkle::HashKind,
        ntt::additive_ntt_f128::AdditiveNttF128,
        pcs::ligerito::{
            LigeritoProfile, ProverConfig, ligero_commit, partial_eval_lsb, prover_config_for,
        },
    };

    fn random_vec(rng: &mut RandomChallenger, len: usize) -> Vec<F128> {
        (0..len).map(|_| rng.sample_f128()).collect()
    }

    /// The kernels of a fold round against their definitions: the answers,
    /// the round polynomial, and the fold with the answers' claims added to
    /// the weight in the same pass.
    #[test]
    fn kernels_match_definitions() {
        let mut rng = RandomChallenger::new(0xBEE9_0003);
        let dot = |a: &[F128], b: &[F128]| {
            a.iter()
                .zip(b)
                .fold(F128::ZERO, |acc, (&x, &y)| acc + x * y)
        };
        for (dim, m) in [(1usize, 2usize), (2, 1), (5, 3), (11, 4), (12, 5), (13, 0)] {
            let n = 1usize << dim;
            let f = random_vec(&mut rng, n);
            let w = random_vec(&mut rng, n);
            let even = |v: &[F128]| v.iter().step_by(2).copied().collect::<Vec<_>>();
            let odd = |v: &[F128]| v.iter().skip(1).step_by(2).copied().collect::<Vec<_>>();
            let (f0, f1, w0, w1) = (even(&f), odd(&f), even(&w), odd(&w));
            let mut level = Level::new(f.clone(), w.clone(), dot(&f, &w));

            let zs: Vec<Vec<F128>> = (0..m).map(|_| random_vec(&mut rng, dim - 1)).collect();
            let eqs: Vec<EqFactors> = zs.iter().map(|z| eq_factors(z)).collect();
            let tables: Vec<Vec<F128>> = zs.iter().map(|z| build_eq_table(z)).collect();
            let answers = level.fold_answers(&eqs);
            assert_eq!(answers.len(), 2 * m);
            for (i, eq) in tables.iter().enumerate() {
                assert_eq!(answers[2 * i], dot(&f0, eq), "dim {dim}, point {i}, half 0");
                assert_eq!(answers[2 * i + 1], dot(&f1, eq), "dim {dim}, point {i}, half 1");
            }

            let msg = level.round_message();
            let sum = |a: &[F128], b: &[F128]| a.iter().zip(b).map(|(&x, &y)| x + y).collect::<Vec<_>>();
            assert_eq!(msg[0], dot(&f0, &w0), "h(0), dim {dim}");
            assert_eq!(msg[1], dot(&sum(&f0, &f1), &sum(&w0, &w1)), "h_2, dim {dim}");
            assert_eq!(msg[0] + dot(&f1, &w1), level.claim, "h(0) + h(1) is the claim");

            let r = rng.sample_f128();
            let coefs = random_vec(&mut rng, m);
            level.fold(r, msg, &eqs, &coefs);
            let fold = |a: &[F128], b: &[F128]| {
                a.iter().zip(b).map(|(&x, &y)| x + r * (x + y)).collect::<Vec<_>>()
            };
            let f_next = fold(&f0, &f1);
            let w_folded = fold(&w0, &w1);
            assert_eq!(level.f, f_next, "folded table, dim {dim}");
            assert_eq!(level.claim, dot(&f_next, &w_folded), "h(r), dim {dim}");
            let w_next: Vec<F128> = (0..n / 2)
                .map(|q| {
                    tables
                        .iter()
                        .zip(&coefs)
                        .fold(w_folded[q], |acc, (eq, &c)| acc + c * eq[q])
                })
                .collect();
            assert_eq!(level.w, w_next, "folded weight with the claims, dim {dim}");
        }
    }

    /// A small split config whose native ladder has three recursive levels,
    /// with the out-of-domain samples of the `Fast` profile (1 at L0, then 2).
    fn small_split(log_n: usize, initial_k: usize) -> ProverConfig {
        let ks = vec![2, 2, 2];
        let levels = ks.len() + 1;
        ProverConfig {
            log_inv_rates: vec![1, 2, 2, 3],
            recursive_steps: ks.len(),
            initial_log_msg_cols: log_n - initial_k,
            initial_log_num_interleaved: initial_k,
            initial_k,
            recursive_log_msg_cols: vec![0; ks.len()],
            recursive_ks: ks,
            queries: vec![23, 17, 13, 11],
            grinding_bits: vec![2; levels],
            fold_grinding_bits: vec![0; levels],
            claim_batch_grinding_bits: vec![1; levels],
            consistency_batch_grinding_bits: vec![1; levels],
            ood_samples: vec![1, 2, 2, 2],
            merkle_hash: HashKind::Blake3,
            stratified: vec![],
        }
    }

    /// The small ladder with its grinding cut down, so that the test does
    /// not spend its time on proofs of work, and with `ood` binding samples
    /// at every level, to cover the transcripts with none, one and two. The
    /// analysis of the ladder no longer applies to it; the protocol runs.
    fn small_ladder(ood: usize) -> (BeepConfig, usize) {
        let log_n = 14;
        let split = small_split(log_n, 3);
        let mut beep = beep_ladder(&split, log_n, &[1, 2, 2, 3], &[0.02; 4]).expect("ladder");
        assert_eq!(beep.prover.recursive_log_msg_cols, vec![9, 7, 5]);
        beep.prover.ood_samples = vec![ood; 4];
        beep.verifier.ood_samples = vec![ood; 4];
        for bits in [
            &mut beep.prover.fold_grinding_bits,
            &mut beep.prover.claim_batch_grinding_bits,
            &mut beep.prover.consistency_batch_grinding_bits,
        ] {
            bits.iter_mut().for_each(|b| *b = (*b).min(3));
        }
        beep.verifier.fold_grinding_bits = beep.prover.fold_grinding_bits.clone();
        beep.verifier.claim_batch_grinding_bits = beep.prover.claim_batch_grinding_bits.clone();
        beep.verifier.consistency_batch_grinding_bits =
            beep.prover.consistency_batch_grinding_bits.clone();
        beep.sync_bit_grinding();
        (beep, log_n)
    }

    struct Fixture {
        beep: BeepConfig,
        log_n: usize,
        basis: Vec<F128>,
        target: F128,
        cap: Vec<crate::merkle::Hash>,
        proof: BeepProof,
    }

    fn fixture(ood: usize) -> Fixture {
        fixture_with(ood, |beep| beep)
    }

    /// The fixture on the small ladder after `change`.
    fn fixture_with(ood: usize, change: impl FnOnce(BeepConfig) -> BeepConfig) -> Fixture {
        let (beep, log_n) = small_ladder(ood);
        let beep = change(beep);
        let initial_k = beep.prover.initial_k;
        let mut rng = RandomChallenger::new(0xBEE9_0002);
        let witness = random_vec(&mut rng, 1 << log_n);
        let z1 = random_vec(&mut rng, log_n);
        let z2 = random_vec(&mut rng, log_n);
        let gamma = rng.sample_f128();
        let basis: Vec<F128> = build_eq_table(&z1)
            .into_iter()
            .zip(build_eq_table(&z2))
            .map(|(a, b)| a + gamma * b)
            .collect();
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let rate = beep.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - initial_k + rate);
        let l0 = ligero_commit(
            &witness,
            log_n - initial_k,
            initial_k,
            rate,
            &ntt,
            HashKind::Blake3,
        );
        let cap = l0.cap(beep.prover.level_zero_cap_depth()).to_vec();
        let mut ch = FsChallenger::new(b"beep-test");
        let proof = prove_beep(&beep, witness, basis.clone(), target, &l0.mat, &l0.tree, &mut ch);
        Fixture {
            beep,
            log_n,
            basis,
            target,
            cap,
            proof,
        }
    }

    fn verifies(fx: &Fixture, proof: &BeepProof, target: F128) -> bool {
        let mut ch = FsChallenger::new(b"beep-test");
        verify_beep(
            &fx.beep,
            proof,
            fx.log_n,
            target,
            &fx.cap,
            |rs, residual_log| {
                let out = partial_eval_lsb(&fx.basis, rs);
                assert_eq!(out.len(), 1usize << residual_log);
                out
            },
            &mut ch,
        )
    }

    #[test]
    fn roundtrip() {
        for ood in [0, 1, 2] {
            let fx = fixture(ood);
            assert!(verifies(&fx, &fx.proof, fx.target), "ood = {ood}");
            let rounds: usize = fx.beep.prover.initial_k
                + fx.beep.prover.recursive_ks.iter().sum::<usize>();
            assert_eq!(fx.proof.rounds.len(), rounds);
            let answers: usize = (0..fx.beep.samples.len())
                .map(|li| {
                    let k = if li == 0 {
                        fx.beep.prover.initial_k
                    } else {
                        fx.beep.prover.recursive_ks[li - 1]
                    };
                    2 * fx.beep.samples[li] * k
                })
                .sum();
            assert_eq!(fx.proof.answers.len(), answers);
            assert_eq!(fx.proof.size_bytes(), fx.proof.size_breakdown().total());
            // One nonce per search of `pow_searches`, in every vector.
            let searches = pow_searches(&fx.beep.prover, Ladder::Beep);
            assert_eq!(fx.proof.fold_grinding_nonces.len(), searches.fold.len());
            assert_eq!(fx.proof.claim_batch_grinding_nonces.len(), searches.claim.len());
            assert_eq!(
                fx.proof.consistency_batch_grinding_nonces.len(),
                searches.consistency.len()
            );
            assert_eq!(fx.proof.grinding_nonces.len(), searches.queries.len());
            // One binding per level that has samples, and one glue per code switch.
            let levels = fx.beep.prover.recursive_steps + 1;
            assert_eq!(searches.claim.len(), if ood == 0 { 0 } else { levels } + levels - 1);
            assert_eq!(fx.proof.ood_values.len(), ood * levels);
            // The parts of the levels add up to the parts of the proof.
            let parts = fx.proof.level_bytes();
            let total = fx.proof.size_breakdown();
            assert_eq!(parts.len(), levels);
            assert_eq!(parts.iter().map(|l| l.leaves).sum::<usize>(), total.opened_rows);
            assert_eq!(parts.iter().map(|l| l.paths).sum::<usize>(), total.merkle_paths);
            assert_eq!(parts.iter().map(|l| l.cap).sum::<usize>(), total.caps);
            for (li, part) in parts.iter().enumerate() {
                assert_eq!(part.queries, fx.beep.prover.queries[li]);
            }
        }
    }

    #[test]
    fn rejects_tampering() {
        let fx = fixture(2);
        let one = F128::ONE;
        assert!(!verifies(&fx, &fx.proof, fx.target + one), "wrong target");
        let n_answers = fx.proof.answers.len();
        for i in [0, 1, n_answers / 2, n_answers - 1] {
            let mut bad = fx.proof.clone();
            bad.answers[i] += one;
            assert!(!verifies(&fx, &bad, fx.target), "answer {i}");
        }
        for i in [0, fx.proof.rounds.len() - 1] {
            for part in 0..2 {
                let mut bad = fx.proof.clone();
                bad.rounds[i][part] += one;
                assert!(!verifies(&fx, &bad, fx.target), "round {i} part {part}");
            }
        }
        let mut bad = fx.proof.clone();
        bad.yr[3] += one;
        assert!(!verifies(&fx, &bad, fx.target), "final message");
        for i in [0, 1, fx.proof.ood_values.len() - 1] {
            let mut bad = fx.proof.clone();
            bad.ood_values[i] += one;
            assert!(!verifies(&fx, &bad, fx.target), "binding value {i}");
        }
        let mut bad = fx.proof.clone();
        bad.ood_values.pop();
        assert!(!verifies(&fx, &bad, fx.target), "missing binding value");
        let mut bad = fx.proof.clone();
        bad.claim_batch_grinding_nonces.push(0);
        assert!(!verifies(&fx, &bad, fx.target), "extra claim nonce");
        let mut bad = fx.proof.clone();
        bad.openings[1].opened_rows[0][0] += one;
        assert!(!verifies(&fx, &bad, fx.target), "opened row");
        let mut bad = fx.proof.clone();
        bad.fold_grinding_nonces[0] ^= 1;
        assert!(!verifies(&fx, &bad, fx.target), "fold nonce");
        let mut bad = fx.proof.clone();
        bad.answers.pop();
        assert!(!verifies(&fx, &bad, fx.target), "missing answer");
        let mut bad = fx.proof.clone();
        bad.answers.push(one);
        assert!(!verifies(&fx, &bad, fx.target), "extra answer");
    }

    /// An honest fold of a wrong pair of halves is caught: the answers of a
    /// witness that differs from the committed one fail the final check.
    #[test]
    fn rejects_answers_of_another_witness() {
        let fx = fixture(1);
        let mut bad = fx.proof.clone();
        // Swap the two answers of the first point of the first round.
        bad.answers.swap(0, 1);
        assert!(!verifies(&fx, &bad, fx.target));
    }

    /// The selection on Flock's shapes: every level reaches the target, the
    /// threshold is the least one, and one point fewer does not reach it
    /// at that threshold.
    #[test]
    fn ladders_reach_the_target() {
        for (log_n, initial_k, rates) in [
            (20usize, 6usize, &[1usize, 3, 5][..]),
            (20, 6, &[1, 3, 6]),
            (22, 5, &[1, 3, 5, 7]),
            (24, 6, &[1, 3, 5, 7]),
            (25, 6, &[1, 3, 5, 7]),
        ] {
            let split = prover_config_for(log_n, initial_k, LigeritoProfile::Fast).expect("split");
            for eta in [0.02, 0.005, 0.001] {
                let beep = beep_ladder(&split, log_n, rates, &vec![eta; rates.len()])
                    .unwrap_or_else(|e| panic!("log_n {log_n}, eta {eta}: {e}"));
                assert!(beep.min_bits() >= TARGET_BITS, "log_n {log_n}, eta {eta}");
                for (li, lv) in beep.levels.iter().enumerate() {
                    assert!(lv.samples >= 1 && lv.samples <= MAX_SAMPLES);
                    assert!(lv.threshold > lv.line_bound, "level {li}");
                    let t = u128::from(lv.threshold);
                    assert_eq!(
                        least_threshold(
                            lv.list_size,
                            lv.max_variables,
                            lv.samples,
                            lv.line_bound,
                            TARGET_BITS
                        ),
                        Some(t)
                    );
                    assert!(
                        sample_bits(lv.list_size, lv.max_variables, lv.samples - 1, lv.line_bound, t)
                            < TARGET_BITS,
                        "level {li}: one point fewer must not reach the target"
                    );
                    assert_eq!(beep.prover.fold_grinding_bits[li], lv.fold_grinding_bits);
                    assert_eq!(beep.samples[li], lv.samples);
                    // The coefficients that batch the queries: the least grinding that
                    // covers the list of the next level times the degree, strictly.
                    let g = lv.consistency_batch_grinding_bits;
                    assert_eq!(beep.prover.consistency_batch_grinding_bits[li], g);
                    if let Some(next) = beep.levels.get(li + 1) {
                        let num = next.list_size * ceil_log2(lv.queries).max(1) as u64;
                        assert!(num < 1u64 << g, "level {li}: {num} against 2^{g}");
                        assert!(g == 0 || num >= 1u64 << (g - 1), "level {li}: not the least");
                        assert!(next.list_size >= lv.list_size, "the rate does not increase");
                    } else {
                        assert_eq!(g, 0, "the last level batches nothing");
                    }
                }
            }
        }
    }

    /// [`affine_ladder_at`] at the slack of the `Fast` profile is Flock's
    /// [`affine_ladder`], and a smaller slack takes fewer queries.
    /// Both provers on the same statement and transcript: `(fast, reference)`.
    fn prove_both(beep: &BeepConfig, log_n: usize) -> (BeepProof, BeepProof) {
        let initial_k = beep.prover.initial_k;
        let mut rng = RandomChallenger::new(0xBEE9_0003);
        let witness = random_vec(&mut rng, 1 << log_n);
        let basis = random_vec(&mut rng, 1 << log_n);
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let rate = beep.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - initial_k + rate);
        let l0 = ligero_commit(
            &witness,
            log_n - initial_k,
            initial_k,
            rate,
            &ntt,
            beep.prover.merkle_hash,
        );
        let run = |fast: bool| {
            let mut ch = FsChallenger::new(b"beep-both");
            super::prove_beep_impl(
                beep,
                witness.clone(),
                basis.clone(),
                target,
                &l0.mat,
                &l0.tree,
                &mut ch,
                fast,
            )
            .0
        };
        (run(true), run(false))
    }

    /// The rounds with one pass per round and factored claims write the
    /// proof of the reference rounds, byte for byte: on the small ladder
    /// with no, one and two binding samples per level, with and without
    /// points, and on ladders of the comparison.
    #[test]
    fn fast_rounds_match_reference() {
        for ood in [0, 1, 2] {
            let (beep, log_n) = small_ladder(ood);
            let (fast, reference) = prove_both(&beep, log_n);
            assert_eq!(fast, reference, "small ladder, ood = {ood}");
            let mut control = beep.clone();
            control.samples.iter_mut().for_each(|m| *m = 0);
            let (fast, reference) = prove_both(&control, log_n);
            assert_eq!(fast, reference, "small ladder without points, ood = {ood}");
        }
        for (log_n, k0, rates, eta) in [
            (16usize, 6usize, vec![1usize, 6], 0.001),
            (17, 6, vec![1, 5], 0.02),
            (20, 6, vec![1, 3, 6], 0.001),
        ] {
            let split = prover_config_for(log_n, k0, LigeritoProfile::Fast).expect("split");
            let beep = beep_ladder(&split, log_n, &rates, &vec![eta; rates.len()]).expect("ladder");
            let (fast, reference) = prove_both(&beep, log_n);
            assert_eq!(fast, reference, "2^{log_n} words at eta = {eta}");
            let nb = beep.without_first_binding().expect("no first binding");
            let (fast, reference) = prove_both(&nb, log_n);
            assert_eq!(fast, reference, "2^{log_n} words, no first binding");
        }
    }

    /// The thresholds of `with_exact_grinding` are the largest ones that keep
    /// every ground squeeze below `2^-128`, the proofs under them verify,
    /// both provers write the same proof, and the work is at most that of
    /// the bits.
    #[test]
    fn exact_grinding() {
        for (log_n, k0, rates, eta) in [
            (16usize, 6usize, vec![1usize, 6], 0.001),
            (20, 6, vec![1, 3, 6], 0.02),
        ] {
            let split = prover_config_for(log_n, k0, LigeritoProfile::Fast).expect("split");
            let bits = beep_ladder(&split, log_n, &rates, &vec![eta; rates.len()])
                .expect("ladder")
                .without_first_binding()
                .expect("no first binding");
            let exact = bits.with_exact_grinding();
            assert!(exact.min_bits() >= TARGET_BITS, "{}", exact.min_bits());
            let last = exact.levels.len() - 1;
            for (li, lv) in exact.levels.iter().enumerate() {
                let mut pairs = vec![
                    (exact.fold[li], lv.fold_numerator, lv.fold_grinding_bits),
                    (exact.claim[li], lv.claim_numerator, lv.claim_batch_grinding_bits),
                ];
                if li < last {
                    pairs.push((
                        exact.consistency[li],
                        lv.consistency_numerator,
                        lv.consistency_batch_grinding_bits,
                    ));
                } else {
                    assert_eq!(exact.consistency[li], super::Grind::Bits(0));
                }
                for (grind, numerator, grinding_bits) in pairs {
                    let super::Grind::Below(target) = grind else {
                        panic!("level {li}: a threshold is expected")
                    };
                    let (m, t) = (u128::from(numerator), u128::from(target));
                    // The squeeze stays below 2^-128, and no larger threshold does.
                    assert!(m * t < 1u128 << 64 && m * (t + 1) >= 1u128 << 64);
                    // The bits cover the numerator, so the threshold never asks for more work.
                    assert!(m < 1u128 << grinding_bits);
                    assert!(grind.work() <= (grinding_bits as f64).exp2());
                    assert!(grind.work() >= numerator as f64);
                }
            }
            assert!(exact.expected_pow_hashes() < bits.expected_pow_hashes());
            assert_eq!(
                bits.expected_pow_hashes(),
                pow_searches(&bits.prover, Ladder::Beep).expected_hashes()
            );
            let (fast, reference) = prove_both(&exact, log_n);
            assert_eq!(fast, reference, "2^{log_n} words, thresholds");
            let (fast_bits, _) = prove_both(&bits, log_n);
            assert_eq!(fast.size_bytes(), fast_bits.size_bytes());
            assert_ne!(fast, fast_bits);
        }
        // On the small ladder: the proof verifies under its own grinding and not under the other.
        let base = fixture(2);
        let fx = fixture_with(2, |b| b.with_exact_grinding());
        assert!(verifies(&fx, &fx.proof, fx.target));
        assert!(!verifies(&base, &fx.proof, fx.target));
        assert!(!verifies(&fx, &base.proof, base.target));
    }

    /// The ladders at 100 bits, on the shapes of Flock's `Fast100` and
    /// `Slim100` configurations: every level reaches the target with the
    /// least threshold for it, it takes fewer queries than at 128 bits, the
    /// fold squeezes need no proof of work on these shapes, the thresholds
    /// of `with_exact_grinding` are the largest ones for the target, both
    /// provers write the same proof, and a proof verifies.
    #[test]
    fn ladders_at_100_bits() {
        let target_bits = 100.0;
        for (log_n, k0, profile, strict, rates, eta) in [
            (16usize, 6usize, LigeritoProfile::Fast100, LigeritoProfile::Fast, vec![1usize, 6], 0.001),
            (20, 6, LigeritoProfile::Fast100, LigeritoProfile::Fast, vec![1, 3, 6], 0.02),
            (22, 5, LigeritoProfile::Slim100, LigeritoProfile::Slim, vec![2, 4, 6, 8], 0.001),
        ] {
            let split = prover_config_for(log_n, k0, profile).expect("split");
            let etas = vec![eta; rates.len()];
            let bits = beep_ladder_at(&split, log_n, &rates, &etas, target_bits)
                .unwrap_or_else(|e| panic!("log_n {log_n}: {e}"));
            assert_eq!(bits.target_bits, target_bits);
            assert!(bits.min_bits() >= target_bits, "{}", bits.min_bits());
            let split128 = prover_config_for(log_n, k0, strict).expect("split at 128 bits");
            let at128 = beep_ladder(&split128, log_n, &rates, &etas).expect("ladder at 128 bits");
            assert_eq!(at128.target_bits, TARGET_BITS);
            for (li, lv) in bits.levels.iter().enumerate() {
                let t = u128::from(lv.threshold);
                assert_eq!(
                    least_threshold(lv.list_size, lv.max_variables, lv.samples, lv.line_bound, target_bits),
                    Some(t),
                    "level {li}"
                );
                assert!(
                    sample_bits(lv.list_size, lv.max_variables, lv.samples - 1, lv.line_bound, t)
                        < target_bits,
                    "level {li}: one point fewer must not reach the target"
                );
                assert_eq!(lv.fold_grinding_bits, 0, "level {li}: (t + 3L) / 2^128 is below 2^-100");
                assert!(lv.fold_numerator < 1 << 28, "level {li}");
                assert!(lv.queries < at128.levels[li].queries, "level {li}: fewer queries");
                assert!(lv.threshold <= at128.levels[li].threshold, "level {li}");
            }
            let exact = bits
                .without_first_binding()
                .expect("no first binding")
                .with_exact_grinding();
            assert!(exact.min_bits() >= target_bits, "{}", exact.min_bits());
            let last = exact.levels.len() - 1;
            for (li, lv) in exact.levels.iter().enumerate() {
                let mut pairs = vec![
                    (exact.fold[li], lv.fold_numerator),
                    (exact.claim[li], lv.claim_numerator),
                ];
                if li < last {
                    pairs.push((exact.consistency[li], lv.consistency_numerator));
                }
                for (grind, numerator) in pairs {
                    let m = u128::from(numerator);
                    match grind {
                        // No proof of work: the squeeze is below 2^-100 as it is.
                        super::Grind::Bits(0) => assert!(m < 1u128 << 28, "level {li}"),
                        // The largest threshold that keeps it below 2^-100.
                        super::Grind::Below(t) => {
                            let t = u128::from(t);
                            assert!(m * t < 1u128 << 92 && m * (t + 1) >= 1u128 << 92, "level {li}");
                        }
                        other => panic!("level {li}: {other:?}"),
                    }
                }
            }
            let (fast, reference) = prove_both(&exact, log_n);
            assert_eq!(fast, reference, "2^{log_n} words at 100 bits");
        }

        // A proof of the ladder for 2^16 words verifies, and a tampered one does not.
        let log_n = 16;
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
        let beep = beep_ladder_at(&split, log_n, &[1, 6], &[0.001; 2], target_bits)
            .expect("ladder")
            .without_first_binding()
            .expect("no first binding")
            .with_exact_grinding();
        let mut rng = RandomChallenger::new(0xBEE9_0100);
        let witness = random_vec(&mut rng, 1 << log_n);
        let z = random_vec(&mut rng, log_n);
        let basis = build_eq_table(&z);
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let k0 = beep.prover.initial_k;
        let rate = beep.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - k0 + rate);
        let l0 = ligero_commit(&witness, log_n - k0, k0, rate, &ntt, beep.prover.merkle_hash);
        let cap = l0.cap(beep.prover.level_zero_cap_depth()).to_vec();
        let mut ch = FsChallenger::new(b"beep-100");
        let proof = prove_beep(&beep, witness, basis.clone(), target, &l0.mat, &l0.tree, &mut ch);
        let check = |proof: &BeepProof| {
            let mut ch = FsChallenger::new(b"beep-100");
            verify_beep(
                &beep,
                proof,
                log_n,
                target,
                &cap,
                |rs, residual_log| {
                    let out = partial_eval_lsb(&basis, rs);
                    assert_eq!(out.len(), 1usize << residual_log);
                    out
                },
                &mut ch,
            )
        };
        assert!(check(&proof));
        let mut bad = proof.clone();
        bad.answers.swap(0, 1);
        assert!(!check(&bad));
    }

    /// [`mca_ladder_at`] at 100 bits: the ladder of [`beep_ladder_at`] with no
    /// points, the same queries, a fold grinding per round that covers
    /// Flock's MCA numerator of that round over `F128` (and, in bits, no more
    /// than one bit above that of the first round), both provers write the
    /// same proof, and a proof verifies.
    #[test]
    fn mca_ladder_at_100_bits() {
        let target_bits = 100.0;
        for (log_n, rates) in [(16usize, vec![1usize, 3]), (20, vec![1, 3, 5])] {
            let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
            let etas = vec![0.02; rates.len()];
            let beep = beep_ladder_at(&split, log_n, &rates, &etas, target_bits).expect("BEEP ladder");
            let mca = mca_ladder_at(&split, log_n, &rates, &etas, target_bits)
                .unwrap_or_else(|e| panic!("log_n {log_n}: {e}"));
            assert!(mca.min_bits() >= target_bits, "{}", mca.min_bits());
            assert!(mca.samples.iter().all(|&m| m == 0));
            assert_eq!(mca.prover.queries, beep.prover.queries);
            assert_eq!(mca.prover.ood_samples, split.ood_samples[..rates.len()].to_vec());
            for (li, lv) in mca.levels.iter().enumerate() {
                let log_a =
                    crate::pcs::ligerito::paper_johnson_log_a(lv.log_inv_rate, lv.eta, lv.log_msg_cols, lv.folds);
                let num = lv.fold_numerator as f64;
                assert!(num >= log_a.exp2(), "level {li}");
                // The grinding is the least whole number of bits for the numerator.
                let need = num.log2() - 28.0;
                assert!(lv.fold_grinding_bits as f64 > need, "level {li}");
                assert!((lv.fold_grinding_bits as f64) <= need.max(0.0) + 1.0, "level {li}");
                assert_eq!(mca.prover.fold_grinding_bits[li], lv.fold_grinding_bits);
            }
            // A long code needs a proof of work on its fold challenges.
            assert!(mca.levels[0].fold_grinding_bits > 0);
            let exact = mca.with_exact_grinding();
            assert!(exact.min_bits() >= target_bits, "{}", exact.min_bits());
            // One numerator and one grind per fold round: round j folds
            // 2^(folds − 1 − j) pairs of rows, so its numerator is that of
            // round 0 with a_0 halved j times.
            let numerators = mca.fold_round_numerators.as_ref().expect("numerators per round");
            let rounds = exact.fold_rounds.as_ref().expect("grinds per round");
            let in_bits = mca.fold_rounds.as_ref().expect("bits per round");
            for (li, lv) in mca.levels.iter().enumerate() {
                assert_eq!(numerators[li].len(), lv.folds);
                assert_eq!(numerators[li][0], lv.fold_numerator);
                assert_eq!(in_bits[li][0], super::Grind::Bits(lv.fold_grinding_bits as u32));
                let log_a =
                    crate::pcs::ligerito::paper_johnson_log_a(lv.log_inv_rate, lv.eta, lv.log_msg_cols, lv.folds);
                for (j, (&num, &grind)) in numerators[li].iter().zip(&rounds[li]).enumerate() {
                    assert!(num as f64 >= (log_a - j as f64).exp2(), "level {li}, round {j}");
                    assert!(j == 0 || num < numerators[li][j - 1], "level {li}, round {j}");
                    assert_eq!(grind, super::Grind::exact_at(num, target_bits));
                    assert_eq!(exact.fold_grind(li, j), grind);
                    assert_eq!(mca.fold_grind(li, j), in_bits[li][j]);
                    // A search tries about numerator / 2^28 hashes, and the bits cover the numerator.
                    assert!(grind.work() <= num as f64 / 28f64.exp2() * 1.000001 + 1.0, "level {li}, round {j}");
                    assert!(in_bits[li][j].bits() > (num as f64).log2() - 28.0, "level {li}, round {j}");
                }
            }
            let grinds = exact.pow_grinds();
            assert_eq!(grinds.fold.len(), mca.levels.iter().map(|l| l.folds).sum::<usize>());
            assert_eq!(grinds.fold[..mca.levels[0].folds], rounds[0][..]);
            // The first level has 2^6 rows: its six searches try less than half
            // the hashes of six searches of its first round.
            let first: f64 = rounds[0].iter().map(|g| g.work()).sum();
            assert!(first < 0.5 * 6.0 * rounds[0][0].work(), "{first}");
            let (fast, reference) = prove_both(&exact, log_n);
            assert_eq!(fast, reference, "2^{log_n} words, MCA ladder");
        }

        let log_n = 16;
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
        let mca = mca_ladder_at(&split, log_n, &[1, 3], &[0.02; 2], target_bits)
            .expect("ladder")
            .with_exact_grinding();
        let mut rng = RandomChallenger::new(0xBEE9_0101);
        let witness = random_vec(&mut rng, 1 << log_n);
        let z = random_vec(&mut rng, log_n);
        let basis = build_eq_table(&z);
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let k0 = mca.prover.initial_k;
        let rate = mca.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - k0 + rate);
        let l0 = ligero_commit(&witness, log_n - k0, k0, rate, &ntt, mca.prover.merkle_hash);
        let cap = l0.cap(mca.prover.level_zero_cap_depth()).to_vec();
        let mut ch = FsChallenger::new(b"mca-100");
        let proof = prove_beep(&mca, witness, basis.clone(), target, &l0.mat, &l0.tree, &mut ch);
        assert!(proof.answers.is_empty(), "no points, no answers");
        let check = |proof: &BeepProof, target: F128| {
            let mut ch = FsChallenger::new(b"mca-100");
            verify_beep(
                &mca,
                proof,
                log_n,
                target,
                &cap,
                |rs, residual_log| {
                    let out = partial_eval_lsb(&basis, rs);
                    assert_eq!(out.len(), 1usize << residual_log);
                    out
                },
                &mut ch,
            )
        };
        assert!(check(&proof, target));
        assert!(!check(&proof, target + F128::ONE));
    }

    /// [`mca_ladder_no_first_sample_at`] is [`mca_ladder_at`] without the
    /// binding sample of level 0 and with nothing else changed: the same
    /// fold numerators and proofs of work per fold round, one claim-batching
    /// search fewer, a proof that is one binding value shorter, that
    /// verifies, and that the ladder with the sample rejects.
    #[test]
    fn mca_ladder_no_first_sample() {
        let (target_bits, log_n, rates) = (100.0, 16usize, [1usize, 3]);
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
        let with = mca_ladder_at(&split, log_n, &rates, &[0.02; 2], target_bits).expect("ladder");
        let nf = mca_ladder_no_first_sample_at(&split, log_n, &rates, &[0.02; 2], target_bits).expect("ladder");
        assert!(with.prover.ood_samples[0] > 0);
        assert_eq!(nf.prover.ood_samples[0], 0);
        assert_eq!(nf.verifier.ood_samples, nf.prover.ood_samples);
        assert_eq!(nf.prover.ood_samples[1..], with.prover.ood_samples[1..]);
        assert!(nf.samples.iter().all(|&m| m == 0));
        assert_eq!(nf.prover.queries, with.prover.queries);
        assert_eq!(nf.prover.fold_grinding_bits, with.prover.fold_grinding_bits);
        for (a, b) in nf.levels.iter().zip(&with.levels) {
            assert_eq!(a.fold_numerator, b.fold_numerator);
        }
        assert!(nf.fold_round_numerators.is_some());
        assert_eq!(nf.fold_round_numerators, with.fold_round_numerators);
        assert_eq!(nf.fold_rounds, with.fold_rounds);
        assert_eq!(nf.levels[1..], with.levels[1..]);
        assert!(nf.min_bits() >= target_bits, "{}", nf.min_bits());
        let (with, nf) = (with.with_exact_grinding(), nf.with_exact_grinding());
        assert!(nf.min_bits() >= target_bits, "{}", nf.min_bits());
        let (a, b) = (with.pow_grinds(), nf.pow_grinds());
        assert_eq!(b.claim.len() + 1, a.claim.len());
        assert_eq!((&b.fold, &b.consistency, &b.queries), (&a.fold, &a.consistency, &a.queries));
        let (fast, reference) = prove_both(&nf, log_n);
        assert_eq!(fast, reference, "MCA ladder with no first sample");

        let mut rng = RandomChallenger::new(0xBEE9_0102);
        let witness = random_vec(&mut rng, 1 << log_n);
        let z = random_vec(&mut rng, log_n);
        let basis = build_eq_table(&z);
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let k0 = nf.prover.initial_k;
        let rate = nf.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - k0 + rate);
        let l0 = ligero_commit(&witness, log_n - k0, k0, rate, &ntt, nf.prover.merkle_hash);
        let cap = l0.cap(nf.prover.level_zero_cap_depth()).to_vec();
        let prove = |config: &BeepConfig| {
            let mut ch = FsChallenger::new(b"mca-nf-100");
            prove_beep(config, witness.clone(), basis.clone(), target, &l0.mat, &l0.tree, &mut ch)
        };
        let check = |config: &BeepConfig, proof: &BeepProof, target: F128| {
            let mut ch = FsChallenger::new(b"mca-nf-100");
            verify_beep(
                config,
                proof,
                log_n,
                target,
                &cap,
                |rs, residual_log| {
                    let out = partial_eval_lsb(&basis, rs);
                    assert_eq!(out.len(), 1usize << residual_log);
                    out
                },
                &mut ch,
            )
        };
        let (proof_nf, proof_with) = (prove(&nf), prove(&with));
        assert!(proof_nf.answers.is_empty(), "no points, no answers");
        assert_eq!(proof_nf.ood_values.len() + with.prover.ood_samples[0], proof_with.ood_values.len());
        assert!(proof_nf.size_bytes() < proof_with.size_bytes());
        assert!(check(&nf, &proof_nf, target));
        assert!(check(&with, &proof_with, target));
        assert!(!check(&nf, &proof_nf, target + F128::ONE));
        assert!(!check(&with, &proof_nf, target));
    }

    /// [`dkt_exceptional_count`] against values computed from the statement
    /// of the theorem (real ceilings with 80-digit decimals, the count as an
    /// exact fraction, rounded up): codes of rates 1/2, 1/4, 1/8 and 2^-9,
    /// with `m` from 3 to 354, one with `B_jet > 2D + 1`, and the instance
    /// `(n, D, A) = (1024, 511, 744)` of the theorem's own agreement at `η_0
    /// = 0.02`. In the last three instances a real quantity under a ceiling
    /// is a whole number, which pins the strict inequalities of the integer
    /// form (found by the independent check of this function): for `(64, 9,
    /// 27)`, `√(D/n) / (2 η_0) = 4`, `t √(n/D) = 12` and `t² n / (3D) = 48`;
    /// for `(16, 1, 8)`, `t √(n/D) = 14`; for `(48, 4, 20)`, `t² n / (3D) =
    /// 49`.
    #[test]
    fn dkt_exceptional_count_values() {
        for (n, dim, agreement, count) in [
            (1024u64, 512u64, 745u64, 21_483_639u128),
            (1024, 512, 744, 26_164_695),
            (1 << 18, 1 << 17, 185_889, 6_595_801_891_350),
            (1 << 16, 1 << 13, 24_482, 707_284_599),
            (1024, 512, 878, 82_043),
            (1 << 21, 1 << 20, 1_485_008, 422_558_744_513_390),
            (1 << 13, 1 << 4, 526, 171_236_999),
            (8, 2, 4, 2_859),
            (64, 10, 27, 53_028),
            (16, 2, 8, 8_242),
            (48, 5, 20, 23_829),
        ] {
            assert_eq!(
                dkt_exceptional_count(n, dim, agreement),
                Ok(count),
                "n = {n}, dimension {dim}, agreement {agreement}"
            );
            // The closed form of the theorem, (8/3) n t³ / (D/n): t = m + 1/2
            // for the least m ≥ 3 with 2 m η_0 ≥ √(D/n).
            let (nf, df, af) = (n as f64, (dim - 1) as f64, agreement as f64);
            let m = ((df / nf).sqrt() / (2.0 * (af / nf - (df / nf).sqrt()))).ceil().max(3.0);
            let closed = 8.0 / 3.0 * nf * (m + 0.5).powi(3) * nf / df;
            assert!((count as f64) < closed, "n = {n}, dimension {dim}: {count} against {closed}");
            assert!((count as f64) > closed / 4.0, "n = {n}, dimension {dim}: {count} against {closed}");
        }
        // No bound at or below the Johnson agreement of the theorem (723² ≤
        // 1024 · 511 < 724²), for a constant code, or for the full space.
        assert!(dkt_exceptional_count(1024, 512, 723).is_err());
        assert!(dkt_exceptional_count(1024, 512, 724).is_ok());
        assert!(dkt_exceptional_count(1024, 1, 900).is_err());
        assert!(dkt_exceptional_count(1024, 1024, 1024).is_err());
        assert!(dkt_exceptional_count(1024, 512, 1025).is_err());
    }

    /// [`mca_dkt_ladder_at`] at 100 bits: the ladder of [`beep_ladder_at`]
    /// at the same slacks with no points, the same queries, binding samples
    /// and batching, and one fold numerator per level, `E + ⌈2L⌉` for the
    /// count `E` of DKT26 at the agreement of the level, below Flock's
    /// numerator of every round. Its proofs of work cover that numerator,
    /// both provers write the same proof, and a proof of the ladder with no
    /// first sample verifies.
    #[test]
    fn mca_dkt_ladder_at_100_bits() {
        let target_bits = 100.0;
        for (log_n, rates) in [(16usize, vec![1usize, 3]), (20, vec![1, 3, 5])] {
            let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
            for eta in [0.02, 0.002] {
                let etas = vec![eta; rates.len()];
                let beep = beep_ladder_at(&split, log_n, &rates, &etas, target_bits).expect("BEEP ladder");
                let dkt = mca_dkt_ladder_at(&split, log_n, &rates, &etas, target_bits)
                    .unwrap_or_else(|e| panic!("log_n {log_n}, eta {eta}: {e}"));
                assert!(dkt.min_bits() >= target_bits, "{}", dkt.min_bits());
                assert!(dkt.samples.iter().all(|&m| m == 0));
                assert_eq!(dkt.prover.queries, beep.prover.queries);
                assert_eq!(dkt.prover.ood_samples, beep.prover.ood_samples);
                assert_eq!(dkt.prover.grinding_bits, beep.prover.grinding_bits);
                assert_eq!(dkt.prover.claim_batch_grinding_bits, beep.prover.claim_batch_grinding_bits);
                assert_eq!(
                    dkt.prover.consistency_batch_grinding_bits,
                    beep.prover.consistency_batch_grinding_bits
                );
                assert!(dkt.fold_round_numerators.is_none() && dkt.fold_rounds.is_none());
                for (li, lv) in dkt.levels.iter().enumerate() {
                    assert_eq!(lv.agreement, beep.levels[li].agreement, "level {li}");
                    let n = 1u64 << (lv.log_msg_cols + lv.log_inv_rate);
                    let count = dkt_exceptional_count(n, 1 << lv.log_msg_cols, lv.agreement).expect("count");
                    let rho = (-(lv.log_inv_rate as f64)).exp2();
                    let two_lists = (2.0 * (1.0 / (2.0 * lv.eta * rho.sqrt()))).ceil() as u128;
                    assert_eq!(u128::from(lv.fold_numerator), count + two_lists, "level {li}");
                    // The grinding is the least whole number of bits for the numerator.
                    let need = (lv.fold_numerator as f64).log2() - 28.0;
                    assert!(lv.fold_grinding_bits as f64 > need, "level {li}");
                    assert!((lv.fold_grinding_bits as f64) <= need.max(0.0) + 1.0, "level {li}");
                    assert_eq!(dkt.prover.fold_grinding_bits[li], lv.fold_grinding_bits);
                    assert_eq!(dkt.verifier.fold_grinding_bits[li], lv.fold_grinding_bits);
                }
                // Below Flock's bound of every round, where that ladder exists
                // (at a small slack it asks for more grinding than the selection accepts).
                if let Ok(mca) = mca_ladder_at(&split, log_n, &rates, &etas, target_bits) {
                    let flock = mca.fold_round_numerators.as_ref().expect("numerators per round");
                    for (li, lv) in dkt.levels.iter().enumerate() {
                        let least = *flock[li].iter().min().expect("a round");
                        assert!(lv.fold_numerator < least, "level {li}: {} against {least}", lv.fold_numerator);
                    }
                } else {
                    assert!(eta < 0.02, "Flock's ladder exists at its own slack");
                }
                let exact = dkt.with_exact_grinding();
                assert!(exact.min_bits() >= target_bits, "{}", exact.min_bits());
                let grinds = exact.pow_grinds();
                assert_eq!(grinds.fold.len(), dkt.levels.iter().map(|l| l.folds).sum::<usize>());
                let mut at = 0;
                for (li, lv) in dkt.levels.iter().enumerate() {
                    let grind = super::Grind::exact_at(lv.fold_numerator, target_bits);
                    // A search tries about numerator / 2^28 hashes.
                    assert!(grind.work() <= lv.fold_numerator as f64 / 28f64.exp2() * 1.000001 + 1.0, "level {li}");
                    for j in 0..lv.folds {
                        assert_eq!(grinds.fold[at], grind, "level {li}, round {j}");
                        assert_eq!(exact.fold_grind(li, j), grind);
                        at += 1;
                    }
                }
                let (fast, reference) = prove_both(&exact, log_n);
                assert_eq!(fast, reference, "2^{log_n} words, eta {eta}, MCA ladder with the bound of DKT26");
            }
        }

        // The ladder with no first sample: the same fold rounds, no binding
        // sample of level 0, and a proof that verifies.
        let (log_n, rates) = (16usize, [1usize, 3]);
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
        let with = mca_dkt_ladder_at(&split, log_n, &rates, &[0.002; 2], target_bits).expect("ladder");
        let nf = mca_dkt_ladder_no_first_sample_at(&split, log_n, &rates, &[0.002; 2], target_bits).expect("ladder");
        assert!(with.prover.ood_samples[0] > 0);
        assert_eq!(nf.prover.ood_samples[0], 0);
        assert_eq!(nf.verifier.ood_samples, nf.prover.ood_samples);
        assert_eq!(nf.prover.ood_samples[1..], with.prover.ood_samples[1..]);
        assert_eq!(nf.prover.queries, with.prover.queries);
        assert_eq!(nf.prover.fold_grinding_bits, with.prover.fold_grinding_bits);
        assert_eq!(nf.levels[1..], with.levels[1..]);
        for (a, b) in nf.levels.iter().zip(&with.levels) {
            assert_eq!(a.fold_numerator, b.fold_numerator);
        }
        let nf = nf.with_exact_grinding();
        assert!(nf.min_bits() >= target_bits, "{}", nf.min_bits());
        let mut rng = RandomChallenger::new(0xBEE9_0103);
        let witness = random_vec(&mut rng, 1 << log_n);
        let z = random_vec(&mut rng, log_n);
        let basis = build_eq_table(&z);
        let target = witness
            .iter()
            .zip(&basis)
            .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
        let k0 = nf.prover.initial_k;
        let rate = nf.prover.log_inv_rates[0];
        let ntt = AdditiveNttF128::standard(log_n - k0 + rate);
        let l0 = ligero_commit(&witness, log_n - k0, k0, rate, &ntt, nf.prover.merkle_hash);
        let cap = l0.cap(nf.prover.level_zero_cap_depth()).to_vec();
        let mut ch = FsChallenger::new(b"mca-dkt-100");
        let proof = prove_beep(&nf, witness, basis.clone(), target, &l0.mat, &l0.tree, &mut ch);
        assert!(proof.answers.is_empty(), "no points, no answers");
        let check = |proof: &BeepProof, target: F128| {
            let mut ch = FsChallenger::new(b"mca-dkt-100");
            verify_beep(
                &nf,
                proof,
                log_n,
                target,
                &cap,
                |rs, residual_log| {
                    let out = partial_eval_lsb(&basis, rs);
                    assert_eq!(out.len(), 1usize << residual_log);
                    out
                },
                &mut ch,
            )
        };
        assert!(check(&proof, target));
        assert!(!check(&proof, target + F128::ONE));
        let mut bad = proof.clone();
        bad.fold_grinding_nonces[0] ^= 1;
        assert!(!check(&bad, target));

        // At 128 bits over a field of 2^128 elements every fold challenge
        // needs a proof of work for its whole numerator: at least 2^19
        // hashes per round for 2^16 words at the slacks 0.02 and 0.1.
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast).expect("split");
        for eta in [0.02, 0.1] {
            let dkt = mca_dkt_ladder_no_first_sample_at(&split, log_n, &rates, &[eta; 2], TARGET_BITS).expect("ladder");
            assert!(dkt.min_bits() >= TARGET_BITS, "{}", dkt.min_bits());
            assert!(dkt.levels[0].fold_grinding_bits >= 19, "eta {eta}: {}", dkt.levels[0].fold_grinding_bits);
            let work = dkt.with_exact_grinding().pow_grinds().fold[0].work();
            assert!(work >= dkt.levels[0].fold_numerator as f64 * 0.999, "eta {eta}");
        }
    }

    /// [`affine_ladder_target`] at 128 bits is [`affine_ladder_at`]. At 100
    /// bits, on Flock's `Fast100` configuration, a level takes fewer queries
    /// and its batching coefficients need no proof of work.
    #[test]
    fn affine_ladder_at_100_bits() {
        let (log_n, rates, etas, fold) = (20usize, [1usize, 3, 6], [0.02; 3], [4usize, 5, 5]);
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast).expect("split");
        let at = affine_ladder_at(&split, log_n, &rates, &etas, &fold).expect("ladder");
        let same =
            affine_ladder_target(&split, log_n, &rates, &etas, &fold, TARGET_BITS).expect("ladder");
        assert_eq!(same.0.queries, at.0.queries);
        assert_eq!(same.0.claim_batch_grinding_bits, at.0.claim_batch_grinding_bits);
        assert_eq!(
            same.0.consistency_batch_grinding_bits,
            at.0.consistency_batch_grinding_bits
        );
        let split100 = prover_config_for(log_n, 6, LigeritoProfile::Fast100).expect("split");
        let low = affine_ladder_target(&split100, log_n, &rates, &etas, &[0; 3], 100.0).expect("ladder");
        assert_eq!(low.0.fold_grinding_bits, vec![0; 3]);
        assert_eq!(low.0.claim_batch_grinding_bits, vec![0; 3]);
        assert_eq!(low.0.consistency_batch_grinding_bits, vec![0; 3]);
        assert_eq!(low.1.queries, low.0.queries);
        for li in 0..3 {
            assert!(low.0.queries[li] < at.0.queries[li], "level {li}");
        }
    }

    /// `with_fold_grinding` changes the proofs of work of the fold challenges
    /// and nothing else, and the prover and the verifier agree on it.
    #[test]
    fn fold_grinding_override() {
        let base = fixture(2);
        let bits = vec![1usize, 0, 2, 1];
        assert_ne!(base.beep.prover.fold_grinding_bits, bits);
        let fx = fixture_with(2, |b| b.with_fold_grinding(&bits).expect("override"));
        assert_eq!(fx.beep.prover.fold_grinding_bits, bits);
        assert_eq!(fx.beep.verifier.fold_grinding_bits, bits);
        assert_eq!(fx.beep.samples, base.beep.samples);
        assert_eq!(fx.beep.prover.queries, base.beep.prover.queries);
        assert_eq!(fx.beep.levels, base.beep.levels);
        assert!(verifies(&fx, &fx.proof, fx.target));
        assert_eq!(fx.proof.size_bytes(), base.proof.size_bytes());
        assert_eq!(
            pow_searches(&fx.beep.prover, Ladder::Beep).fold,
            vec![1, 1, 1, 0, 0, 2, 2, 1, 1]
        );
        assert!(base.beep.with_fold_grinding(&[1, 2]).is_err());
        assert!(base.beep.with_fold_grinding(&[41, 0, 0, 0]).is_err());
    }

    /// `without_first_binding` drops the binding sample of level 0 and
    /// nothing else: the proof has one binding value and one claim-batching
    /// nonce fewer, and it verifies.
    #[test]
    fn no_first_binding() {
        let log_n = 24;
        let split = prover_config_for(log_n, 6, LigeritoProfile::Fast).expect("split");
        let beep = beep_ladder(&split, log_n, &[1, 3, 5, 7], &[0.001; 4]).expect("ladder");
        let nb = beep.without_first_binding().expect("no first binding");
        assert_eq!(nb.prover.ood_samples, vec![0, 2, 2, 2]);
        assert_eq!(nb.verifier.ood_samples, nb.prover.ood_samples);
        assert_eq!(nb.samples, beep.samples);
        assert_eq!(nb.prover.queries, beep.prover.queries);
        assert!(nb.levels[0].ood_bits >= TARGET_BITS && nb.min_bits() >= TARGET_BITS);
        assert_eq!(nb.levels[1..], beep.levels[1..]);
        let (a, b) = (
            pow_searches(&beep.prover, Ladder::Beep),
            pow_searches(&nb.prover, Ladder::Beep),
        );
        assert_eq!(b.claim.len() + 1, a.claim.len());
        assert_eq!((&b.fold, &b.consistency, &b.queries), (&a.fold, &a.consistency, &a.queries));

        // On the small ladder: the transcript with no binding at level 0.
        let base = fixture(2);
        let fx = fixture_with(2, |mut b| {
            b.prover.ood_samples[0] = 0;
            b.verifier.ood_samples[0] = 0;
            b
        });
        assert!(verifies(&fx, &fx.proof, fx.target));
        // The fixture has two binding samples per level, drawn in one message.
        assert_eq!(fx.proof.ood_values.len() + 2, base.proof.ood_values.len());
        assert_eq!(
            fx.proof.claim_batch_grinding_nonces.len() + 1,
            base.proof.claim_batch_grinding_nonces.len()
        );
        assert!(!verifies(&base, &fx.proof, fx.target));
    }

    /// The split configurations of the bench at the rates that Flock does
    /// not ship: `derive_profile_ladder_at_rate` is Flock's derivation at
    /// the rate of the profile, and at 1/8 and 1/16 it gives a ladder that
    /// climbs two rate steps per level, with no fold grinding and 16 bits of
    /// query grinding, as `slim` does.
    #[test]
    fn split_ladders_at_other_rates() {
        use crate::pcs::ligerito::LigeritoSecurityConfig;
        for m in [29usize, 31] {
            let own = LigeritoSecurityConfig::derive_profile(m, LigeritoProfile::Slim).expect("slim");
            let same = LigeritoSecurityConfig::derive_profile_ladder_at_rate(
                m,
                LigeritoProfile::Slim,
                3,
                2,
                2,
            )
            .expect("slim at its own rate");
            assert_eq!(
                own.to_toml_string().expect("toml"),
                same.to_toml_string().expect("toml")
            );
            for rate in [3usize, 4] {
                let sec = LigeritoSecurityConfig::derive_profile_ladder_at_rate(
                    m,
                    LigeritoProfile::Slim,
                    3,
                    2,
                    rate,
                )
                .expect("derived");
                let (p, v) = sec.to_prover_verifier_configs().expect("configs");
                assert_eq!(p.log_inv_rates[0], rate);
                assert!(p.log_inv_rates.windows(2).all(|w| w[1] == w[0] + 2));
                assert!(p.fold_grinding_bits.iter().all(|&b| b == 0));
                assert!(p.grinding_bits.iter().all(|&b| b == 16));
                assert_eq!(p.queries, v.queries);
                assert_eq!(p.initial_k, own.initial_k);
                p.validate_stratified().expect("stratified");
            }
        }
    }

    #[test]
    fn affine_ladder_at_the_default_slack() {
        let (log_n, initial_k, rates, fold) = (24usize, 6usize, [1usize, 3, 5, 7], [4usize, 5, 5, 5]);
        let split = prover_config_for(log_n, initial_k, LigeritoProfile::Fast).expect("split");
        let (p0, v0) = affine_ladder(&split, log_n, &rates, &fold);
        let (p1, v1) = affine_ladder_at(&split, log_n, &rates, &[0.02; 4], &fold).expect("ladder");
        assert_eq!(p0.queries, p1.queries);
        assert_eq!(p0.claim_batch_grinding_bits, p1.claim_batch_grinding_bits);
        assert_eq!(p0.consistency_batch_grinding_bits, p1.consistency_batch_grinding_bits);
        assert_eq!(p0.stratified, p1.stratified);
        assert_eq!(v0.queries, v1.queries);
        assert_eq!(v0.stratified, v1.stratified);
        let etas = [0.001, 0.002, 0.005, 0.02];
        let (p2, v2) = affine_ladder_at(&split, log_n, &rates, &etas, &[8, 8, 7, 5]).expect("ladder");
        assert!(p2.queries[0] < p0.queries[0] && p2.queries[3] == p0.queries[3]);
        assert_eq!(p2.queries, v2.queries);
        assert_eq!(p2.stratified, v2.stratified);
        assert_eq!(p2.claim_batch_grinding_bits, v2.claim_batch_grinding_bits);
        p2.validate_stratified().expect("stratified");
    }
}
