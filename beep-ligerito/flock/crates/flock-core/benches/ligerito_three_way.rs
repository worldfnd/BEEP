// [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: the bench of the
// comparison of the BEEP paper (`typst/deep+.typ` of the repository `random-domain-ligerito`).
// Not part of upstream Flock. Research, unaudited. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-13, after an independent review: the affine ladder at a
// slack per level (`affine_eta=`, `affine_fold=`), the list of proof-of-work searches of every
// variant checked against the nonces of its proofs, a calibration of the searches per bit count,
// and the Merkle parts of every level]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: smaller rates (`l0_rate=`: Flock's
// derivation of the profile at another rate of L0, for the rates that Flock does not ship), and the variant
// `beepaff-<eta>` (`beepaff=`: a BEEP ladder whose fold challenges are ground for the error of the affine fold,
// an accounting experiment)]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: resource counters of every prover run
// (`benches/support/run_counters.rs`: CPU time and its part on performance cores, cycles, instructions, page
// faults, context switches), to understand timings that are not what we expect]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: `beep-<eta>` is now the BEEP ladder with no
// binding sample on the first commitment, proved with one pass per fold round; `beepb-<eta>` keeps that sample and
// `beepref-<eta>` is the reference prover (three passes per round), to record what each change saves]
// [AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: `beep-<eta>` grinds its fold and batching
// squeezes against a threshold (`BeepConfig::with_exact_grinding`); `beepbits-<eta>` keeps the bits; the searches
// of every variant are printed with their expected work, and every distinct search is timed on its own]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("bring the affine version to a similar level
// of optimization as BEEP", "remove the sample on the first commitment for the affine version"): the affine ladders
// with the prover of `affine_fast.rs` (`afast`, `afast-small`: the same proofs as `affine`, `affine-small`), and with
// no out-of-domain sample on the first commitment (`anf`, `anf-small` with that prover, `anfref`, `anfref-small`
// with Flock's)]
// [AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("run experiments for 100 bits of security,
// same parameter regimes as for 128 bits"): `bits=100` builds the affine and BEEP ladders for a round-by-round
// target of 100 bits, on Flock's profiles `fast100` and `slim100` (`profile=`); the target is printed with the
// context and with every configuration. With the default `bits=128` nothing changes]
// [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request (a minimal Experiments section, with Ligerito
// and BEEP-Ligerito "at 100 bits of security over a field of size GF(2^128)"): the variant `mca-<eta>`
// (`variants=..,mca`, `mca_eta=`, default 0.02), which is `beep::mca_ladder_at`: the ladder with no points per fold
// round and with its fold challenges ground for Flock's MCA bound over GF(2^128). The other variants are unchanged]

//! Three openings of the same Ligerito commitment, on the plain native path
//! of `benches/affine_vs_f256.rs` (flock-prover): the same witness, dense eq
//! basis and L0 commitment (LSB lanes) go through
//!
//! * `split`: Flock's Ligerito at 128 bits, with fold challenges in F256
//!   and the coordinate split (`recursive_prover_with_basis`);
//! * `affine`: the affine F128 ladder (`pcs::ligerito::affine`), at the
//!   slack 0.02 of Flock's `Fast` profile;
//! * `affine-small`: the same prover and verifier on a ladder with a slack
//!   per level (`affine_eta=`), which must come with the fold grinding of a
//!   certificate at that slack (`affine_fold=`);
//! * `beep-<eta>`: the BEEP ladder (`pcs::ligerito::beep`) at slack `eta`,
//!   with no binding sample on the first commitment
//!   (`BeepConfig::without_first_binding`) and with proofs of work against a
//!   threshold (`BeepConfig::with_exact_grinding`).
//!
//! Runs are interleaved; each prover gets its own clones outside the timer,
//! and each repetition its own transcript domain, so that the proof-of-work
//! searches of the repetitions are independent samples. One `RESULT {json}`
//! line is printed per variant, and one `CONTEXT {json}` line for the run.
//!
//! Arguments (all optional, `key=value`):
//!   `log_n=20`          words of the witness, as a power of two
//!   `profile=fast`      Flock profile of the split config: `fast` or `slim`
//!                       (128 bits), `fast100` or `slim100` (their 100-bit
//!                       cost points: the query term at 100 bits)
//!   `bits=128`          round-by-round target of the affine and BEEP
//!                       ladders: 128, or 100 with a 100-bit profile
//!   `l0_rate=3`         log inverse rate of L0. Flock ships `fast` at 1 and
//!                       `slim` at 2; at another rate the split config is
//!                       Flock's derivation of `profile` at that rate
//!                       (`derive_profile_ladder_at_rate`, a local addition)
//!   `rates=1,3,5`       log inverse rates of the affine and BEEP ladders
//!   `fold=4,5,5`        fold grinding of the affine ladder, per level
//!                       (from `scripts/affine_fold_params.py`)
//!   `eta=0.02,0.005`    one BEEP variant per value (the same slack at
//!                       every level)
//!   `affine_eta=0.001,0.002,0.005,0.02`  slack per level of `affine-small`
//!   `affine_fold=8,8,7,5`  its fold grinding per level (from
//!                       `7-beep-ligerito/scripts/beep_params.py --affine-ladder`)
//!   `variants=split,affine,beep`  (add `affine-small`, and `control` for the scalar fold
//!                       alone: each BEEP ladder with no points per fold
//!                       round, a timing control and not a sound
//!                       configuration)
//!   `beepaff=0.02:7,7,7,7/0.001:12,13,15,13`  with `variants=..,beepaff`:
//!                       for each BEEP ladder, the same ladder with these
//!                       fold grinding bits per level (`beepaff-<eta>`).
//!                       An accounting experiment: the fold challenge is
//!                       charged the error of the affine fold where that
//!                       has a certificate (`beep_params.py
//!                       --beep-affine-charge`). Not a sound configuration
//!                       of this protocol, whose fold is not the affine one
//!   `variants=..,mca`  "Ligerito over GF(2^128)" (`mca-<eta>`, at the slacks of
//!                       `mca_eta=`, default 0.02): the same ladder with no points
//!                       per fold round, Flock's binding sample on the first
//!                       commitment, and fold challenges ground for Flock's MCA
//!                       bound over `F128` (`beep::mca_ladder_at`)
//!   `variants=..,beepb`  each BEEP ladder with the binding sample that
//!                       Flock's ladders draw on the first commitment
//!                       (`beepb-<eta>`): what `beep-<eta>` was before
//!   `variants=..,beepref`  each `beep-<eta>` with the reference prover
//!                       (`prove_beep_reference_timed`: three passes per fold
//!                       round, claims added to the dense weight). The same
//!                       proofs, more slowly
//!   `variants=..,beepold`  each BEEP ladder as it was before these changes
//!                       (`beepold-<eta>`): the binding sample on the first
//!                       commitment, the reference prover, and proofs of
//!                       work in bits
//!   `variants=..,beepbits`  each `beep-<eta>` with proofs of work in bits
//!                       (`beepbits-<eta>`), as before the thresholds
//!   `variants=..,afast,afast-small`  the ladders of `affine` and of
//!                       `affine-small` with the prover of
//!                       `pcs::ligerito::affine_fast` (one pass per fold
//!                       round). The same proofs, which the bench checks
//!   `variants=..,anf,anf-small`  the same two ladders with no out-of-domain
//!                       sample on the first commitment
//!                       (`affine_fast::without_first_sample`), with that
//!                       prover; `anfref`, `anfref-small`: with Flock's prover
//!   `fold_nf=7,5,5,5`   the fold grinding of `anf` (the first level carries
//!                       the list; the other levels are those of `fold=`)
//!   `affine_fold_nf=11,8,7,5`  the same for `anf-small` (both from
//!                       `beep_params.py --affine-ladder`)
//!   `reps=5`            timed repetitions (after one warm-up)
//!   `check`             build the configurations, print them and exit
//!
//! With `FLOCK_NO_GRIND=1` in the environment no proof of work is done (the
//! knob of flock-transcript): proofs do not verify, so verification is
//! skipped, and the times are those of the provers without grinding.

use std::{env, time::Instant};

use flock_core::{
    challenger::{Challenger, FsChallenger},
    field::F128,
    init_perf_thread_pool,
    lincheck::build_eq_table,
    ntt::additive_ntt_f128::AdditiveNttF128,
    pcs::ligerito::{
        LigeritoProfile, LigeritoSecurityConfig, ProverConfig, VerifierConfig,
        affine::{affine_ladder, prove_affine, verify_affine},
        affine_fast::{prove_affine_fast_timed, without_first_sample},
        beep::{
            BeepConfig, Grind, Ladder, LevelBytes, PowGrinds, ProveTimings, SizeBreakdown,
            TARGET_BITS, affine_ladder_target, affine_level_bytes, affine_size_breakdown, beep_ladder_at,
            mca_ladder_at, pow_searches, prove_beep_reference_timed, prove_beep_timed, split_level_bytes,
            split_size_breakdown, verify_beep, verify_split_eq_point,
        },
        embedded_initial_k, ligero_commit, prover_config_for, recursive_prover_with_basis,
        verifier_config_for,
    },
};
use serde_json::{Value, json};

#[path = "support/run_counters.rs"]
mod run_counters;
use run_counters::{Snapshot, Used};

fn arg(key: &str) -> Option<String> {
    env::args().find_map(|a| a.strip_prefix(key).map(str::to_owned))
}

fn list<T: std::str::FromStr>(key: &str) -> Option<Vec<T>>
where
    T::Err: std::fmt::Debug,
{
    arg(key).map(|v| v.split(',').map(|x| x.parse::<T>().expect(key)).collect())
}

fn rand_vec(len: usize, seed: u64) -> Vec<F128> {
    let mut s = seed | 1;
    (0..len)
        .map(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            let lo = s;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            F128::new(lo, s)
        })
        .collect()
}

fn median(v: &[f64]) -> f64 {
    let mut v = v.to_vec();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n == 0 {
        f64::NAN
    } else if n % 2 == 1 {
        v[n / 2]
    } else {
        0.5 * (v[n / 2 - 1] + v[n / 2])
    }
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1e3
}

/// Hashes per millisecond of the proof-of-work search, measured on searches
/// of `bits` bits: the least passing nonce is returned, so a search tried
/// `nonce + 1` hashes (up to the block that the parallel search cancels).
/// The search is the fused search and squeeze that every prover of this
/// bench calls (`grind_pow_and_sample_f128`), on the same kind of
/// transcript. Returns `(hashes per ms, hashes, ms)` over the `searches`
/// searches.
fn pow_rate(bits: u32, searches: usize) -> (f64, f64, f64) {
    let mut ch = FsChallenger::new(b"pow-calibration");
    let (mut hashes, mut time) = (0f64, 0f64);
    for i in 0..searches {
        ch.observe_f128(F128::new(i as u64, bits as u64));
        let t = Instant::now();
        let (nonce, _) = ch.grind_pow_and_sample_f128(bits);
        time += ms(t);
        hashes += (nonce + 1) as f64;
    }
    (hashes / time, hashes, time)
}

/// The searches of a threshold proof of work, like [`pow_rate`]: `(hashes,
/// ms)` over `searches` searches below `target`.
fn pow_rate_below(target: u64, searches: usize) -> (f64, f64) {
    let mut ch = FsChallenger::new(b"pow-calibration-below");
    let (mut hashes, mut time) = (0f64, 0f64);
    for i in 0..searches {
        ch.observe_f128(F128::new(i as u64, target));
        let t = Instant::now();
        let (nonce, _) = ch.grind_pow_below_and_sample_f128(target);
        time += ms(t);
        hashes += (nonce + 1) as f64;
    }
    (hashes, time)
}

fn grind_json(g: Grind) -> Value {
    match g {
        Grind::Bits(bits) => json!({ "bits": bits, "work": g.work() }),
        Grind::Below(target) => json!({ "target": target, "work": g.work() }),
    }
}

fn grinds_json(g: &PowGrinds) -> Value {
    let list = |v: &[Grind]| v.iter().map(|&x| grind_json(x)).collect::<Vec<_>>();
    json!({
        "fold": list(&g.fold),
        "claim": list(&g.claim),
        "consistency": list(&g.consistency),
        "queries": list(&g.queries),
    })
}

/// The grinds of a BEEP ladder per level, for its configuration.
fn beep_grinds_json(b: &BeepConfig) -> Value {
    let list = |v: &[Grind]| v.iter().map(|&x| grind_json(x)).collect::<Vec<_>>();
    json!({ "fold": list(&b.fold), "claim": list(&b.claim), "consistency": list(&b.consistency) })
}

fn config_json(c: &ProverConfig) -> Value {
    json!({
        "initial_k": c.initial_k,
        "recursive_ks": c.recursive_ks,
        "recursive_log_msg_cols": c.recursive_log_msg_cols,
        "log_inv_rates": c.log_inv_rates,
        "queries": c.queries,
        "query_grinding_bits": c.grinding_bits,
        "fold_grinding_bits": c.fold_grinding_bits,
        "claim_batch_grinding_bits": c.claim_batch_grinding_bits,
        "consistency_batch_grinding_bits": c.consistency_batch_grinding_bits,
        "ood_samples": c.ood_samples,
    })
}

struct Run {
    prove_ms: f64,
    /// What the process used during the prover run (not the verifications).
    used: Used,
    proof_bytes: usize,
    breakdown: SizeBreakdown,
    levels: Vec<LevelBytes>,
    /// Nonces of the proof: fold, claim batching, consistency batching, queries.
    nonces: [usize; 4],
    hashes: f64,
    verify_ms: Option<f64>,
    timings: Option<ProveTimings>,
}

/// The nonces that a proof must have for the searches of its ladder: one per
/// search, except that the split ladder has no fold nonce (no fold grinding).
fn check_nonces(name: &str, searches: &PowGrinds, nonces: [usize; 4]) {
    let expected = [
        searches.fold.len(),
        searches.claim.len(),
        searches.consistency.len(),
        searches.queries.len(),
    ];
    assert_eq!(nonces, expected, "{name}: nonces of the proof against the list of searches");
}

fn main() {
    let threads = init_perf_thread_pool();
    let log_n: usize = arg("log_n=").map_or(20, |v| v.parse().expect("log_n"));
    let profile = match arg("profile=").as_deref() {
        None | Some("fast") => LigeritoProfile::Fast,
        Some("slim") => LigeritoProfile::Slim,
        Some("fast100") => LigeritoProfile::Fast100,
        Some("slim100") => LigeritoProfile::Slim100,
        Some(other) => panic!("profile must be fast, slim, fast100 or slim100 (got {other})"),
    };
    // The round-by-round target of the affine and BEEP ladders. The split
    // config is Flock's: at 100 bits its profiles keep 128 bits for every
    // term but the queries.
    let target_bits: f64 = match arg("bits=").as_deref() {
        None | Some("128") => TARGET_BITS,
        Some("100") => 100.0,
        Some(other) => panic!("bits must be 128 or 100 (got {other})"),
    };
    let hundred = matches!(profile, LigeritoProfile::Fast100 | LigeritoProfile::Slim100);
    assert_eq!(
        hundred,
        target_bits == 100.0,
        "bits=100 goes with profile=fast100 or slim100, and bits=128 with fast or slim"
    );
    let reps: usize = arg("reps=").map_or(5, |v| v.parse().expect("reps"));
    let variants = arg("variants=").unwrap_or_else(|| "split,affine,beep".into());
    let want = |name: &str| variants.split(',').any(|v| v == name);
    let no_grind = env::var_os("FLOCK_NO_GRIND").is_some();
    let check_only = env::args().any(|a| a == "check");

    let m = log_n + 7;
    // The split config: Flock's embedded one for the profile, or, at a rate
    // of L0 that Flock does not ship, Flock's derivation of the profile (3
    // folds per level, the rate gain of `derive_profile`) at that rate.
    let l0_rate: Option<usize> = arg("l0_rate=").map(|v| v.parse().expect("l0_rate"));
    let derived = l0_rate.is_some_and(|r| r != profile.log_inv_rate());
    let (split, split_v, initial_k) = if derived {
        let rate = l0_rate.expect("l0_rate");
        // As `derive_profile`: `slim` climbs the rate +2 per level, the
        // other profiles (`slim100` among them) +1.
        let rate_gain = if profile == LigeritoProfile::Slim { 2 } else { 1 };
        let sec =
            LigeritoSecurityConfig::derive_profile_ladder_at_rate(m, profile, 3, rate_gain, rate)
                .unwrap_or_else(|e| panic!("split config at rate 2^-{rate}: {e}"));
        let (p, v) = sec.to_prover_verifier_configs().expect("derived split configs");
        (p, v, sec.initial_k)
    } else {
        let initial_k = embedded_initial_k(m, profile)
            .unwrap_or_else(|| panic!("no embedded config for m = {m}"));
        (
            prover_config_for(log_n, initial_k, profile).expect("split config"),
            verifier_config_for(log_n, initial_k, profile).expect("split verifier config"),
            initial_k,
        )
    };
    let rates: Vec<usize> = list("rates=").expect("rates=.. (the ladder of affine and BEEP)");
    let etas: Vec<f64> = list("eta=").unwrap_or_else(|| vec![0.02]);
    // The affine family: `affine` (Flock's ladder at slack 0.02) and
    // `affine-small` (a slack per level), each with Flock's prover, with the
    // prover of `affine_fast.rs` (`afast*`), and with no sample on the first
    // commitment (`anf*` with that prover, `anfref*` with Flock's).
    let any = |names: &[&str]| names.iter().any(|n| want(n));
    let affine = any(&["affine", "afast", "anf", "anfref"]).then(|| {
        let fold: Vec<usize> = list("fold=").expect("fold=.. (affine fold grinding)");
        if target_bits == TARGET_BITS {
            affine_ladder(&split, log_n, &rates, &fold)
        } else {
            // Flock's `affine_ladder` is for 128 bits: its rules at the same
            // slack 0.02, for the target.
            affine_ladder_target(&split, log_n, &rates, &vec![0.02; rates.len()], &fold, target_bits)
                .unwrap_or_else(|e| panic!("affine ladder at {target_bits} bits: {e}"))
        }
    });
    let affine_etas: Option<Vec<f64>> = list("affine_eta=");
    let affine_small: Option<(ProverConfig, VerifierConfig)> =
        any(&["affine-small", "afast-small", "anf-small", "anfref-small"]).then(|| {
            let etas = affine_etas.clone().expect("affine_eta=.. (slack per level)");
            let fold: Vec<usize> = list("affine_fold=").expect("affine_fold=.. (fold grinding)");
            affine_ladder_target(&split, log_n, &rates, &etas, &fold, target_bits)
                .unwrap_or_else(|e| panic!("affine ladder at {etas:?}: {e}"))
        });
    // No sample on the first commitment: the fold grinding of the first
    // level comes with the list (`fold_nf=`, `affine_fold_nf=`), and the
    // other levels must be those of the ladder.
    let no_first = |ladder: &(ProverConfig, VerifierConfig), key: &str| {
        let fold: Vec<usize> = list(key).unwrap_or_else(|| panic!("{key}.. (fold grinding with no first sample)"));
        assert_eq!(fold[1..], ladder.0.fold_grinding_bits[1..], "{key}: only the first level changes");
        assert!(fold[0] >= ladder.0.fold_grinding_bits[0], "{key}: the first level carries the list");
        without_first_sample(ladder, fold[0])
    };
    let affine_nf = any(&["anf", "anfref"]).then(|| no_first(affine.as_ref().expect("affine ladder"), "fold_nf="));
    let affine_small_nf = any(&["anf-small", "anfref-small"])
        .then(|| no_first(affine_small.as_ref().expect("affine ladder"), "affine_fold_nf="));
    // (name, ladder, slack of its levels, with the prover of `affine_fast.rs`?)
    // of every variant of the family that runs.
    let default_etas = vec![0.02; rates.len()];
    let mut affine_family: Vec<(&str, &(ProverConfig, VerifierConfig), Vec<f64>, bool)> = Vec::new();
    for (name, ladder, small, fast) in [
        ("affine", affine.as_ref(), false, false),
        ("affine-small", affine_small.as_ref(), true, false),
        ("afast", affine.as_ref(), false, true),
        ("afast-small", affine_small.as_ref(), true, true),
        ("anf", affine_nf.as_ref(), false, true),
        ("anf-small", affine_small_nf.as_ref(), true, true),
        ("anfref", affine_nf.as_ref(), false, false),
        ("anfref-small", affine_small_nf.as_ref(), true, false),
    ] {
        if want(name) {
            let etas = if small {
                affine_etas.clone().expect("affine_eta")
            } else {
                default_etas.clone()
            };
            affine_family.push((name, ladder.expect("ladder of the variant"), etas, fast));
        }
    }
    // The BEEP ladders as `beep_ladder` builds them, with Flock's binding
    // sample on the first commitment (`beepb-<eta>`), and without it
    // (`beep-<eta>`, the variant of the comparison).
    let with_binding: Vec<(f64, BeepConfig)> = if want("beep") {
        etas.iter()
            .map(|&eta| {
                let cfg = beep_ladder_at(&split, log_n, &rates, &vec![eta; rates.len()], target_bits)
                    .unwrap_or_else(|e| panic!("BEEP ladder at eta = {eta}: {e}"));
                (eta, cfg)
            })
            .collect()
    } else {
        Vec::new()
    };
    // Without the binding sample, with proofs of work in bits (`beepbits-<eta>`)
    // and against thresholds (`beep-<eta>`, the variant of the comparison).
    let in_bits: Vec<(f64, BeepConfig)> = with_binding
        .iter()
        .map(|(eta, cfg)| {
            let c = cfg
                .without_first_binding()
                .unwrap_or_else(|e| panic!("BEEP ladder at eta = {eta}: {e}"));
            (*eta, c)
        })
        .collect();
    let beeps: Vec<(f64, BeepConfig)> = in_bits
        .iter()
        .map(|(eta, cfg)| (*eta, cfg.with_exact_grinding()))
        .collect();

    // Timing controls: each BEEP ladder with no points per fold round, i.e.
    // the scalar fold alone. Not a sound configuration.
    let controls: Vec<(f64, BeepConfig)> = if want("control") {
        beeps
            .iter()
            .map(|(eta, cfg)| {
                let mut c = cfg.clone();
                c.samples.iter_mut().for_each(|m| *m = 0);
                (*eta, c)
            })
            .collect()
    } else {
        Vec::new()
    };

    // `mca-<eta>`: "Ligerito over GF(2^128)", i.e. the ladder with no points
    // per fold round, with Flock's binding sample on the first commitment,
    // and with its fold challenges ground for Flock's MCA bound over F128
    // (`beep::mca_ladder_at`). Proofs of work against thresholds, as `beep`.
    let mca_etas: Vec<f64> = list("mca_eta=").unwrap_or_else(|| vec![0.02]);
    let mcas: Vec<(f64, BeepConfig)> = if want("mca") {
        mca_etas
            .iter()
            .map(|&eta| {
                let cfg = mca_ladder_at(&split, log_n, &rates, &vec![eta; rates.len()], target_bits)
                    .unwrap_or_else(|e| panic!("MCA ladder at eta = {eta}: {e}"));
                (eta, cfg.with_exact_grinding())
            })
            .collect()
    } else {
        Vec::new()
    };

    // Each BEEP ladder with the fold grinding of `beepaff=` (module docs).
    let beepaff_bits: Vec<(f64, Vec<usize>)> = arg("beepaff=")
        .map(|v| {
            v.split('/')
                .map(|part| {
                    let (eta, bits) = part.split_once(':').expect("beepaff=eta:bits,..[/eta:bits,..]");
                    (
                        eta.parse::<f64>().expect("beepaff eta"),
                        bits.split(',').map(|x| x.parse::<usize>().expect("beepaff bits")).collect(),
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    let hybrids: Vec<(f64, BeepConfig)> = if want("beepaff") {
        beeps
            .iter()
            .map(|(eta, cfg)| {
                let bits = &beepaff_bits
                    .iter()
                    .find(|(e, _)| e == eta)
                    .unwrap_or_else(|| panic!("beepaff= has no entry for eta = {eta}"))
                    .1;
                let c = cfg
                    .with_fold_grinding(bits)
                    .unwrap_or_else(|e| panic!("beepaff at eta = {eta}: {e}"));
                (*eta, c)
            })
            .collect()
    } else {
        Vec::new()
    };

    let keep_binding = want("beepb");
    let reference = want("beepref");
    let old = want("beepold");
    let bits_only = want("beepbits");
    // `beepb-<eta>`: the binding sample, and thresholds as `beep-<eta>`.
    let bound: Vec<(f64, BeepConfig)> = with_binding
        .iter()
        .map(|(eta, cfg)| (*eta, cfg.with_exact_grinding()))
        .collect();

    let mut configs = json!({ "split": config_json(&split) });
    for (name, ladder, etas, _) in &affine_family {
        let mut c = config_json(&ladder.0);
        c["etas"] = json!(etas);
        configs[*name] = c;
    }
    // A BEEP ladder: Flock's fields, the points, the analysis of its levels,
    // and how it grinds (the bits of Flock's fields do not say it when the
    // ladder grinds against thresholds).
    let beep_json = |b: &BeepConfig| -> Value {
        let mut c = config_json(&b.prover);
        c["samples"] = json!(b.samples);
        c["levels"] = serde_json::to_value(&b.levels).expect("levels");
        c["min_bits"] = json!(b.min_bits());
        c["grinds"] = beep_grinds_json(b);
        c
    };
    for (eta, b) in &beeps {
        configs[format!("beep-{eta}")] = beep_json(b);
    }
    for (eta, b) in &controls {
        let mut c = config_json(&b.prover);
        c["samples"] = json!(b.samples);
        c["grinds"] = beep_grinds_json(b);
        configs[format!("control-{eta}")] = c;
    }
    for (eta, b) in &hybrids {
        // `levels`: the analysis of the BEEP ladder that this variant is derived from.
        configs[format!("beepaff-{eta}")] = beep_json(b);
    }
    for (eta, b) in &mcas {
        configs[format!("mca-{eta}")] = beep_json(b);
    }
    if keep_binding {
        for (eta, b) in &bound {
            configs[format!("beepb-{eta}")] = beep_json(b);
        }
    }
    if reference {
        for (eta, _) in &beeps {
            configs[format!("beepref-{eta}")] = configs[format!("beep-{eta}")].clone();
        }
    }
    if old {
        for (eta, b) in &with_binding {
            configs[format!("beepold-{eta}")] = beep_json(b);
        }
    }
    if bits_only {
        for (eta, b) in &in_bits {
            configs[format!("beepbits-{eta}")] = beep_json(b);
        }
    }
    // The target of every ladder: that of the affine and BEEP ladders, and
    // for the split config the target of its query term (the profile's).
    if let Some(map) = configs.as_object_mut() {
        for (name, c) in map.iter_mut() {
            c["target_bits"] = if name == "split" {
                json!(if hundred { 100.0 } else { TARGET_BITS })
            } else {
                json!(target_bits)
            };
        }
    }
    if check_only {
        println!(
            "CHECK {}",
            json!({ "log_n": log_n, "profile": profile.as_str(), "target_bits": target_bits, "configs": configs })
        );
        return;
    }

    // Witness, dense eq basis and L0 commitment, shared by every variant.
    let witness = rand_vec(1 << log_n, 0xA11E);
    let z = rand_vec(log_n, 0x5EED);
    let basis = build_eq_table(&z);
    let target = witness
        .iter()
        .zip(&basis)
        .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
    let log_cols = log_n - initial_k;
    let rate = split.log_inv_rates[0];
    let ntt = AdditiveNttF128::standard(log_cols + rate);
    let commit = || ligero_commit(&witness, log_cols, initial_k, rate, &ntt, split.merkle_hash);
    // One commitment is alive at a time: the previous one is dropped (its
    // table goes back to Flock's buffer pool) before the next is timed, so
    // that a long code (2^24 words at rate 1/16 is a table of 4 GiB) does
    // not take twice its memory. The first commitment is a warm-up.
    let mut l0 = Some(commit());
    let mut commit_ms = Vec::new();
    for _ in 0..reps {
        drop(l0.take());
        let t = Instant::now();
        l0 = Some(commit());
        commit_ms.push(ms(t));
    }
    let l0 = l0.expect("commitment");

    // eq(z) bound at the fold challenges rs: a prefix scalar times eq over the rest.
    let eq_residual = |rs: &[F128], residual_log: usize| {
        let prefix = z
            .iter()
            .zip(rs)
            .fold(F128::ONE, |acc, (&zi, &ri)| acc * (F128::ONE + zi + ri));
        let mut out = build_eq_table(&z[rs.len()..]);
        assert_eq!(out.len(), 1usize << residual_log);
        out.iter_mut().for_each(|v| *v *= prefix);
        out
    };
    let domain = |rep: usize| format!("three-way-{log_n}-{rep}").into_bytes();
    let verify_reps = 5;

    let run_split = |rep: usize| -> Run {
        let (w, b) = (witness.clone(), basis.clone());
        let mut ch = FsChallenger::new(&domain(rep));
        let before = Snapshot::now();
        let t = Instant::now();
        let proof = recursive_prover_with_basis(&split, w, b, target, &l0.mat, &l0.tree, &mut ch);
        let prove_ms = ms(t);
        let used = Snapshot::now().since(&before);
        let cap = l0.cap(split.level_zero_cap_depth()).to_vec();
        let verify_ms = (!no_grind).then(|| {
            let times: Vec<f64> = (0..verify_reps)
                .map(|_| {
                    let mut ch = FsChallenger::new(&domain(rep));
                    let t = Instant::now();
                    let ok =
                        verify_split_eq_point(&split_v, &proof, log_n, target, &cap, &z, &mut ch);
                    let dt = ms(t);
                    assert!(ok, "the split proof must verify");
                    dt
                })
                .collect();
            median(&times)
        });
        let nonces = proof
            .grinding_nonces
            .iter()
            .chain(&proof.fold_grinding_nonces)
            .chain(&proof.claim_batch_grinding_nonces)
            .chain(&proof.consistency_batch_grinding_nonces);
        Run {
            prove_ms,
            used,
            proof_bytes: proof.size_bytes(),
            breakdown: split_size_breakdown(&proof),
            levels: split_level_bytes(&proof),
            nonces: [
                proof.fold_grinding_nonces.len(),
                proof.claim_batch_grinding_nonces.len(),
                proof.consistency_batch_grinding_nonces.len(),
                proof.grinding_nonces.len(),
            ],
            hashes: nonces.map(|&n| (n + 1) as f64).sum(),
            verify_ms,
            timings: None,
        }
    };
    let run_affine = |ladder: &(ProverConfig, VerifierConfig), rep: usize, fast: bool| -> Run {
        let (cfg, cfg_v) = ladder;
        let (w, b) = (witness.clone(), basis.clone());
        let mut ch = FsChallenger::new(&domain(rep));
        let before = Snapshot::now();
        let t = Instant::now();
        let (proof, timings) = if fast {
            let (proof, timings) =
                prove_affine_fast_timed(cfg, w, b, target, &l0.mat, &l0.tree, &mut ch);
            (proof, Some(timings))
        } else {
            (prove_affine(cfg, w, b, target, &l0.mat, &l0.tree, &mut ch), None)
        };
        let prove_ms = ms(t);
        let used = Snapshot::now().since(&before);
        let cap = l0.cap(cfg.level_zero_cap_depth()).to_vec();
        let verify_ms = (!no_grind).then(|| {
            let times: Vec<f64> = (0..verify_reps)
                .map(|_| {
                    let mut ch = FsChallenger::new(&domain(rep));
                    let t = Instant::now();
                    let ok =
                        verify_affine(cfg_v, &proof, log_n, target, &cap, eq_residual, &mut ch);
                    let dt = ms(t);
                    assert!(ok, "the affine proof must verify");
                    dt
                })
                .collect();
            median(&times)
        });
        let nonces = proof
            .grinding_nonces
            .iter()
            .chain(&proof.fold_grinding_nonces)
            .chain(&proof.claim_batch_grinding_nonces)
            .chain(&proof.consistency_batch_grinding_nonces);
        Run {
            prove_ms,
            used,
            proof_bytes: proof.size_bytes(),
            breakdown: affine_size_breakdown(&proof),
            levels: affine_level_bytes(&proof),
            nonces: [
                proof.fold_grinding_nonces.len(),
                proof.claim_batch_grinding_nonces.len(),
                proof.consistency_batch_grinding_nonces.len(),
                proof.grinding_nonces.len(),
            ],
            hashes: nonces.map(|&n| (n + 1) as f64).sum(),
            verify_ms,
            timings,
        }
    };
    let run_beep = |cfg: &BeepConfig, rep: usize, reference: bool| -> Run {
        let (w, b) = (witness.clone(), basis.clone());
        let mut ch = FsChallenger::new(&domain(rep));
        let before = Snapshot::now();
        let t = Instant::now();
        let (proof, timings) = if reference {
            prove_beep_reference_timed(cfg, w, b, target, &l0.mat, &l0.tree, &mut ch)
        } else {
            prove_beep_timed(cfg, w, b, target, &l0.mat, &l0.tree, &mut ch)
        };
        let prove_ms = ms(t);
        let used = Snapshot::now().since(&before);
        let cap = l0.cap(cfg.prover.level_zero_cap_depth()).to_vec();
        let verify_ms = (!no_grind).then(|| {
            let times: Vec<f64> = (0..verify_reps)
                .map(|_| {
                    let mut ch = FsChallenger::new(&domain(rep));
                    let t = Instant::now();
                    let ok = verify_beep(cfg, &proof, log_n, target, &cap, eq_residual, &mut ch);
                    let dt = ms(t);
                    assert!(ok, "the BEEP proof must verify");
                    dt
                })
                .collect();
            median(&times)
        });
        Run {
            prove_ms,
            used,
            proof_bytes: proof.size_bytes(),
            breakdown: proof.size_breakdown(),
            levels: proof.level_bytes(),
            nonces: [
                proof.fold_grinding_nonces.len(),
                proof.claim_batch_grinding_nonces.len(),
                proof.consistency_batch_grinding_nonces.len(),
                proof.grinding_nonces.len(),
            ],
            hashes: proof.nonces().map(|n| (n + 1) as f64).sum(),
            verify_ms,
            timings: Some(timings),
        }
    };

    // One warm-up of every variant (repetition index `reps`), then the
    // timed repetitions, interleaved.
    let mut names: Vec<String> = Vec::new();
    if want("split") {
        names.push("split".into());
    }
    for (name, ..) in &affine_family {
        names.push((*name).into());
    }
    for (eta, _) in &beeps {
        names.push(format!("beep-{eta}"));
    }
    for (eta, _) in &controls {
        names.push(format!("control-{eta}"));
    }
    for (eta, _) in &hybrids {
        names.push(format!("beepaff-{eta}"));
    }
    for (eta, _) in &mcas {
        names.push(format!("mca-{eta}"));
    }
    if keep_binding {
        for (eta, _) in &bound {
            names.push(format!("beepb-{eta}"));
        }
    }
    if bits_only {
        for (eta, _) in &in_bits {
            names.push(format!("beepbits-{eta}"));
        }
    }
    if reference {
        for (eta, _) in &beeps {
            names.push(format!("beepref-{eta}"));
        }
    }
    if old {
        for (eta, _) in &with_binding {
            names.push(format!("beepold-{eta}"));
        }
    }
    let ladder = |name: &str| -> &BeepConfig {
        beeps
            .iter()
            .map(|(eta, cfg)| (format!("beep-{eta}"), cfg))
            .chain(controls.iter().map(|(eta, cfg)| (format!("control-{eta}"), cfg)))
            .chain(hybrids.iter().map(|(eta, cfg)| (format!("beepaff-{eta}"), cfg)))
            .chain(mcas.iter().map(|(eta, cfg)| (format!("mca-{eta}"), cfg)))
            .chain(bound.iter().map(|(eta, cfg)| (format!("beepb-{eta}"), cfg)))
            .chain(in_bits.iter().map(|(eta, cfg)| (format!("beepbits-{eta}"), cfg)))
            .chain(beeps.iter().map(|(eta, cfg)| (format!("beepref-{eta}"), cfg)))
            .chain(with_binding.iter().map(|(eta, cfg)| (format!("beepold-{eta}"), cfg)))
            .find(|(n, _)| n == name)
            .expect("variant")
            .1
    };
    let affine_of = |name: &str| affine_family.iter().find(|(n, ..)| *n == name);
    let run = |name: &str, rep: usize| -> Run {
        if name == "split" {
            return run_split(rep);
        }
        if let Some((_, ladder, _, fast)) = affine_of(name) {
            return run_affine(ladder, rep, *fast);
        }
        run_beep(
            ladder(name),
            rep,
            name.starts_with("beepref-") || name.starts_with("beepold-"),
        )
    };
    // The searches of every variant, and the configuration they come from.
    let searches_of = |name: &str| -> PowGrinds {
        if name == "split" {
            return PowGrinds::from_bits(&pow_searches(&split, Ladder::Split));
        }
        if let Some((_, ladder, ..)) = affine_of(name) {
            return PowGrinds::from_bits(&pow_searches(&ladder.0, Ladder::Affine));
        }
        ladder(name).pow_grinds()
    };
    // The prover of `affine_fast.rs` must write the proof of Flock's prover.
    for (name, ladder, _, fast) in &affine_family {
        if *fast {
            let prove = |fast: bool| {
                let mut ch = FsChallenger::new(&domain(reps));
                let (w, b) = (witness.clone(), basis.clone());
                if fast {
                    prove_affine_fast_timed(&ladder.0, w, b, target, &l0.mat, &l0.tree, &mut ch).0
                } else {
                    prove_affine(&ladder.0, w, b, target, &l0.mat, &l0.tree, &mut ch)
                }
            };
            assert!(prove(true) == prove(false), "{name}: the two provers must write the same proof");
        }
    }
    for name in &names {
        let warm = run(name, reps);
        let searches = searches_of(name);
        if name == "split" {
            // No fold grinding, and no fold nonce in the proof.
            assert_eq!(warm.nonces[0], 0, "split: fold nonces");
            assert!(searches.fold.is_empty());
        }
        check_nonces(name, &searches, warm.nonces);
        let parts = &warm.levels;
        assert_eq!(parts.iter().map(|l| l.leaves).sum::<usize>(), warm.breakdown.opened_rows);
        assert_eq!(parts.iter().map(|l| l.paths).sum::<usize>(), warm.breakdown.merkle_paths);
        assert_eq!(parts.iter().map(|l| l.cap).sum::<usize>(), warm.breakdown.caps);
        assert_eq!(warm.breakdown.total(), warm.proof_bytes);
    }
    let mut runs: Vec<Vec<Run>> = names.iter().map(|_| Vec::new()).collect();
    for rep in 0..reps {
        for (i, name) in names.iter().enumerate() {
            runs[i].push(run(name, rep));
        }
    }

    // Proof-of-work rates: searches above 2^13 expected hashes run on every
    // thread, the others on one (flock-transcript's `search_nonce`).
    let (par_rate, seq_rate) = if no_grind {
        (f64::NAN, f64::NAN)
    } else {
        (pow_rate(20, 24).0, pow_rate(10, 2000).0)
    };
    // The searches of the provers are much shorter than those above, and a
    // parallel search also pays for its dispatch and for the chunks that are
    // in flight when a nonce is found. So every distinct search that some
    // variant makes (a bit count, or a threshold) is also timed on its own:
    // the script that collects the run reads the cost of a search from these.
    let mut distinct: Vec<Grind> = Vec::new();
    for name in &names {
        for g in searches_of(name).all() {
            if g.work() > 0.0 && !distinct.contains(&g) {
                distinct.push(g);
            }
        }
    }
    distinct.sort_by(|a, b| a.work().partial_cmp(&b.work()).expect("work"));
    let calibration: Vec<Value> = if no_grind {
        Vec::new()
    } else {
        distinct
            .iter()
            .map(|&g| {
                // About 2^23 hashes per search kind, and between 128 and 4096 searches.
                let searches = ((23f64.exp2() / g.work()) as usize).clamp(128, 4096);
                let (hashes, time) = match g {
                    Grind::Bits(bits) => {
                        let (_, hashes, time) = pow_rate(bits, searches);
                        (hashes, time)
                    }
                    Grind::Below(target) => pow_rate_below(target, searches),
                };
                let mut entry = grind_json(g);
                entry["searches"] = json!(searches);
                entry["hashes"] = json!(hashes);
                entry["ms"] = json!(time);
                entry
            })
            .collect()
    };

    println!(
        "CONTEXT {}",
        json!({
            "log_n": log_n,
            "profile": profile.as_str(),
            "target_bits": target_bits,
            "initial_k": initial_k,
            "l0_rate": split.log_inv_rates[0],
            "split_derived": derived,
            "threads": threads,
            "reps": reps,
            "no_grind": no_grind,
            "commit_ms_reps": commit_ms,
            "commit_ms": median(&commit_ms),
            "pow_hashes_per_ms_parallel": par_rate,
            "pow_hashes_per_ms_sequential": seq_rate,
            "pow_calibration": calibration,
            "rates": rates,
        })
    );
    for (i, name) in names.iter().enumerate() {
        let rs = &runs[i];
        let prove: Vec<f64> = rs.iter().map(|r| r.prove_ms).collect();
        let verify: Vec<f64> = rs.iter().filter_map(|r| r.verify_ms).collect();
        let hashes: Vec<f64> = rs.iter().map(|r| r.hashes).collect();
        let bytes: Vec<f64> = rs.iter().map(|r| r.proof_bytes as f64).collect();
        let searches = searches_of(name);
        for r in rs {
            check_nonces(name, &searches, r.nonces);
        }
        let mut out = json!({
            "variant": name,
            "log_n": log_n,
            "profile": profile.as_str(),
            "no_grind": no_grind,
            "prove_ms_reps": prove,
            "prove_ms": median(&prove),
            "verify_ms": if verify.is_empty() { Value::Null } else { json!(median(&verify)) },
            "proof_bytes_reps": bytes,
            "proof_bytes": median(&bytes),
            "breakdown": serde_json::to_value(rs[0].breakdown).expect("breakdown"),
            "breakdown_levels": serde_json::to_value(&rs[0].levels).expect("levels"),
            "pow_grinds": grinds_json(&searches),
            "pow_expected_hashes": searches.expected_hashes(),
            "pow_hashes_reps": hashes,
            "config": configs[name.as_str()].clone(),
            // What the process used during the prover runs (null if the
            // system does not report it).
            "counters": run_counters::to_json(
                &rs.iter().map(|r| r.used).collect::<Vec<_>>(),
                &prove,
            ),
        });
        if let Some(first) = rs[0].timings {
            let phase = |f: fn(&ProveTimings) -> f64| {
                median(&rs.iter().map(|r| f(r.timings.as_ref().expect("timings"))).collect::<Vec<_>>())
            };
            let _ = first;
            out["timings_ms"] = json!({
                "fold_answers": phase(|t| t.fold_answers_ms),
                "folds": phase(|t| t.folds_ms),
                "fold_grinding": phase(|t| t.fold_grinding_ms),
                "other_grinding": phase(|t| t.other_grinding_ms),
                "ood": phase(|t| t.ood_ms),
                "commits": phase(|t| t.commits_ms),
                "opens": phase(|t| t.opens_ms),
                "induce": phase(|t| t.induce_ms),
                "total": phase(|t| t.total_ms),
            });
        }
        println!("RESULT {out}");
    }
}
