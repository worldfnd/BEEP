#!/usr/bin/env python3
"""The tables and the numbers of the section "Instantiation and experiments" of the BEEP paper.

[AI-drafted (claude-fable-5-2), 2026-11-16, at the author's request ("Let's write the instantiation and
experiment section. I want something minimal that fits in two pages": a comparison of Ligerito and
BEEP-Ligerito for 2^15 to 2^23 words at 100 bits over GF(2^128), the same at 128 bits, and a table with the
error bounds of the first two rounds of the BEEP IOR and the number of queries, with the fold round of
Ligerito next to them); research, unaudited; please review]

    python3 scripts/minimal_tables.py            (from the folder `paper`; writes tables/minimal.json)
    python3 scripts/minimal_tables.py --print    (also prints every table and every number)
    python3 scripts/minimal_tables.py --results <results.json> --out <file>    (another run, e.g. a smoke run;
                                                 with --allow-battery it accepts processes that ran on battery)
    python3 scripts/minimal_tables.py --readme   (also prints the three tables as Markdown, for
                                                 beep-ligerito/README.md)
    python3 scripts/minimal_tables.py --compare <results.json>    (a second run of the same cells: same sizes
                                                 and configurations, and the ratio of the prover times; by
                                                 default the runs OTHER_RUNS)

It reads the run `beep-ligerito/bench_results/three-way-<RUN>/results.json` (written by
`beep-ligerito/scripts/collect.py` from the cells of `beep-ligerito/scripts/cells_minimal.txt`) and imports
`beep-ligerito/scripts/beep_params.py` for the exact arithmetic. No number of the section is typed by hand:
the section reads `tables/minimal.json` through `num("key")` and `exptable(.., "name")`.

What it rechecks before it writes anything (a failure stops it; a WARNING is printed and written to the file):

  * every BEEP level of the run, in exact integer arithmetic (`beep_params.check_level`, `check_grinds`): the
    agreement, the list size, the points and the threshold, the fold grinding, the queries, the batching, the
    binding, and every proof of work with a threshold;
  * every level of the baseline "Ligerito over GF(2^128)" (`mca-<eta>`): its fold numerator against Flock's
    formula for a fold under MCA (recomputed here), the proof of work of its fold challenges, its queries,
    its binding samples and its batching;
  * that every process ended with status ok, on which power source the processes ran (the number
    `run:power`, which the section prints; a run on battery is only accepted with ALLOW_BATTERY), and which
    processes had part of their memory compressed;
  * how stable the rows of the two measured tables are (`stability`): a row is reported as disturbed if one
    of its repetitions without proofs of work takes more than SPREAD times their median, or if the time
    measured with proofs of work differs from "prove" by more than RESIDUAL;
  * that the two baselines of the run (`mcanf`, `mca`) differ in the sample on the first commitment only,
    and that the baseline has the ladder of BEEP-Ligerito at the same slack;
  * that the earlier runs of the same cells (OTHER_RUNS, or `--compare`) have the same proof sizes and
    configurations for the rows that they share with the run, and how far their prover times are
    (`other:<run>:prove-ratio-*`).

Rounding. Bits of security are rounded down. In a range "a to b" the lower end is rounded down and the upper
end up, so that every value of the range lies between the two numbers that are printed.

Standard library only; runs on Python 3.9.
"""
import json
import sys
from fractions import Fraction
from math import ceil, floor, log2, sqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
BEEP_LIGERITO = PAPER.parent / "beep-ligerito"
sys.path.insert(0, str(BEEP_LIGERITO / "scripts"))
import beep_params as bp  # noqa: E402

# The runs of record, November 16, 2026, on AC power, through the gate, with the idle check before every cell:
# RUN (`-ac3`, 15:05 on) for the cells at 100 bits and RUN_128 (`-ac2`, 13:55 on) for the cells at 128 bits.
# The four runs of that day are second measurements of each other's rows of Ligerito (Flock) and of
# BEEP-Ligerito (OTHER_RUNS, or `--compare`). In `-ac2` the baselines `mca` and `mcanf` ground every fold round
# of a level for its first round (in `-ac3`, each round for its own error); `-ac` (13:37 on) has no `mcanf`;
# `-battery` (12:29 to 13:35) has no `mcanf`, and its first 10 processes ran on battery with little unused
# memory, the other 26 on AC power.
RUN = "three-way-minimal-20261116-ac3"
# The cells at 128 bits are read from the run before (`-ac2`, 13:55 on). They do not involve the baseline, whose
# grinding is the one thing that changed between the two runs, and their rows have the same configurations and
# proof sizes in both (checked in `load`). In the run `-ac3` the machine ran out of memory while these cells
# were measured: its process `m23-128-nopow` started with 0.7 GB unused for a process of 2.9 GB, and its
# commitment took 53.7 ms against 41.0 to 42.6 ms in the three other processes of that size.
RUN_128 = "three-way-minimal-20261116-ac2"
ALL_RUNS = ("three-way-minimal-20261116-ac3", "three-way-minimal-20261116-ac2", "three-way-minimal-20261116-ac",
            "three-way-minimal-20261116-battery")
OTHER_RUNS = ALL_RUNS  # second measurements: a row is compared with every run but the one it is read from
CLEAN_RUNS = ALL_RUNS[:3]  # the runs on AC power: the measure of the noise between runs
SOURCE = {}  # (cell, variant) -> the run that the row is read from
ALLOW_BATTERY = False
# The baseline "Ligerito over GF(2^128)" of the table at 100 bits: `mcanf` (beep::mca_ladder_no_first_sample_at),
# i.e. the ladder of BEEP-Ligerito with no points in its fold rounds and fold challenges ground for the MCA
# bound. `mca` is the same with the sample that Flock's ladders draw on the first commitment.
BASE, BASE_FIRST = "mcanf", "mca"
if "--base" in sys.argv:  # for a run without `mcanf` (the two earlier runs): --base mca
    BASE = sys.argv[sys.argv.index("--base") + 1]
# A row is reported as disturbed if a repetition without proofs of work takes more than SPREAD times the
# median of its repetitions, or if the measured time with proofs of work differs from "prove" by more
# than RESIDUAL (for proofs of MIN_MS or more: below that, a tenth of a millisecond is already 5 %).
SPREAD, RESIDUAL, MIN_MS = 1.5, 0.10, 2.0
SIZES = list(range(15, 24))          # log2 of the number of words of the message
ETA_BEEP, ETA_MCA = "0.001", "0.02"  # the slack of BEEP-Ligerito, and that of Flock's Ligerito
QBITS = 128

WARNINGS = []


def warn(msg):
    WARNINGS.append(msg)
    print("WARNING", msg)


def fail(msg):
    raise SystemExit("FAILED: " + msg)


# ------------------------------------------------------------------ formatting
def down(x, digits=0):
    s = 10 ** digits
    return floor(x * s + 1e-9) / s


def up(x, digits=0):
    s = 10 ** digits
    return ceil(x * s - 1e-9) / s


def fmt(x, digits):
    return f"{x:.{digits}f}"


def m(x):
    """A number as Typst math."""
    return f"${x}$"


def rng(values, digits, unit=""):
    """'a to b' with the lower end rounded down and the upper end rounded up; one number if they agree."""
    lo, hi = fmt(down(min(values), digits), digits), fmt(up(max(values), digits), digits)
    return f"${lo}${unit}" if lo == hi else f"${lo}$ to ${hi}${unit}"


def rng_down(values, digits, unit=""):
    """'a to b' with both ends rounded down (bits of security: every value is at least what is printed)."""
    lo, hi = fmt(down(min(values), digits), digits), fmt(down(max(values), digits), digits)
    return f"${lo}${unit}" if lo == hi else f"${lo}$ to ${hi}${unit}"


def rng_up(values, digits, unit=""):
    """'a to b' with both ends rounded up (bits of grinding: the least whole number that suffices)."""
    lo, hi = fmt(up(min(values), digits), digits), fmt(up(max(values), digits), digits)
    return f"${lo}${unit}" if lo == hi else f"${lo}$ to ${hi}${unit}"


def ms(x):
    """Milliseconds: two decimals below 10 ms, one above."""
    return fmt(x, 2) if x < 9.995 else fmt(x, 1)


def kib(nbytes):
    return fmt(nbytes / 1024, 1)


def pow2(e):
    return f"$2^({e})$"


# ------------------------------------------------------------------ the run
def option(name):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else None


def load():
    """The run of record. With no `--results`: the cells at 100 bits of RUN and the cells at 128 bits of RUN_128
    (see the comment of RUN_128), after a check that the rows at 128 bits of the two runs have the same
    configurations and proof sizes."""
    path = Path(option("--results") or BEEP_LIGERITO / "bench_results" / RUN / "results.json")
    if not path.exists():
        fail(f"no {path}: run beep-ligerito/scripts/collect.py on the run first")
    data = json.loads(path.read_text())
    for r in data["rows"]:
        SOURCE[(r["cell"], r["variant"])] = path.parent.name
    if not option("--results") and RUN_128 != RUN:
        other = json.loads((BEEP_LIGERITO / "bench_results" / RUN_128 / "results.json").read_text())
        theirs = {(r["cell"], r["variant"]): r for r in other["rows"]}
        rows = []
        for r in data["rows"]:
            key = (r["cell"], r["variant"])
            if r["cell"].endswith("-128"):
                o = theirs.get(key)
                if o is None or o["config"] != r["config"] or o["proof_bytes"] != r["proof_bytes"]:
                    fail(f"{key}: the runs {RUN} and {RUN_128} do not have the same configuration and proof size")
                rows.append(o)
                SOURCE[key] = RUN_128
            else:
                rows.append(r)
        cells = {name: (other["cells"][name] if "-128" in name else c) for name, c in data["cells"].items()}
        data = dict(data, rows=rows, cells=cells, binaries_128=other.get("binaries", []),
                    warnings=list(data.get("warnings", [])) + list(other.get("warnings", [])))
    rows = {(r["cell"], r["variant"]): r for r in data["rows"]}
    return data, rows


def check_run(data, rows):
    for w in data.get("warnings", []):
        warn(f"collect.py: {w}")
    expected = set()
    for mu in SIZES:
        for bits in (100, 128):
            expected |= {f"m{mu}-{bits}", f"m{mu}-{bits}-nopow"}
    cells = data["cells"]
    missing = sorted(expected - set(cells))
    if missing:
        fail(f"cells missing from the run: {missing}")
    limited = []
    for name in sorted(expected):
        c = cells[name]
        if c["status"] != "ok":
            fail(f"cell {name}: status {c['status']}")
        meta = c["meta"]
        for key in ("power_before", "power_after"):
            if not meta.get(key, "").startswith("AC"):
                if not (ALLOW_BATTERY or "--allow-battery" in sys.argv):
                    fail(f"cell {name}: {key} = {meta.get(key)!r}")
        t = c.get("time", {})
        fp, rss = t.get("peak_footprint_bytes"), t.get("max_rss_bytes")
        if fp and rss and fp > 1.02 * rss and fp - rss > 32 << 20:
            limited.append(name)
    if limited:
        warn(f"processes with part of their memory compressed or swapped: {limited}")
    for mu in SIZES:
        for bits, variants in ((100, ("split", f"{BASE}-{ETA_MCA}", f"{BASE_FIRST}-{ETA_MCA}", f"beep-{ETA_MCA}",
                                      f"beep-{ETA_BEEP}")),
                               (128, ("split", f"beep-{ETA_MCA}", f"beep-{ETA_BEEP}"))):
            for v in variants:
                r = rows.get((f"m{mu}-{bits}", v))
                if r is None:
                    fail(f"no row for m{mu}-{bits} {v}")
                if r["prove_expected_ms"] is None or r["verify_ms"] is None:
                    fail(f"m{mu}-{bits} {v}: no prove or verify time")
                if r["config"].get("target_bits", 128) != bits and v != "split":
                    fail(f"m{mu}-{bits} {v}: target {r['config'].get('target_bits')}")
    return limited


def table_rows(rows):
    """The rows of the two measured tables, as (cell, variant)."""
    for mu in SIZES:
        for bits, variants in ((100, ("split", f"{BASE}-{ETA_MCA}", f"beep-{ETA_BEEP}")), (128, ("split", f"beep-{ETA_BEEP}"))):
            for v in variants:
                yield f"m{mu}-{bits}", v


def stability(rows):
    """How stable the rows of the tables are. Returns (disturbed rows, largest max/median of the repetitions
    without proofs of work, largest |measured with proofs of work - "prove"| / "prove"), the last two over
    the proofs of MIN_MS or more."""
    disturbed, spreads, resids = [], [], []
    for key in table_rows(rows):
        r = rows[key]
        if r["prove_expected_ms"] < MIN_MS:
            continue
        reps = sorted(r.get("prove_nopow_ms_reps") or [])
        spread = reps[-1] / reps[len(reps) // 2] if reps else 1.0
        resid = abs(r.get("pow_model_residual_ms") or 0.0) / r["prove_expected_ms"]
        spreads.append(spread)
        resids.append(resid)
        if spread > SPREAD or resid > RESIDUAL:
            disturbed.append(f"{key[0]} {key[1]} (slowest repetition {spread:.2f} times the median; "
                             f"measured with proofs of work {100 * resid:.0f} % from \"prove\")")
    return disturbed, max(spreads), max(resids)


def machine_state(cells):
    """Idle CPU (%) and unused memory (GB) right before each process, from the `top` line of its meta file."""
    idle, unused = [], []
    for c in cells.values():
        top = c["meta"].get("top_before", "")
        if "% idle" in top:
            idle.append(float(top.split("% idle")[0].split()[-1]))
        if "unused" in top:
            word = top.split(" unused")[0].split()[-1]
            unused.append(float(word[:-1]) * {"M": 1 / 1024, "G": 1.0}[word[-1]])
    return idle, unused


def describe_run(path):
    """A run of the same cells, for the README: its processes by power source, when it ran, the unused memory
    before its processes, and the slowest repetition without proofs of work against the median of its row
    (over the proofs of MIN_MS or more)."""
    data = json.loads(Path(path).read_text())
    cells = data["cells"]
    battery = [n for n, c in cells.items() if not c["meta"].get("power_before", "").startswith("AC")]
    starts = sorted(c["meta"].get("start", "") for c in cells.values() if c["meta"].get("start"))
    _, unused = machine_state(cells)
    _, unused_battery = machine_state({n: cells[n] for n in battery})
    spreads = {}
    for r in data["rows"]:
        reps = sorted(r.get("prove_nopow_ms_reps") or [])
        if reps and (r.get("prove_expected_ms") or 0) >= MIN_MS:
            spreads[(r["cell"], r["variant"])] = reps[-1] / reps[len(reps) // 2]
    worst = max(spreads, key=spreads.get)
    return {"processes": len(cells), "battery": len(battery), "from": starts[0][11:16], "to": starts[-1][11:16],
            "unused": unused, "unused_battery": unused_battery, "spread_max": spreads[worst], "worst": worst,
            "rows": len(data["rows"])}


def check_shapes(rows):
    """The shapes that the README and the cells file state: Flock's rows per level, and the levels of the
    ladder of BEEP-Ligerito and of the baselines."""
    for mu in SIZES:
        for bits in (100, 128):
            cfg = rows[(f"m{mu}-{bits}", f"beep-{ETA_BEEP}")]["config"]
            split = rows[(f"m{mu}-{bits}", "split")]["config"]
            k0 = {21: 4, 22: 5}.get(mu, 6)
            levels = 2 if mu <= 16 else 3 if mu <= 20 else 4
            if (cfg["initial_k"], split["initial_k"]) != (k0, k0) or any(k != 4 for k in cfg["recursive_ks"]):
                fail(f"m{mu}-{bits}: rows per level {cfg['initial_k']}, {cfg['recursive_ks']}")
            if cfg["log_inv_rates"] != [1, 3, 5, 7][:levels] or split["log_inv_rates"][:2] != [1, 2]:
                fail(f"m{mu}-{bits}: rates {cfg['log_inv_rates']} (Flock: {split['log_inv_rates']})")
            # at these rates the codewords of a level are as long as those of Flock's level
            cols = lambda c: [mu - c["initial_k"]] + c["recursive_log_msg_cols"]
            ours = [a + b for a, b in zip(cols(cfg), cfg["log_inv_rates"])]
            flock = [a + b for a, b in zip(cols(split), split["log_inv_rates"])]
            if ours != flock[:len(ours)] or len(flock) < len(ours):
                fail(f"m{mu}-{bits}: block lengths 2^{ours} (Flock: 2^{flock})")
            # a new level while the folded message has 2^7 elements or more
            last_cols = cfg["recursive_log_msg_cols"][-1]
            if not (last_cols + 4 >= 7 > last_cols):
                fail(f"m{mu}-{bits}: the last message has 2^{last_cols} elements")


def compare_runs(rows, other_path):
    """The rows of the tables in a second run of the same cells: the sizes must agree, and the times are
    compared. Returns the list of 'prove' ratios (this run / the other) for the proofs of MIN_MS or more."""
    other = {(r["cell"], r["variant"]): r for r in json.loads(Path(other_path).read_text())["rows"]}
    ratios = {}
    other_name = Path(other_path).parent.name
    for key in table_rows(rows):
        if key not in other or SOURCE.get(key) == other_name:
            continue  # a variant that the other run does not have, or the run that the row is read from
        a, b = rows[key], other[key]
        if key[1].startswith(BASE + "-") and a["config"] != b["config"]:
            continue  # the baseline of an earlier run ground its fold challenges per level: another variant
        if a["proof_bytes"] != b["proof_bytes"] or a["config"] != b["config"]:
            fail(f"{key}: the two runs do not have the same proof size and configuration")
        if a["prove_expected_ms"] >= MIN_MS:
            ratios[key] = a["prove_expected_ms"] / b["prove_expected_ms"]
    return ratios


# ------------------------------------------------------------------ exact rechecks
def mca_numerator(n, rate, eta, folds):
    """Flock's numerator of a fold under MCA (its Appendix C.3): the bound of BCHKS25, Theorem 4.6, for a
    fold of two words, a = (2 r^5 + 3 r gamma rho)/(3 rho^(3/2)) n + r/sqrt(rho) with r = max(ceil(sqrt(rho)
    /(2 eta)), 3) + 1/2 and gamma = 1 - sqrt(rho) - eta, times the row union 2^(folds - 1) of the worst
    round of a level with 2^folds rows. Floats, as in flock-core (`paper_johnson_log_a`)."""
    rho, eta = 2.0 ** -rate, float(bp.frac(eta))
    r = max(ceil(sqrt(rho) / (2 * eta)), 3) + 0.5
    gamma = 1 - sqrt(rho) - eta
    a = (2 * r ** 5 + 3 * r * gamma * rho) / (3 * rho ** 1.5) * n + r / sqrt(rho)
    return a * 2.0 ** max(folds - 1, 0)


def mca_fold_bits(n, rate, eta, folds, with_sumcheck=True):
    """-log2 of the error of a fold round of Ligerito over a field of 2^128 elements: (a + 2L)/|F|."""
    rho = 2.0 ** -rate
    list_real = 1 / (2 * float(bp.frac(eta)) * sqrt(rho))
    return QBITS - log2(mca_numerator(n, rate, eta, folds) + (2 * list_real if with_sumcheck else 0))


def check_beep_rows(data):
    """`beep_params.check_results` for the BEEP rows, quietly. Returns (levels checked, failures)."""
    seen, failures = set(), []
    for row in data["rows"]:
        if not row["variant"].startswith("beep-"):
            continue
        levels = row["config"]["levels"]
        lam = bp.target_of(row)
        for li, lv in enumerate(levels):
            nxt = levels[li + 1] if li + 1 < len(levels) else None
            key = json.dumps([li, lv, nxt and nxt["list_size"], row["config"].get("grinds") if li == 0 else None],
                             sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            bad = bp.check_level(lv, lam=lam, level_index=li, next_level=nxt, last=nxt is None)
            if li == 0:
                bad += bp.check_grinds(row["config"], lam=lam)
            if bad:
                failures.append(f"{row['cell']} {row['variant']} level {li}: " + "; ".join(bad))
    return len(seen), failures


def check_mca_rows(data):
    """The levels of the baseline `mca-<eta>` (beep::mca_ladder_at). Returns (levels checked, failures)."""
    seen, failures = set(), []
    for row in data["rows"]:
        if not row["variant"].startswith(("mca-", "mcanf-")):
            continue
        cfg = row["config"]
        levels, grinds = cfg["levels"], cfg["grinds"]
        lam = bp.target_of(row)
        shift = 64 + QBITS - lam
        for li, lv in enumerate(levels):
            key = json.dumps([li, lv, grinds["fold"][li], cfg["fold_round_numerators"][li], grinds["fold_rounds"][li]],
                             sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            bad = []
            rate, c, folds = lv["log_inv_rate"], lv["log_msg_cols"], lv["folds"]
            n = 1 << (c + rate)
            eta = bp.frac(repr(lv["eta"]))
            L = lv["list_size"]
            if L != bp.johnson_list_simple(rate, eta):
                bad.append(f"list size {L}")
            if lv["samples"] != 0 or cfg["samples"][li] != 0:
                bad.append("the baseline has points")
            # the fold numerator: ceil(a + 2 L_real), with Flock's a recomputed here
            want = mca_numerator(n, rate, eta, folds) + 2 / (2 * float(eta) * 2.0 ** (-rate / 2))
            num = lv["fold_numerator"]
            if not (num >= want - 1e-6 * want and num <= want * (1 + 1e-9) + 1):
                bad.append(f"fold numerator {num}, recomputed {want:.1f}")
            # One numerator and one proof of work per fold round: round j (from 0) folds 2^(folds - 1 - j)
            # pairs of rows, so its numerator is ceil(a / 2^j + 2 L_real), with `a` that of the first round.
            a0 = mca_numerator(n, rate, eta, folds)
            l2 = 2 / (2 * float(eta) * 2.0 ** (-rate / 2))
            nums = cfg["fold_round_numerators"][li]
            gs = grinds["fold_rounds"][li]
            if len(nums) != folds or len(gs) != folds or nums[0] != num or gs[0] != grinds["fold"][li]:
                bad.append(f"{len(nums)} numerators and {len(gs)} grinds for {folds} fold rounds, or a first round that "
                           f"is not the one of the level")
            for j, (nj, g) in enumerate(zip(nums, gs)):
                wj = a0 / 2 ** j + l2
                if not (nj >= wj - 1e-6 * wj and nj <= wj * (1 + 1e-9) + 1):
                    bad.append(f"round {j}: fold numerator {nj}, recomputed {wj:.1f}")
                if g.get("target") is not None:
                    T = g["target"]
                    if not nj * T < 2 ** shift:
                        bad.append(f"round {j}: fold target {T} does not cover the numerator {nj}")
                    if nj * (T + 1) < 2 ** shift:
                        bad.append(f"round {j}: fold target {T} is not the largest one")
                elif not nj < 2 ** (QBITS - lam + g["bits"]):
                    bad.append(f"round {j}: {g['bits']} fold bits do not cover the numerator {nj}")
            Q, qg = lv["queries"], lv["query_grinding_bits"]
            if bp.queries_are_least(Q, rate, eta, qg, lam) is not True:
                bad.append(f"queries {Q}")
            if row["variant"].startswith("mcanf-") and li == 0:
                # No sample on the first commitment: nothing binds it, and the list is carried through the
                # fold rounds by the term 2L of the numerator, which is checked above.
                if lv["ood_samples"] != 0 or cfg["ood_samples"][0] != 0:
                    bad.append("the baseline with no first sample has one")
            elif not bp.binding_reaches(li, rate, eta, folds + c, lv["ood_samples"], lam, QBITS):
                bad.append(f"the {lv['ood_samples']} binding samples do not reach the target")
            if lv["claim_numerator"] != L + 2 or lv["claim_numerator"] * (grinds["claim"][li].get("target") or 0) >= 2 ** shift:
                bad.append("claim batching")
            if grinds["claim"][li].get("target") is None and not L + 2 < 2 ** (QBITS - lam + grinds["claim"][li]["bits"]):
                bad.append("claim batching bits")
            nxt = levels[li + 1] if li + 1 < len(levels) else None
            if nxt is not None:
                numc = nxt["list_size"] * max((Q - 1).bit_length(), 1)
                gc = grinds["consistency"][li]
                if lv["consistency_numerator"] != numc:
                    bad.append(f"consistency numerator {lv['consistency_numerator']}, exact {numc}")
                if gc.get("target") is not None:
                    if not numc * gc["target"] < 2 ** shift:
                        bad.append("consistency target")
                elif not numc < 2 ** (QBITS - lam + gc["bits"]):
                    bad.append("consistency bits")
            if bad:
                failures.append(f"{row['cell']} {row['variant']} level {li}: " + "; ".join(bad))
    return len(seen), failures


# ------------------------------------------------------------------ the tables
def error_table(rows):
    """Table "errors": the first fold round of the first level of every instance, over a field of 2^128
    elements, for a target of 128 bits."""
    out, info = [], []
    for mu in SIZES:
        beep = rows[(f"m{mu}-128", f"beep-{ETA_BEEP}")]["config"]
        split = rows[(f"m{mu}-128", "split")]["config"]
        mca = rows[(f"m{mu}-100", f"{BASE}-{ETA_MCA}")]["config"]
        lv = beep["levels"][0]
        rate, c, folds = lv["log_inv_rate"], lv["log_msg_cols"], lv["folds"]
        n = 1 << (c + rate)
        N, L, t, pts, var = lv["line_bound"], lv["list_size"], lv["threshold"], lv["samples"], lv["max_variables"]
        if not bp.points_reach(t, N, L, var, pts, 128, QBITS):
            fail(f"m{mu}: the points of BEEP do not reach 128 bits")
        k1 = bp.points_bits(t, N, L, var, pts, QBITS)             # kappa_1(t)
        k2 = QBITS - log2(t - 1 + 2 * L)                           # kappa_2(t)
        if abs(k1 - lv["sample_bits"]) > 1e-6:
            fail(f"m{mu}: kappa_1 {k1} here, {lv['sample_bits']} in the bench")
        lig02 = mca_fold_bits(n, rate, ETA_MCA, folds)
        lig001 = mca_fold_bits(n, rate, ETA_BEEP, folds)
        # the same number from the Rust side (the level 0 of the baseline at 100 bits is the same code)
        rust = mca["levels"][0]
        if (rust["log_msg_cols"], rust["log_inv_rate"], rust["folds"]) != (c, rate, folds):
            fail(f"m{mu}: the baseline and BEEP do not have the same first level")
        if abs(rust["fold_bits"] - lig02) > 1e-6:
            fail(f"m{mu}: fold bits of the baseline {rust['fold_bits']} in the bench, {lig02} here")
        q_lig, q_beep = split["queries"][0], beep["queries"][0]
        if (split["log_inv_rates"][0], split["initial_k"]) != (rate, folds):
            fail(f"m{mu}: Flock's first level differs")
        if q_lig != bp.queries(rate, ETA_MCA, 16, 128) or q_beep != bp.queries(rate, ETA_BEEP, 16, 128):
            fail(f"m{mu}: queries {q_lig}, {q_beep}")
        out.append([pow2(mu), pow2(folds), pow2(c + rate),
                    m(fmt(down(lig02, 1), 1)), m(fmt(down(lig001, 1), 1)), m(q_lig),
                    m(pts), m(fmt(down(k1, 1), 1)), m(fmt(down(k2, 1), 1)), m(q_beep)])
        # kappa_2(t) of BEEP at the slack of Ligerito, for the sentence "this barely depends on eta"
        lv02 = rows[(f"m{mu}-128", f"beep-{ETA_MCA}")]["config"]["levels"][0]
        k2_02 = QBITS - log2(lv02["threshold"] - 1 + 2 * lv02["list_size"])
        info.append({"mu": mu, "folds": folds, "log_n": c + rate, "lig02": lig02, "lig001": lig001,
                     "k1": k1, "k2": k2, "k2_02": k2_02, "m": pts, "t": t, "N": N, "L": L, "q_lig": q_lig,
                     "q_beep": q_beep, "list_mca": mca["levels"][0]["list_size"]})
    return out, info


def commit_of(rows, cell):
    both = rows[(cell, "split")].get("commit_ms_both") or [rows[(cell, "split")]["commit_ms"]]
    return sum(both) / len(both)


def measured_table(rows, bits, variants):
    out = []
    for mu in SIZES:
        cell = f"m{mu}-{bits}"
        line = [pow2(mu), m(ms(commit_of(rows, cell)))]
        for v in variants:
            r = rows[(cell, v)]
            line += [m(kib(r["proof_bytes"])), m(ms(r["prove_expected_ms"])), m(fmt(r["verify_ms"], 2))]
        out.append(line)
    return out


README_BEGIN = "<!-- minimal-run:begin"
README_END = "<!-- minimal-run:end -->"


def plain(cell):
    """A cell or a number of the paper (Typst markup) as plain text."""
    return cell.replace("$", "").replace("^(", "^").replace(")", "") if "^(" in cell else cell.replace("$", "")


def readme_block(N, T, run, checked, checked_mca):
    """The generated part of the section "The minimal run" of beep-ligerito/README.md: the state of the
    machine, the three tables and the numbers, as Markdown. Written by `--write-readme` between the markers."""
    n = lambda key: plain(N.get(key, "?"))
    heads = {
        "errors": ["size", "k", "n", "Ligerito fold, eta 0.02", "Ligerito fold, eta 0.001", "Ligerito queries",
                   "BEEP m", "BEEP round 1", "BEEP round 2", "BEEP queries"],
        "bits100": ["size", "commit (ms)"] + [f"{v} {c}" for v in ("Flock", "GF(2^128)", "BEEP")
                                              for c in ("proof (KiB)", "prove (ms)", "verify (ms)")],
        "bits128": ["size", "commit (ms)"] + [f"{v} {c}" for v in ("Flock", "BEEP")
                                              for c in ("proof (KiB)", "prove (ms)", "verify (ms)")],
    }
    titles = {
        "errors": "Bits of security of the first fold round before grinding, over a field of 2^128 elements, for a "
                  "target of 128 bits (the paper's first table). \"Round 1\" and \"round 2\" are the errors of the "
                  "samples and of the fold challenge of the BEEP IOR; the queries have 16 bits of grinding.",
        "bits100": "100 bits (the paper's second table, top). \"GF(2^128)\" is the baseline `mcanf-0.02`, \"BEEP\" is "
                   "`beep-0.001`, \"Flock\" is `split` on the profile `fast100`.",
        "bits128": "128 bits (bottom). \"BEEP\" is `beep-0.001`, \"Flock\" is `split` on the profile `fast`.",
    }
    out = [f"{README_BEGIN} (written by paper/scripts/minimal_tables.py --write-readme from the runs "
           f"{N.get('run:name')} and {N.get('run128:name')}; do not edit by hand) -->", ""]
    out += [
        f"**Which run.** The table at 100 bits is read from the run `{n('run:name')}` ({n('run:from')} to "
        f"{n('run:to')}), and the table at 128 bits from the run `{n('run128:name')}` ({n('run128:from')} to "
        f"{n('run128:to')}), both on {n('run:date')}. The cells at 128 bits do not involve the baseline, whose grinding "
        f"is the one thing that changed between the two runs, and their rows have the same configurations and proof "
        f"sizes in both (the script checks it). They are read from the earlier run because the machine ran out of "
        f"memory while the later one measured them: for 2^23 elements the commitment took "
        f"{N.get('commit23:ac3:worst')} against {n('commit23:ac3:rest')} ms in the three other processes of that size "
        f"({N.get('commit23:ac2:worst')} against {n('commit23:ac2:rest')} ms in the run `-ac2`).",
        "",
        f"**Machine and state.** {n('run:cpu')} ({n('run:cores')}), {n('run:memory-gb')} GB, {n('run:threads')} threads, "
        f"{n('run:power')}, through the gate, with the idle check before every cell; {n('run:reps')} timed repetitions "
        f"per variant after a warm-up, medians. Right before a process of the cells that the tables use: idle CPU at "
        f"least {n('run:idle-pct-min-part')} % and {n('run:unused-gb-part')} GB of unused memory (100 bits), "
        f"{n('run128:idle-pct-min-part')} % and {n('run128:unused-gb-part')} GB (128 bits); load average {n('run:load')}. "
        f"Processes with part of their memory compressed: {n('run:limited')}. Rows of the two measured tables that the "
        f"script reports as disturbed: {n('run:disturbed')} (over the proofs of {MIN_MS:g} ms or more, the slowest of the "
        f"{n('run:reps')} repetitions without proofs of work takes at most {n('run:spread-max')} times their median, and "
        f"the time measured with proofs of work is within {n('run:resid-pct-max')} % of \"prove\"). The warnings of "
        f"the script:",
        "",
    ]
    out += [f"- {w}" for w in WARNINGS] or ["- none"]
    out += [
        "",
        f"**Exact recheck.** {checked} distinct levels of BEEP-Ligerito and {checked_mca} of the two baselines, in "
        f"integer arithmetic: no failure.",
        "",
        "**Second measurements.** The four runs of the day have the rows of Ligerito (Flock) and of BEEP-Ligerito "
        "with the same proof sizes and configurations. \"prove\" of a row of the tables is within "
        f"{n('run:noise-pct')} % of the same row in the other runs on AC power (proofs of {MIN_MS:g} ms or more; the "
        "commitment moves more: the two tables print it from different processes). The baselines differ between "
        "the runs (see \"The variants\"), so their rows have no second measurement with proofs of work.",
        "",
    ]
    notes = {
        "ac3": "the run of the table at 100 bits",
        "ac2": "the run of the table at 128 bits; its baselines `mca` and `mcanf` ground every fold round of a level "
               "for its first round",
        "ac": "no `mcanf`; `mca` ground every fold round of a level for its first round",
        "battery": "no `mcanf`; `mca` as in the run `-ac`",
    }
    for name in OTHER_RUNS:
        path = BEEP_LIGERITO / "bench_results" / name / "results.json"
        if not path.exists():
            continue
        d, tag = describe_run(path), name.split("-")[-1]
        line = (f"- `bench_results/{name}` ({d['from']} to {d['to']}, {d['processes']} processes, "
                f"{d['battery']} of them on battery power")
        if d["unused_battery"]:
            line += f", with {plain(rng(d['unused_battery'], 1))} GB of unused memory before them"
        line += (f"; {plain(rng(d['unused'], 1))} GB over all its processes): {notes.get(tag, '')}. The slowest "
                 f"repetition of a row is at most {fmt(up(d['spread_max'], 1), 1)} times the median of the row "
                 f"(`{d['worst'][0]}`, `{d['worst'][1]}`).")
        parts = [f"{n(f'other:{tag}:prove-ratio-{bits}')} times ({bits} bits)" for bits in (100, 128)
                 if f"other:{tag}:prove-ratio-{bits}" in N]
        if parts:
            line += (f" \"prove\" in the tables is " + " and ".join(parts) + f" that of this run, over "
                     f"{n(f'other:{tag}:rows')} rows with proofs of {MIN_MS:g} ms or more.")
        out.append(line)
    for name in ("errors", "bits100", "bits128"):
        out += ["", titles[name], "", "| " + " | ".join(heads[name]) + " |", "|" + "---:|" * len(heads[name])]
        out += ["| " + " | ".join(plain(c) for c in line) + " |" for line in T[name]]
    out += [
        "",
        "In short (every range is over the nine sizes):",
        "",
        f"- **100 bits, BEEP-Ligerito against Ligerito over GF(2^128).** Proofs {n('100:size-saving-pct')} % smaller. "
        f"Prover {n('100:prove-ratio')} times as long ({n('100:nopow-ratio')} times without proofs of work, and "
        f"{n('100:total-ratio')} times when the commitment is counted). Verifier {n('100:verify-ratio')} times as long. "
        f"With the proofs of work as they happened (the medians of the processes that did them) the prover ratio is "
        f"{n('100:prove-ratio-measured')}. "
        f"BEEP-Ligerito is slower at {n('100:slower-count')} of the {n('100:sizes')} sizes. It has {n('params:m-100')} "
        f"samples per fold round and no proof of work on a fold challenge; the baseline needs {n('100:mca-fold-grind')} "
        f"bits in the first round of its first level and one bit less in each later round "
        f"({n('100:mca-pow-ms')} ms of proofs of work per proof, {n('100:mca-fold-pow-share-pct')} % of its time for the "
        f"fold challenges). This schedule per round tries {n('100:mca-round-schedule-pct')} % of the hashes of Flock's "
        f"convention, which grinds every round of a level for its first round (the run `-ac2`). At 128 bits the "
        f"baseline would need {n('err:lig-grind')} bits in the first round of the first level, and at the slack 0.001 "
        f"its fold has {n('err:lig001')} bits before grinding (the first table), which is why it runs at 100 bits and "
        f"at the slack 0.02 only.",
        f"- **The same slack on both sides** (`beep-0.02` against the baseline): the proofs of BEEP-Ligerito are "
        f"{n('100:same-eta-size-kib')} KiB larger (the answers to the samples), and its prover takes "
        f"{n('100:same-eta-prove-ratio')} times as long ({n('100:same-eta-nopow-ratio')} times without proofs of work: the "
        f"samples cost {n('100:samples-ms')} ms).",
        f"- **Flock's sample on the first commitment** (`mca-0.02` against `mcanf-0.02`): with it the baseline takes "
        f"{n('100:first-sample-prove-ratio')} times as long and its proof is {n('100:first-sample-bytes')} bytes longer. "
        f"Against that baseline BEEP-Ligerito takes {n('100s:prove-ratio')} times as long.",
        f"- **100 bits, against Ligerito (Flock).** Proofs {n('100f:size-saving-pct')} % smaller, prover "
        f"{n('100f:prove-ratio')} times as long, verifier {n('100f:verify-ratio')} times. Not like for like: other levels, "
        f"another prover, fold challenges in GF(2^256).",
        f"- **128 bits, BEEP-Ligerito against Ligerito (Flock).** Proofs {n('128:size-saving-pct')} % smaller. Prover "
        f"{n('128:prove-ratio')} times as long ({n('128:nopow-ratio')} times without proofs of work), with "
        f"{n('128:pow-share-pct')} % of its time in proofs of work: {n('128:fold-pow-share-pct')} % for the fold "
        f"challenges (searches of 2^x expected hashes with x from {n('128:beep-fold-grind-log2')}, {n('params:m-128')} "
        f"samples per fold round) and "
        f"{n('128:query-pow-share-pct')} % for the 16 bits of the queries, which Flock grinds as well (proofs of work "
        f"are {n('128:flock-pow-share-pct')} % of its time). Flock's ladder has one more level at "
        f"{n('128:fewer-levels')} of the {n('100:sizes')} sizes. With the proofs of work as they happened the prover "
        f"ratio is {n('128:prove-ratio-measured')}: the model of the proofs of work understates BEEP-Ligerito at "
        f"2^17 elements, where the measured ratio is the largest. Verifier {n('128:verify-ratio')} times as long. Not "
        f"like for like either.",
        "",
        README_END,
    ]
    return "\n".join(out)


def main():
    data, rows = load()
    limited = check_run(data, rows)
    check_shapes(rows)
    checked, failures = check_beep_rows(data)
    for f in failures:
        print("FAIL", f)
    checked_mca, failures_mca = check_mca_rows(data)
    for f in failures_mca:
        print("FAIL", f)
    if failures or failures_mca:
        fail(f"{len(failures) + len(failures_mca)} levels fail their exact recheck")
    print(f"exact recheck: {checked} BEEP levels and {checked_mca} levels of the baseline, no failure")

    N = {}  # the numbers of the prose
    T = {}
    T["errors"], info = error_table(rows)
    # `mca` is the baseline of the table, `mca_first` the same with Flock's sample on the first commitment
    mca, mca_first = f"{BASE}-{ETA_MCA}", f"{BASE_FIRST}-{ETA_MCA}"
    beep, beep02 = f"beep-{ETA_BEEP}", f"beep-{ETA_MCA}"
    for mu in SIZES:
        if mca == mca_first:
            break  # a run without `mcanf` (--base mca)
        a, b = rows[(f"m{mu}-100", mca)], rows[(f"m{mu}-100", mca_first)]
        ca, cb = a["config"], b["config"]
        same = all(ca[key] == cb[key] for key in ("queries", "log_inv_rates", "initial_k", "recursive_ks", "samples",
                                                  "fold_grinding_bits", "query_grinding_bits"))
        same = same and ca["grinds"]["fold"] == cb["grinds"]["fold"] and ca["ood_samples"][1:] == cb["ood_samples"][1:]
        same = same and ca["grinds"]["fold_rounds"] == cb["grinds"]["fold_rounds"]
        same = same and ca["fold_round_numerators"] == cb["fold_round_numerators"]
        same = same and [lv["fold_numerator"] for lv in ca["levels"]] == [lv["fold_numerator"] for lv in cb["levels"]]
        if not same or ca["ood_samples"][0] != 0 or cb["ood_samples"][0] == 0 or not a["proof_bytes"] < b["proof_bytes"]:
            fail(f"m{mu}: the two baselines must differ in the sample on the first commitment only")
        bc = rows[(f"m{mu}-100", beep02)]["config"]
        if any(ca[key] != bc[key] for key in ("queries", "log_inv_rates", "initial_k", "recursive_ks", "ood_samples",
                                              "query_grinding_bits")):
            fail(f"m{mu}: the baseline and BEEP-Ligerito at the same slack must have the same ladder")
    T["bits100"] = measured_table(rows, 100, ("split", mca, beep))
    T["bits128"] = measured_table(rows, 128, ("split", beep))

    # ---- the machine and the run
    mach = data["machine"]
    cells = data["cells"]
    N["run:cpu"] = mach.get("machdep.cpu.brand_string", "?")
    N["run:cores"] = f"{mach.get('hw.perflevel0.physicalcpu')} performance and {mach.get('hw.perflevel1.physicalcpu')} efficiency cores"
    N["run:memory-gb"] = str(round(int(mach.get("hw.memsize", 0)) / 2 ** 30))
    N["run:threads"] = str(rows[("m15-100", "split")]["threads"])
    N["run:reps"] = str(rows[("m15-100", "split")]["reps"])
    N["run:date"] = mach.get("date", "?")[:10]
    # the power source of the processes of the tables
    sources = {c["meta"].get(key, "?").split()[0] for name, c in cells.items() for key in ("power_before", "power_after")}
    if sources == {"AC"}:
        N["run:power"] = "on AC power"
    elif sources == {"Battery"}:
        N["run:power"] = "on battery power"
    else:
        N["run:power"] = "partly on battery power"
        warn(f"power sources of the processes: {sorted(sources)}")
    loads = [float(c["meta"]["load_before"].split()[0]) for c in cells.values() if c["meta"].get("load_before")]
    N["run:load"] = rng(loads, 1)
    N["run:processes"] = str(len(cells))
    N["run:limited"] = str(len(limited))
    idle, unused = machine_state(cells)
    if idle:
        N["run:idle-pct-min"] = m(fmt(down(min(idle), 0), 0))
    if unused:
        N["run:unused-gb"] = rng(unused, 1)
    for part, tag in (("-100", "run"), ("-128", "run128")):
        starts = sorted(c["meta"].get("start", "") for name, c in cells.items() if part in name and c["meta"].get("start"))
        if starts:
            N[f"{tag}:from"], N[f"{tag}:to"] = starts[0][11:16], starts[-1][11:16]
        idle_p, unused_p = machine_state({name: c for name, c in cells.items() if part in name})
        if unused_p:
            N[f"{tag}:unused-gb-part"] = rng(unused_p, 1)
            N[f"{tag}:idle-pct-min-part"] = m(fmt(down(min(idle_p), 0), 0))
    N["run:name"], N["run128:name"] = RUN, (RUN_128 if not option("--results") else RUN)
    # the commitment of the largest size in the four processes of each run on AC power: what a process that ran
    # short of memory looks like (the reason for RUN_128)
    if not option("--results"):
        for name in CLEAN_RUNS:
            d = json.loads((BEEP_LIGERITO / "bench_results" / name / "results.json").read_text())
            vals = {n: c["context"]["commit_ms"] for n, c in d["cells"].items() if n.startswith(f"m{SIZES[-1]}-")}
            worst = max(vals, key=vals.get)
            rest = [v for n, v in vals.items() if n != worst]
            tag = name.split("-")[-1]
            N[f"commit23:{tag}:worst"] = f"{fmt(vals[worst], 1)} ms (`{worst}`)"
            N[f"commit23:{tag}:rest"] = rng(rest, 1)
    disturbed, spread_max, resid_max = stability(rows)
    for d in disturbed:
        warn(f"disturbed row: {d}")
    N["run:disturbed"] = str(len(disturbed))
    N["run:spread-max"] = m(fmt(up(spread_max, 2), 2))
    N["run:resid-pct-max"] = m(fmt(up(100 * resid_max, 0), 0))
    # second measurements of the rows of the tables: the earlier runs of the same cells
    others = [option("--compare")] if option("--compare") else (
        [] if option("--results") else [BEEP_LIGERITO / "bench_results" / name / "results.json" for name in OTHER_RUNS])
    noise = []
    for other in others:
        if not Path(other).exists():
            continue
        tag = Path(other).parent.name.split("-")[-1]
        ratios = compare_runs(rows, other)
        for bits in (100, 128):
            xs = [x for (cell, v), x in ratios.items() if cell.endswith(f"-{bits}")]
            if xs:
                N[f"other:{tag}:prove-ratio-{bits}"] = rng(xs, 2)
        N[f"other:{tag}:rows"] = str(len(ratios))
        if Path(other).parent.name in CLEAN_RUNS:
            noise += [abs(x - 1) for x in ratios.values()]
    if noise:
        # how far "prove" of a row of the tables is from the same row of the earlier runs on AC power
        N["run:noise-pct"] = m(fmt(up(100 * max(noise), 0), 0))
    N["params:qgrind"] = "16"
    N["eta:beep"], N["eta:lig"] = ETA_BEEP, ETA_MCA
    N["sizes:first"], N["sizes:last"] = pow2(SIZES[0]), pow2(SIZES[-1])

    # ---- the errors
    N["err:lig02"] = rng_down([i["lig02"] for i in info], 1)
    N["err:lig001"] = rng_down([i["lig001"] for i in info], 1)
    N["err:beep2"] = rng_down([i["k2"] for i in info], 1)
    N["err:beep2-02"] = rng_down([i["k2_02"] for i in info], 1)
    N["err:beep-grind"] = rng_up([128 - i["k2"] for i in info], 0)
    N["err:lig-grind"] = rng_up([128 - i["lig02"] for i in info], 0)
    # the same with one decimal (the proofs of work are thresholds, not whole numbers of bits)
    N["err:beep-grind-1"] = rng_up([128 - i["k2"] for i in info], 1)
    N["err:lig-grind-1"] = rng_up([128 - i["lig02"] for i in info], 1)
    N["err:m"] = " or ".join(m(v) for v in sorted({i["m"] for i in info}))
    N["err:L-beep"] = " or ".join(m(v) for v in sorted({i["L"] for i in info}))
    N["err:L-lig"] = " or ".join(m(v) for v in sorted({i["list_mca"] for i in info}))
    N["err:q-lig"] = " or ".join(m(v) for v in sorted({i["q_lig"] for i in info}))
    N["err:q-beep"] = " or ".join(m(v) for v in sorted({i["q_beep"] for i in info}))
    N["err:q-saving-pct"] = rng([100 * (1 - i["q_beep"] / i["q_lig"]) for i in info], 0)
    all_m = sorted({s for mu in SIZES for b in (100, 128) for s in rows[(f"m{mu}-{b}", beep)]["config"]["samples"]})
    N["params:m-all"] = f"${all_m[0]}$ to ${all_m[-1]}$" if len(all_m) > 1 else f"${all_m[0]}$"
    N["params:m-100"] = " or ".join(m(v) for v in sorted({s for mu in SIZES for s in rows[(f"m{mu}-100", beep)]["config"]["samples"]}))
    N["params:m-128"] = " or ".join(m(v) for v in sorted({s for mu in SIZES for s in rows[(f"m{mu}-128", beep)]["config"]["samples"]}))

    def ratios(bits, a, b, key):
        """a / b over the sizes, for a field of the rows or a function of a row."""
        f = key if callable(key) else (lambda r: r[key])
        return [f(rows[(f"m{mu}-{bits}", a)]) / f(rows[(f"m{mu}-{bits}", b)]) for mu in SIZES]

    def total(bits):
        return lambda r: r["prove_expected_ms"] + commit_of(rows, r["cell"])

    for bits, base, tag in ((100, mca, "100"), (100, "split", "100f"), (128, "split", "128")):
        size = ratios(bits, beep, base, "proof_bytes")
        N[f"{tag}:size-ratio"] = rng(size, 2)
        N[f"{tag}:size-saving-pct"] = rng([100 * (1 - x) for x in size], 0)
        N[f"{tag}:prove-ratio"] = rng(ratios(bits, beep, base, "prove_expected_ms"), 2)
        N[f"{tag}:nopow-ratio"] = rng(ratios(bits, beep, base, "prove_nopow_ms"), 2)
        N[f"{tag}:total-ratio"] = rng(ratios(bits, beep, base, total(bits)), 2)
        N[f"{tag}:verify-ratio"] = rng(ratios(bits, beep, base, "verify_ms"), 2)
        # the same for 2^18 words and more, where a proof takes a few milliseconds or more
        big = [i for i, mu in enumerate(SIZES) if mu >= 18]
        pr = ratios(bits, beep, base, "prove_expected_ms")
        N[f"{tag}:prove-ratio-big"] = rng([pr[i] for i in big], 2)
        tr = ratios(bits, beep, base, total(bits))
        N[f"{tag}:total-ratio-big"] = rng([tr[i] for i in big], 2)
    # the same slack on both sides, at 100 bits: what the answers add
    N["100:same-eta-size-kib"] = rng([(rows[(f"m{mu}-100", beep02)]["proof_bytes"] - rows[(f"m{mu}-100", mca)]["proof_bytes"]) / 1024
                                      for mu in SIZES], 1)
    N["100:same-eta-prove-ratio"] = rng(ratios(100, beep02, mca, "prove_expected_ms"), 2)
    N["100:same-eta-nopow-ratio"] = rng(ratios(100, beep02, mca, "prove_nopow_ms"), 2)
    N["100:same-eta-verify-ratio"] = rng(ratios(100, beep02, mca, "verify_ms"), 2)
    # what Flock's sample on the first commitment costs the baseline, and BEEP-Ligerito against that baseline
    N["100:first-sample-prove-ratio"] = rng(ratios(100, mca_first, mca, "prove_expected_ms"), 2)
    N["100:first-sample-nopow-ratio"] = rng(ratios(100, mca_first, mca, "prove_nopow_ms"), 2)
    N["100:first-sample-bytes"] = rng([rows[(f"m{mu}-100", mca_first)]["proof_bytes"] - rows[(f"m{mu}-100", mca)]["proof_bytes"]
                                       for mu in SIZES], 0)
    N["100s:prove-ratio"] = rng(ratios(100, beep, mca_first, "prove_expected_ms"), 2)
    N["100s:nopow-ratio"] = rng(ratios(100, beep, mca_first, "prove_nopow_ms"), 2)
    # the absolute cost of the samples: BEEP-Ligerito at the slack of the baseline, without proofs of work
    N["100:samples-ms"] = rng([rows[(f"m{mu}-100", beep02)]["prove_nopow_ms"] - rows[(f"m{mu}-100", mca)]["prove_nopow_ms"]
                               for mu in SIZES], 2)
    N["100:mca-pow-ms"] = rng([rows[(f"m{mu}-100", mca)]["pow_expected_ms"] for mu in SIZES], 2)
    # grinding
    N["100:mca-fold-grind"] = rng([g for mu in SIZES for g in rows[(f"m{mu}-100", mca)]["config"]["fold_grinding_bits"][:1]], 0)
    # the same as log2 of the expected hashes of the search (a threshold, not a whole number of bits)
    N["100:mca-fold-grind-log2"] = rng([log2(rows[(f"m{mu}-100", mca)]["config"]["grinds"]["fold_rounds"][0][0]["work"])
                                        for mu in SIZES], 1)
    N["128:beep-fold-grind-log2"] = rng([log2(g["work"]) for mu in SIZES
                                         for g in rows[(f"m{mu}-128", beep)]["config"]["grinds"]["fold"]], 1)
    # the ratios of the prover times with the proofs of work as they happened (the medians of the processes that
    # did them), next to those of "prove": a check of the model of the proofs of work
    N["100:prove-ratio-measured"] = rng(ratios(100, beep, mca, "prove_ms"), 2)
    N["128:prove-ratio-measured"] = rng(ratios(128, beep, "split", "prove_ms"), 2)
    N["100:mca-hashes-k"] = rng([rows[(f"m{mu}-100", mca)]["pow_expected_hashes"] / 1e3 for mu in SIZES], 0)
    # the fold searches of the baseline, against the first round's search repeated in every round (Flock's
    # convention for a level): the share of the hashes that the schedule per round tries
    shares = []
    for mu in SIZES:
        cfg = rows[(f"m{mu}-100", mca)]["config"]
        per_round = sum(g["work"] for lvl in cfg["grinds"]["fold_rounds"] for g in lvl)
        per_level = sum(len(lvl) * lvl[0]["work"] for lvl in cfg["grinds"]["fold_rounds"])
        shares.append(100 * per_round / per_level)
    N["100:mca-round-schedule-pct"] = rng(shares, 0)
    N["100:slower-count"] = str(sum(x > 1 for x in ratios(100, beep, mca, "prove_expected_ms")))
    N["100:sizes"] = str(len(SIZES))
    N["100:beep-hashes"] = rng([rows[(f"m{mu}-100", beep)]["pow_expected_hashes"] for mu in SIZES], 0)
    N["128:beep-fold-grind"] = rng_up([log2(max(lv["fold_numerator"], 1))
                                   for mu in SIZES for lv in rows[(f"m{mu}-128", beep)]["config"]["levels"]], 0)
    N["128:beep-hashes-m"] = rng([rows[(f"m{mu}-128", beep)]["pow_expected_hashes"] / 1e6 for mu in SIZES], 2)
    N["128:flock-hashes-m"] = rng([rows[(f"m{mu}-128", 'split')]["pow_expected_hashes"] / 1e6 for mu in SIZES], 2)
    N["128:pow-share-pct"] = rng([100 * rows[(f"m{mu}-128", beep)]["pow_expected_ms"] / rows[(f"m{mu}-128", beep)]["prove_expected_ms"]
                                  for mu in SIZES], 0)
    N["128:flock-pow-share-pct"] = rng([100 * rows[(f"m{mu}-128", "split")]["pow_expected_ms"]
                                        / rows[(f"m{mu}-128", "split")]["prove_expected_ms"] for mu in SIZES], 0)

    # the proofs of work by kind of search (collect.py, `pow_expected_ms_by_kind`): the fold challenges alone
    def kind_share(cell, variant, kind):
        r = rows[(cell, variant)]
        by = r.get("pow_expected_ms_by_kind")
        if not by:
            fail(f"{cell} {variant}: no proofs of work by kind (collect.py of November 16, 2026 or later)")
        return 100 * by[kind] / r["prove_expected_ms"]

    N["128:fold-pow-share-pct"] = rng([kind_share(f"m{mu}-128", beep, "fold") for mu in SIZES], 0)
    N["128:query-pow-share-pct"] = rng([kind_share(f"m{mu}-128", beep, "queries") for mu in SIZES], 0)
    N["100:mca-fold-pow-share-pct"] = rng([kind_share(f"m{mu}-100", mca, "fold") for mu in SIZES], 0)
    # the levels of the two ladders at 128 bits: where Flock's has one more
    more = [len(rows[(f"m{mu}-128", "split")]["config"]["log_inv_rates"]) - len(rows[(f"m{mu}-128", beep)]["config"]["log_inv_rates"])
            for mu in SIZES]
    if any(x not in (0, 1) for x in more):
        fail(f"levels of Flock's ladder beyond those of BEEP-Ligerito: {more}")
    N["128:fewer-levels"] = str(sum(more))
    # the queries per level: BEEP-Ligerito makes fewer at every level that the two ladders share
    for mu in SIZES:
        qb, qs = rows[(f"m{mu}-128", beep)]["config"]["queries"], rows[(f"m{mu}-128", "split")]["config"]["queries"]
        if not all(x < y for x, y in zip(qb, qs)):
            fail(f"m{mu}-128: queries {qb} (Flock: {qs})")
    # examples at the largest size
    last = SIZES[-1]
    for bits, variants in ((100, ("split", mca, beep)), (128, ("split", beep))):
        for v in variants:
            r = rows[(f"m{last}-{bits}", v)]
            tag = {"split": "flock", mca: "lig", beep: "beep"}[v]
            N[f"ex:{bits}:{tag}:kib"] = m(kib(r["proof_bytes"]))
            N[f"ex:{bits}:{tag}:prove"] = m(ms(r["prove_expected_ms"]))
            N[f"ex:{bits}:{tag}:verify"] = m(fmt(r["verify_ms"], 2))
    N["commit:range"] = rng([commit_of(rows, f"m{mu}-{b}") for mu in SIZES for b in (100, 128)], 1)
    # how well "prove" (no proofs of work + their expected cost) agrees with the measured times
    resid = [abs(r["pow_model_residual_ms"]) / r["prove_expected_ms"] * 100 for r in data["rows"]
             if r.get("pow_model_residual_ms") is not None and r["variant"] in ("split", mca, beep)
             and r["prove_expected_ms"] >= 2]
    N["run:residual-pct-max"] = m(fmt(up(max(resid), 0), 0)) if resid else "?"
    # levels of the ladders
    N["ladder:levels"] = rng([len(rows[(f"m{mu}-128", beep)]["config"]["log_inv_rates"]) for mu in SIZES], 0)
    N["ladder:levels-flock"] = rng([len(rows[(f"m{mu}-128", 'split')]["config"]["log_inv_rates"]) for mu in SIZES], 0)

    out = {
        "generated_by": "paper/scripts/minimal_tables.py",
        "run": option("--results") or RUN,
        "binaries": data.get("binaries", []),
        "numbers": N,
        "tables": T,
        "errors_info": info,
        "warnings": WARNINGS,
    }
    target = Path(option("--out") or PAPER / "tables" / "minimal.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(f"wrote {target}: {len(N)} numbers, {len(T)} tables, {len(WARNINGS)} warnings")
    if "--readme" in sys.argv or "--write-readme" in sys.argv:
        block = readme_block(N, T, out["run"], checked, checked_mca)
        if "--readme" in sys.argv:
            print(block)
        if "--write-readme" in sys.argv:
            readme = BEEP_LIGERITO / "README.md"
            text = readme.read_text()
            if text.count(README_BEGIN) != 1 or text.count(README_END) != 1:
                fail(f"{readme} must have the two markers of the generated block once each")
            a, b = text.index(README_BEGIN), text.index(README_END) + len(README_END)
            readme.write_text(text[:a] + block + text[b:])
            print(f"wrote the generated block of {readme}")
    if "--print" in sys.argv:
        for name, table in T.items():
            print(f"\n== {name}")
            for line in table:
                print("  " + " | ".join(c.strip("$") for c in line))
        print()
        for key in sorted(N):
            print(f"  {key:28} {N[key]}")


if __name__ == "__main__":
    main()
