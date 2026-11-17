#!/usr/bin/env python3
"""The tables and the numbers of the section "Instantiation and Experiments" of the BEEP paper, at 128 bits.

[AI-drafted (claude-fable-5-2), 2026-11-17, at the author's request ("Ok let's do 128 bits only", after the
comparison with the MCA bound of DKT26 showed no gain in proof size at 100 bits; and, for the sizes, "go from
n=14 to n=26 doing only even n's"); research, unaudited; please review]

    python3 scripts/tables128.py            (from the folder `paper`; writes tables/tables128.json)
    python3 scripts/tables128.py --print    (also prints every table and every number)

It takes the place of scripts/minimal_tables.py, which wrote the section of November 16 (a table at 100 bits and
one at 128 bits, for 2^15 to 2^23 elements, with Flock's MCA bound in the table of errors). That script and its
tables/minimal.json are kept as the record of that section; main.typ no longer reads them.

It reads three runs of `beep-ligerito/bench_results` (written by `beep-ligerito/scripts/collect.py`):

  * RUN, the cells of `beep-ligerito/scripts/cells_dkt.txt` (2^14 to 2^26 elements, 100 and 128 bits);
  * RERUNS, later measurements of some of its cells, whose rows replace those of RUN;
  * AGAIN, a second measurement of the cells at 128 bits that the table uses: only for the sentence on how far
    the prover times of the two measurements are.

No number of the section is typed by hand: the section reads `tables/tables128.json` through `num("key")` and
`exptable(.., "name")`.

What it rechecks before it writes anything (a failure stops it; a WARNING is printed and written to the file):

  * every level of BEEP-Ligerito that the section uses, in exact integer arithmetic (`beep_params.check_level`,
    `check_grinds`);
  * every level of the baseline "Ligerito over GF(2^128)" with the bound of DKT26 (`dkt-<eta>`): the count of
    Theorem 4.4 of DKT26 computed twice here (in integers, and from the statement of the theorem with 80-digit
    decimals and exact fractions), its fold numerator `count + ceil(2L)`, its proofs of work, its queries, and
    that it has the ladder of BEEP-Ligerito at the same slack;
  * the shapes that the section states (rows per level, rates, block lengths against Flock's, levels);
  * that every process ended with status ok on AC power, and which processes had part of their memory
    compressed: the cells of the table that come from such a process carry a dagger, and the ranges of the
    prose leave their rows out;
  * that the second measurement has the same proof sizes and configurations (its bench binary is a rebuild of
    the first one after an edit of the test module of beep.rs: the same configurations, checked here row by row).

Rounding. Bits of security are rounded down. In a range "a to b" the lower end is rounded down and the upper
end up, so that every value of the range lies between the two numbers that are printed.

Standard library only; runs on Python 3.9.
"""
import json
import re
import statistics
import sys
from decimal import ROUND_CEILING, Decimal, getcontext
from fractions import Fraction
from math import ceil, floor, isqrt, log2, sqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent
BEEP_LIGERITO = PAPER.parent / "beep-ligerito"
sys.path.insert(0, str(BEEP_LIGERITO / "scripts"))
import beep_params as bp  # noqa: E402

RUN = "three-way-dkt-20261117"
RERUNS = ("three-way-dkt-20261117-m16",)   # the nine cells for 2^16 elements, measured again (see the WORKLOG)
AGAIN = "three-way-dkt-20261117-again128"  # a second measurement of the cells at 128 bits of the table
SIZES = [14, 16, 18, 20, 22, 24, 26]       # log2 of the number of elements of the message
ETA_BEEP, ETA_LIG = "0.001", "0.02"        # the slack of BEEP-Ligerito, and that of Flock's Ligerito
DKT_ETAS = ("0.02", "0.05", "0.1")         # the slacks of the baseline with the bound of DKT26 at 128 bits
LOW_BITS, LOW_ETA = 100, "0.002"           # the remark on a lower security level
QBITS = 128
# A row is reported as disturbed if a repetition without proofs of work takes more than SPREAD times the median
# of its repetitions, or if the measured time with proofs of work differs from "prove" by more than RESIDUAL
# (for proofs of MIN_MS or more).
SPREAD, RESIDUAL, MIN_MS = 1.5, 0.10, 2.0

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


def rng_down(values, digits):
    """'a to b' with both ends rounded down (bits of security: every value is at least what is printed)."""
    lo, hi = fmt(down(min(values), digits), digits), fmt(down(max(values), digits), digits)
    return f"${lo}$" if lo == hi else f"${lo}$ to ${hi}$"


def rng_up(values, digits):
    """'a to b' with both ends rounded up (bits of grinding: the least number that suffices)."""
    lo, hi = fmt(up(min(values), digits), digits), fmt(up(max(values), digits), digits)
    return f"${lo}$" if lo == hi else f"${lo}$ to ${hi}$"


def ms(x):
    """Milliseconds: two decimals below 10 ms, one above."""
    return fmt(x, 2) if x < 9.995 else fmt(x, 1)


def kib(nbytes):
    return fmt(nbytes / 1024, 1)


def pow2(e):
    return f"$2^({e})$"


def one_of(values):
    vals = sorted(set(values))
    return " or ".join(m(v) for v in vals)


# ------------------------------------------------------------------ the runs
def read_run(name):
    path = BEEP_LIGERITO / "bench_results" / name / "results.json"
    if not path.exists():
        fail(f"no {path}: run beep-ligerito/scripts/collect.py on the run first")
    return json.loads(path.read_text())


def load():
    """The rows of RUN, with those of RERUNS in place of the rows of the same processes, as (bits, mu, variant)
    -> row; the processes as name -> cell; and the folder that every process is read from."""
    rows, cells, source = {}, {}, {}
    main = read_run(RUN)
    for name in (RUN,) + RERUNS:
        data = main if name == RUN else read_run(name)
        for w in data.get("warnings", []):
            warn(f"collect.py ({name}): {w}")
        for proc, cell in data["cells"].items():
            cells[proc], source[proc] = cell, name
        for r in data["rows"]:
            mt = re.fullmatch(r"m(\d+)-(\d+)", r["cell"])
            rows[(int(mt.group(2)), int(mt.group(1)), r["variant"])] = r
    return main, rows, cells, source


def results_of(folder, proc):
    """The RESULT lines of one process, as variant -> result (for a cell that only ran without proofs of work,
    for which collect.py makes no row)."""
    out = {}
    path = BEEP_LIGERITO / "bench_results" / folder / "cells" / f"{proc}.out"
    if not path.exists():
        fail(f"no {path}")
    for line in path.read_text().splitlines():
        if line.startswith("RESULT "):
            r = json.loads(line[7:])
            out[r["variant"]] = r
    return out


def check_run(cells):
    """Every process that the section uses: status ok, AC power. Returns the processes with part of their memory
    compressed or swapped."""
    expected = []
    for mu in SIZES:
        expected += [f"m{mu}-128.{p}{s}" for p in ("fold", "split") for s in ("", "-nopow")] + [f"m{mu}-128.dkt-nopow"]
        expected += [f"m{mu}-{LOW_BITS}.fold", f"m{mu}-{LOW_BITS}.fold-nopow"]
    missing = sorted(set(expected) - set(cells))
    if missing:
        fail(f"processes missing from the run: {missing}")
    limited = []
    for name in expected + [n for n in cells if n.endswith(".dkt")]:
        c = cells[name]
        if c["status"] != "ok":
            fail(f"process {name}: status {c['status']}")
        for key in ("power_before", "power_after"):
            if not c["meta"].get(key, "").startswith("AC"):
                fail(f"process {name}: {key} = {c['meta'].get(key)!r}")
        t = c.get("time", {})
        fp, rss = t.get("peak_footprint_bytes"), t.get("max_rss_bytes")
        if fp and rss and fp > 1.02 * rss and fp - rss > 32 << 20:
            limited.append(name)
    return limited


def disturbed_by_memory(row, limited):
    return row["process"] in limited or row["process"] + "-nopow" in limited


def stability(table_rows):
    """Rows of the table with a slow repetition or a measured time far from "prove" (see SPREAD, RESIDUAL)."""
    out, spreads, resids = [], [], []
    for r in table_rows:
        if r["prove_expected_ms"] < MIN_MS:
            continue
        reps = sorted(r.get("prove_nopow_ms_reps") or [])
        spread = reps[-1] / reps[len(reps) // 2] if reps else 1.0
        resid = abs(r.get("pow_model_residual_ms") or 0.0) / r["prove_expected_ms"]
        spreads.append(spread)
        resids.append(resid)
        if spread > SPREAD or resid > RESIDUAL:
            out.append(f"{r['cell']} {r['variant']} (slowest repetition {spread:.2f} times the median; measured "
                       f"with proofs of work {100 * resid:.0f} % from \"prove\")")
    return out, max(spreads), max(resids)


def machine_state(cells, names):
    """Idle CPU (%) and unused memory (GB) right before each of the processes, from the `top` line of its meta."""
    idle, unused = [], []
    for name in names:
        top = cells[name]["meta"].get("top_before", "")
        if "% idle" in top:
            idle.append(float(top.split("% idle")[0].split()[-1]))
        if "unused" in top:
            word = top.split(" unused")[0].split()[-1]
            unused.append(float(word[:-1]) * {"M": 1 / 1024, "G": 1.0}[word[-1]])
    return idle, unused


# ------------------------------------------------------------------ exact arithmetic
def dkt_count(n, dim, agreement):
    """The count of DKT26 (ePrint 2026/2056), Theorem 4.4, in integers, as `dkt_exceptional_count` of beep.rs:
    D = dim - 1, m the least integer >= 3 with 4 m^2 A^2 >= (2m+1)^2 D n, B_jet the largest integer with
    4 D B_jet^2 < (2m+1)^2 n, B_Z the largest one with 12 D B_Z < (2m+1)^2 n, and
    (2 B_jet - 1) B_Z + ceil((n - D)(B_jet + B_Z Psi)/(A - D)) + (n - D - 1) B_jet,
    Psi = 1 + (2D - 1)(2 B_jet - 1) + 2 (B_jet - 2D - 1)_+. Returns (count, m)."""
    D, A = dim - 1, agreement
    if not (1 <= D <= n - 2 and A <= n and A * A > n * D):
        fail(f"no bound of DKT26 for n = {n}, dimension {dim}, agreement {A}")
    mm = 3
    while 4 * mm * mm * A * A < (2 * mm + 1) ** 2 * D * n:
        mm += 1
    t2n = (2 * mm + 1) ** 2 * n
    b_jet = isqrt((t2n - 1) // (4 * D))
    b_z = (t2n - 1) // (12 * D)
    psi = 1 + (2 * D - 1) * (2 * b_jet - 1) + 2 * max(b_jet - 2 * D - 1, 0)
    off = -((-(n - D) * (b_jet + b_z * psi)) // (A - D))
    return (2 * b_jet - 1) * b_z + off + (n - D - 1) * b_jet, mm


def dkt_count_statement(n, dim, agreement):
    """The same count from the statement of the theorem (its equations (33), (36), (37), (39)): the real
    quantities with 80-digit decimals, the count as an exact fraction, rounded up. Returns (count, m, closed),
    with `closed` the closed form (8/3) n t^3 n / D that the theorem states as a strict upper bound."""
    getcontext().prec = 80
    ceil_dec = lambda x: int(x.to_integral_value(rounding=ROUND_CEILING))
    D, A = dim - 1, agreement
    rho_minus = Decimal(D) / Decimal(n)
    s = rho_minus.sqrt()
    eta0 = Decimal(A) / Decimal(n) - s
    mm = max(ceil_dec(s / (2 * eta0)), 3)
    t = Decimal(mm) + Decimal(1) / 2
    b_jet = ceil_dec(t / s) - 1
    b_z = ceil_dec(t * t / (3 * rho_minus)) - 1
    psi = 1 + (2 * D - 1) * (2 * b_jet - 1) + 2 * max(b_jet - 2 * D - 1, 0)
    count = (2 * b_jet - 1) * b_z + Fraction(n - D, A - D) * (b_jet + b_z * psi) + (n - D - 1) * b_jet
    closed = Fraction(8, 3) * n * Fraction(2 * mm + 1, 2) ** 3 * Fraction(n, D)
    if not count < closed:
        fail(f"the count of DKT26 is not below its closed form (n = {n}, dimension {dim}, agreement {A})")
    return ceil(count), mm, closed


def two_lists(rate, eta):
    """ceil(2 L) for the real Johnson bound L = 1/(2 eta sqrt(rho)): the least integer v with (v eta)^2 >= 2^rate."""
    eta = bp.frac(eta)
    v = int(1 / (float(eta) * 2.0 ** (-rate / 2)))
    ok = lambda x: (x * eta) ** 2 >= 2 ** rate
    while ok(v - 1):
        v -= 1
    while not ok(v):
        v += 1
    return v


def dkt_numerator(c, rate, eta):
    """The numerator of a fold challenge of the baseline with the bound of DKT26, for a level of rate 2^-rate
    with 2^c message columns at slack eta: count + ceil(2L), at the agreement ceil((sqrt(rho) + eta) n)."""
    n = 1 << (c + rate)
    agreement = bp.agreement(n, rate, eta)
    count, mm = dkt_count(n, 1 << c, agreement)
    count2, mm2, _ = dkt_count_statement(n, 1 << c, agreement)
    if (count, mm) != (count2, mm2):
        fail(f"the two computations of the count of DKT26 differ (n = 2^{c + rate}, rate 2^-{rate}, eta {eta})")
    return count + two_lists(rate, eta), agreement


def flock_numerator(n, rate, eta, folds):
    """Flock's numerator of a fold under MCA (its Appendix C.3), as in scripts/minimal_tables.py: the bound of
    BCHKS25, Theorem 4.6, a = (2 r^5 + 3 r gamma rho)/(3 rho^(3/2)) n + r/sqrt(rho) with r = max(ceil(sqrt(rho)
    /(2 eta)), 3) + 1/2 and gamma = 1 - sqrt(rho) - eta, times the row union 2^(folds - 1) of the first round of
    a level with 2^folds rows. Floats, as in flock-core (`paper_johnson_log_a`)."""
    rho, eta = 2.0 ** -rate, float(bp.frac(eta))
    r = max(ceil(sqrt(rho) / (2 * eta)), 3) + 0.5
    gamma = 1 - sqrt(rho) - eta
    a = (2 * r ** 5 + 3 * r * gamma * rho) / (3 * rho ** 1.5) * n + r / sqrt(rho)
    return a * 2.0 ** max(folds - 1, 0)


def check_beep_config(label, cfg, lam, seen):
    """`beep_params.check_level` and `check_grinds` on a configuration of BEEP-Ligerito. Returns the failures."""
    failures = []
    levels = cfg["levels"]
    for li, lv in enumerate(levels):
        nxt = levels[li + 1] if li + 1 < len(levels) else None
        key = json.dumps([lam, li, lv, nxt and nxt["list_size"], cfg.get("grinds") if li == 0 else None], sort_keys=True)
        if key in seen:
            continue
        seen.add(key)
        bad = bp.check_level(lv, lam=lam, level_index=li, next_level=nxt, last=nxt is None)
        if li == 0:
            bad += bp.check_grinds(cfg, lam=lam)
        if bad:
            failures.append(f"{label} level {li}: " + "; ".join(bad))
    return failures


def check_dkt_config(label, cfg, beep_cfg, lam, seen):
    """A configuration of the baseline `dkt-<eta>` against the theorem and against BEEP-Ligerito at the same
    slack (`beep_cfg`, or None if the run has none). Returns the failures."""
    failures = []
    levels, grinds = cfg["levels"], cfg["grinds"]
    shift = 64 + QBITS - lam
    if "fold_rounds" in grinds or "fold_round_numerators" in cfg:
        failures.append(f"{label}: a numerator per round (the baseline with the bound of DKT26 has one per level)")
    if cfg["ood_samples"][0] != 0:
        failures.append(f"{label}: a sample on the first commitment")
    if beep_cfg is not None:
        for key in ("queries", "log_inv_rates", "initial_k", "recursive_ks", "recursive_log_msg_cols", "ood_samples",
                    "query_grinding_bits", "claim_batch_grinding_bits", "consistency_batch_grinding_bits"):
            if cfg[key] != beep_cfg[key]:
                failures.append(f"{label}: {key} differs from BEEP-Ligerito at the same slack")
        if grinds["claim"] != beep_cfg["grinds"]["claim"] or grinds["consistency"] != beep_cfg["grinds"]["consistency"]:
            failures.append(f"{label}: the batching proofs of work differ from BEEP-Ligerito at the same slack")
    for li, lv in enumerate(levels):
        key = json.dumps([lam, li, lv, grinds["fold"][li]], sort_keys=True)
        if key in seen:
            continue
        seen.add(key)
        bad = []
        rate, c = lv["log_inv_rate"], lv["log_msg_cols"]
        eta = bp.frac(repr(lv["eta"]))
        want, agreement = dkt_numerator(c, rate, eta)
        if lv["agreement"] != agreement:
            bad.append(f"agreement {lv['agreement']}, exact {agreement}")
        if lv["list_size"] != bp.johnson_list_simple(rate, eta):
            bad.append(f"list size {lv['list_size']}")
        if lv["fold_numerator"] != want:
            bad.append(f"fold numerator {lv['fold_numerator']}, recomputed {want}")
        if lv["samples"] != 0 or cfg["samples"][li] != 0:
            bad.append("the baseline has points")
        g = grinds["fold"][li]
        if g.get("target") is not None:
            if not want * g["target"] < 2 ** shift:
                bad.append(f"fold target {g['target']} does not cover the numerator")
            if want * (g["target"] + 1) < 2 ** shift:
                bad.append(f"fold target {g['target']} is not the largest one")
        elif not want < 2 ** (QBITS - lam + g["bits"]):
            bad.append(f"{g['bits']} fold bits do not cover the numerator")
        if bp.queries_are_least(lv["queries"], rate, eta, lv["query_grinding_bits"], lam) is not True:
            bad.append(f"queries {lv['queries']}")
        if bad:
            failures.append(f"{label} level {li}: " + "; ".join(bad))
    return failures


def check_shapes(rows):
    """The shapes that the section states: Flock's rows per level, the rates 1/2, 1/8, 1/32, ..., codewords as
    long as Flock's at every level, and a new level while the folded message has 2^7 elements or more."""
    for mu in SIZES:
        cfg = rows[(128, mu, f"beep-{ETA_BEEP}")]["config"]
        split = rows[(128, mu, "split")]["config"]
        levels = len(cfg["log_inv_rates"])
        if cfg["initial_k"] != split["initial_k"] or any(k != 4 for k in cfg["recursive_ks"]):
            fail(f"2^{mu}: rows per level {cfg['initial_k']}, {cfg['recursive_ks']} (Flock: {split['initial_k']})")
        if cfg["log_inv_rates"] != [1, 3, 5, 7, 9][:levels] or split["log_inv_rates"][:2] != [1, 2]:
            fail(f"2^{mu}: rates {cfg['log_inv_rates']} (Flock: {split['log_inv_rates']})")
        cols = lambda c: [mu - c["initial_k"]] + c["recursive_log_msg_cols"]
        ours = [a + b for a, b in zip(cols(cfg), cfg["log_inv_rates"])]
        flock = [a + b for a, b in zip(cols(split), split["log_inv_rates"])]
        if ours != flock[:len(ours)] or len(flock) < len(ours):
            fail(f"2^{mu}: block lengths 2^{ours} (Flock: 2^{flock})")
        last_cols = cfg["recursive_log_msg_cols"][-1]
        if not (last_cols + 4 >= 7 > last_cols):
            fail(f"2^{mu}: the last message has 2^{last_cols} elements")
        for eta in (ETA_LIG,):
            other = rows[(128, mu, f"beep-{eta}")]["config"]
            if any(other[k] != cfg[k] for k in ("log_inv_rates", "initial_k", "recursive_ks", "recursive_log_msg_cols")):
                fail(f"2^{mu}: BEEP-Ligerito at the two slacks must have the same ladder")


# ------------------------------------------------------------------ the tables
def error_table(rows, dkt128):
    """Table "errors": the first fold round of the first level of every instance, over a field of 2^128
    elements, for a target of 128 bits. The fold of Ligerito under MCA has the bound of DKT26 (no row union)."""
    out, info = [], []
    for mu in SIZES:
        beep = rows[(128, mu, f"beep-{ETA_BEEP}")]["config"]
        split = rows[(128, mu, "split")]["config"]
        lv = beep["levels"][0]
        rate, c, folds = lv["log_inv_rate"], lv["log_msg_cols"], lv["folds"]
        n = 1 << (c + rate)
        N, L, t, pts, var = lv["line_bound"], lv["list_size"], lv["threshold"], lv["samples"], lv["max_variables"]
        if not bp.points_reach(t, N, L, var, pts, 128, QBITS):
            fail(f"2^{mu}: the points of BEEP do not reach 128 bits")
        k1 = bp.points_bits(t, N, L, var, pts, QBITS)   # kappa_1(t)
        k2 = QBITS - log2(t - 1 + 2 * L)                 # kappa_2(t)
        if abs(k1 - lv["sample_bits"]) > 1e-6:
            fail(f"2^{mu}: kappa_1 {k1} here, {lv['sample_bits']} in the bench")
        num02, _ = dkt_numerator(c, rate, ETA_LIG)
        num001, _ = dkt_numerator(c, rate, ETA_BEEP)
        # the same numerators from the Rust side: the first level of the baseline at 128 bits (slack 0.02) and at
        # 100 bits (slack 0.001; the numerator of a level does not depend on the target)
        rust02 = dkt128[mu][f"dkt-{ETA_LIG}"]["config"]["levels"][0]
        rust001 = rows[(LOW_BITS, mu, f"dkt-{ETA_BEEP}")]["config"]["levels"][0]
        for rust, num in ((rust02, num02), (rust001, num001)):
            if (rust["log_msg_cols"], rust["log_inv_rate"], rust["folds"]) != (c, rate, folds):
                fail(f"2^{mu}: the baseline and BEEP do not have the same first level")
            if rust["fold_numerator"] != num:
                fail(f"2^{mu}: fold numerator of the baseline {rust['fold_numerator']} in the bench, {num} here")
        lig02, lig001 = QBITS - log2(num02), QBITS - log2(num001)
        # Flock's own accounting of the same round (BCHKS25 times the row union), from the run and from the formula
        flock02 = QBITS - log2(flock_numerator(n, rate, ETA_LIG, folds) + 2 / (2 * float(ETA_LIG) * 2.0 ** (-rate / 2)))
        rust_flock = rows[(LOW_BITS, mu, f"mcanf-{ETA_LIG}")]["config"]["levels"][0]
        if abs(rust_flock["fold_bits"] - flock02) > 1e-6:
            fail(f"2^{mu}: fold bits under Flock's bound {rust_flock['fold_bits']} in the bench, {flock02} here")
        q_lig, q_beep = split["queries"][0], beep["queries"][0]
        if (split["log_inv_rates"][0], split["initial_k"]) != (rate, folds):
            fail(f"2^{mu}: Flock's first level differs")
        if q_lig != bp.queries(rate, ETA_LIG, 16, 128) or q_beep != bp.queries(rate, ETA_BEEP, 16, 128):
            fail(f"2^{mu}: queries {q_lig}, {q_beep}")
        out.append([pow2(mu), pow2(folds), pow2(c + rate),
                    m(fmt(down(lig02, 1), 1)), m(fmt(down(lig001, 1), 1)), m(q_lig),
                    m(pts), m(fmt(down(k1, 1), 1)), m(fmt(down(k2, 1), 1)), m(q_beep)])
        info.append({"mu": mu, "folds": folds, "log_n": c + rate, "lig02": lig02, "lig001": lig001, "flock02": flock02,
                     "k1": k1, "k2": k2, "m": pts, "t": t, "N": N, "L": L, "q_lig": q_lig, "q_beep": q_beep,
                     "numerator02": num02, "numerator001": num001})
    return out, info


def commit_of(rows, mu):
    """The commitment, which every variant shares: the mean over the processes of the size at 128 bits."""
    vals = []
    for v in ("split", f"beep-{ETA_BEEP}"):
        r = rows[(128, mu, v)]
        vals += r.get("commit_ms_both") or [r["commit_ms"]]
    return sum(vals) / len(vals)


def measured_table(rows, variants, limited):
    out = []
    for mu in SIZES:
        line = [pow2(mu), m(ms(commit_of(rows, mu)))]
        for v in variants:
            r = rows[(128, mu, v)]
            mark = "^dagger" if disturbed_by_memory(r, limited) else ""
            line += [m(kib(r["proof_bytes"])), m(ms(r["prove_expected_ms"]) + mark), m(fmt(r["verify_ms"], 2) + mark)]
        out.append(line)
    return out


def main():
    data, rows, cells, source = load()
    limited = check_run(cells)
    if limited:
        warn(f"processes with part of their memory compressed or swapped: {limited}")
    check_shapes(rows)
    beep, beep02 = f"beep-{ETA_BEEP}", f"beep-{ETA_LIG}"
    table_variants = ("split", beep02, beep)

    # the baseline with the bound of DKT26 at 128 bits: its processes without proofs of work
    dkt128 = {mu: results_of(source[f"m{mu}-128.dkt-nopow"], f"m{mu}-128.dkt-nopow") for mu in SIZES}

    # ---- exact rechecks
    seen, failures = set(), []
    for mu in SIZES:
        for v in (beep, beep02):
            failures += check_beep_config(f"2^{mu} at 128 bits, {v}", rows[(128, mu, v)]["config"], 128, seen)
        failures += check_beep_config(f"2^{mu} at {LOW_BITS} bits, {beep}", rows[(LOW_BITS, mu, beep)]["config"], LOW_BITS, seen)
    checked_beep = len(seen)
    seen = set()
    for mu in SIZES:
        for eta in DKT_ETAS:
            same = dkt128[mu].get(f"beep-{eta}")
            failures += check_dkt_config(f"2^{mu} at 128 bits, dkt-{eta}", dkt128[mu][f"dkt-{eta}"]["config"],
                                         same and same["config"], 128, seen)
            if dkt128[mu][f"dkt-{eta}"]["config"]["target_bits"] != 128:
                fail(f"2^{mu}: dkt-{eta} of the cell at 128 bits has another target")
        for eta in (LOW_ETA, ETA_BEEP):
            same = rows.get((LOW_BITS, mu, f"beep-{eta}"))
            failures += check_dkt_config(f"2^{mu} at {LOW_BITS} bits, dkt-{eta}", rows[(LOW_BITS, mu, f"dkt-{eta}")]["config"],
                                         same and same["config"], LOW_BITS, seen)
    for f in failures:
        print("FAIL", f)
    if failures:
        fail(f"{len(failures)} levels fail their exact recheck")
    print(f"exact recheck: {checked_beep} levels of BEEP-Ligerito and {len(seen)} levels of the baseline, no failure")

    N, T = {}, {}
    T["errors"], info = error_table(rows, dkt128)
    T["bits128"] = measured_table(rows, table_variants, limited)

    # ---- the machine and the run
    mach = data["machine"]
    first = rows[(128, SIZES[0], "split")]
    N["run:name"] = RUN
    N["run:cpu"] = mach.get("machdep.cpu.brand_string", "?")
    N["run:memory-gb"] = str(round(int(mach.get("hw.memsize", 0)) / 2 ** 30))
    N["run:threads"] = str(first["threads"])
    N["run:reps"] = str(first["reps"])
    N["run:date"] = mach.get("date", "?")[:10]
    N["run:power"] = "on AC power"   # check_run fails otherwise
    table_procs = [f"m{mu}-128.{p}{s}" for mu in SIZES for p in ("fold", "split") for s in ("", "-nopow")]
    idle, unused = machine_state(cells, table_procs)
    N["run:idle-pct-min"] = m(fmt(down(min(idle), 0), 0))
    N["run:unused-gb"] = rng(unused, 1)
    N["run:processes"] = str(len(table_procs))
    N["run:limited"] = str(len([p for p in limited if p in table_procs]))
    the_rows = [rows[(128, mu, v)] for mu in SIZES for v in table_variants]
    for r in the_rows:
        if r["prove_expected_ms"] is None or r["verify_ms"] is None or r["config"].get("target_bits", 128) != 128:
            fail(f"{r['cell']} {r['variant']}: no prove or verify time, or another target")
    disturbed, spread_max, resid_max = stability(the_rows)
    for d in disturbed:
        warn(f"disturbed row: {d}")
    N["run:disturbed"] = str(len(disturbed))
    N["run:spread-max"] = m(fmt(up(spread_max, 2), 2))
    N["run:resid-pct-max"] = m(fmt(up(100 * resid_max, 0), 0))
    # the sizes whose rows of the table come from processes with all their memory: the ranges below are over them
    clean = [mu for mu in SIZES if not any(disturbed_by_memory(rows[(128, mu, v)], limited) for v in table_variants)]
    N["sizes:clean"] = str(len(clean))
    N["sizes:clean-last"] = pow2(clean[-1])
    N["sizes:dagger"] = " and ".join(pow2(mu) for mu in SIZES if mu not in clean) or "none"

    # ---- the second measurement: the same proof sizes and configurations, and how far "prove" is
    again_path = BEEP_LIGERITO / "bench_results" / AGAIN / "results.json"
    if again_path.exists():
        again = json.loads(again_path.read_text())
        again_limited = [name for name, c in again["cells"].items()
                         if (c.get("time", {}).get("peak_footprint_bytes") or 0) > 1.02 * (c.get("time", {}).get("max_rss_bytes") or 1)
                         and c["time"]["peak_footprint_bytes"] - c["time"]["max_rss_bytes"] > 32 << 20]
        theirs = {(r["cell"], r["variant"]): r for r in again["rows"]}
        ratios, vratios = [], []
        for r in the_rows:
            o = theirs.get((r["cell"], r["variant"]))
            if o is None:
                fail(f"{r['cell']} {r['variant']}: not in the second measurement")
            if o["proof_bytes"] != r["proof_bytes"] or o["config"] != r["config"]:
                fail(f"{r['cell']} {r['variant']}: the two measurements do not have the same proof size and configuration")
            if disturbed_by_memory(r, limited) or disturbed_by_memory(o, again_limited):
                continue
            vratios.append(o["verify_ms"] / r["verify_ms"])
            if r["prove_expected_ms"] >= MIN_MS:
                ratios.append(o["prove_expected_ms"] / r["prove_expected_ms"])
        # how far the second measurement is from the one of the table, in either direction
        away = lambda xs: 100 * max(max(x, 1 / x) - 1 for x in xs)
        N["again:name"] = AGAIN
        N["again:rows"] = str(len(ratios))
        N["again:prove-ratio"] = rng(ratios, 2)
        N["again:verify-ratio"] = rng(vratios, 2)
        N["run:noise-pct"] = m(fmt(up(away(ratios), 0), 0))
        N["run:verify-noise-pct"] = m(fmt(up(away(vratios), 0), 0))
        if again_limited:
            warn(f"second measurement: processes with part of their memory compressed or swapped: {sorted(again_limited)}")
    else:
        warn(f"no second measurement ({AGAIN})")

    N["params:qgrind"] = "16"
    N["eta:beep"], N["eta:lig"] = ETA_BEEP, ETA_LIG
    N["sizes:first"], N["sizes:last"] = pow2(SIZES[0]), pow2(SIZES[-1])
    N["sizes:count"] = str(len(SIZES))

    # ---- the errors
    N["err:lig02"] = rng_down([i["lig02"] for i in info], 1)
    N["err:lig001"] = rng_down([i["lig001"] for i in info], 1)
    N["err:beep2"] = rng_down([i["k2"] for i in info], 1)
    N["err:beep-grind-1"] = rng_up([128 - i["k2"] for i in info], 1)
    N["err:lig-grind-1"] = rng_up([128 - i["lig02"] for i in info], 1)
    N["err:q-lig"] = one_of(i["q_lig"] for i in info)
    N["err:q-beep"] = one_of(i["q_beep"] for i in info)
    # how many bits less the same round has under Flock's own accounting (BCHKS25 times the row union)
    N["err:flock-less"] = rng([i["lig02"] - i["flock02"] for i in info], 0)
    N["err:flock02"] = rng_down([i["flock02"] for i in info], 1)
    N["params:m-128"] = one_of(s for mu in SIZES for s in rows[(128, mu, beep)]["config"]["samples"])
    N["params:m-128-02"] = one_of(s for mu in SIZES for s in rows[(128, mu, beep02)]["config"]["samples"])
    levels = [len(rows[(128, mu, beep)]["config"]["log_inv_rates"]) for mu in SIZES]
    N["ladder:levels"] = rng(levels, 0)

    def ratios_of(a, b, key, sizes):
        f = key if callable(key) else (lambda r: r[key])
        return [f(rows[(128, mu, a)]) / f(rows[(128, mu, b)]) for mu in sizes]

    # ---- BEEP-Ligerito against Ligerito (Flock) at 128 bits: at Flock's slack (128e) and at its own (128)
    for v, tag in ((beep02, "128e"), (beep, "128")):
        size = ratios_of(v, "split", "proof_bytes", SIZES)
        N[f"{tag}:size-saving-pct"] = rng([100 * (1 - x) for x in size], 0)
        N[f"{tag}:prove-ratio"] = rng(ratios_of(v, "split", "prove_expected_ms", clean), 2)
        N[f"{tag}:verify-ratio"] = rng(ratios_of(v, "split", "verify_ms", clean), 2)
        N[f"{tag}:nopow-ratio"] = rng(ratios_of(v, "split", "prove_nopow_ms", clean), 2)
        N[f"{tag}:prove-ratio-all"] = rng(ratios_of(v, "split", "prove_expected_ms", SIZES), 2)
        N[f"{tag}:verify-ratio-all"] = rng(ratios_of(v, "split", "verify_ms", SIZES), 2)
        N[f"{tag}:fold-pow-share-pct"] = rng([100 * rows[(128, mu, v)]["pow_expected_ms_by_kind"]["fold"]
                                              / rows[(128, mu, v)]["prove_expected_ms"] for mu in SIZES], 0)
        N[f"{tag}:fold-grind-log2"] = rng([log2(g["work"]) for mu in SIZES
                                           for g in rows[(128, mu, v)]["config"]["grinds"]["fold"]], 1)
        N[f"{tag}:fold-hashes-log2"] = rng([log2(sum(g["work"] for g in rows[(128, mu, v)]["pow_grinds"]["fold"]))
                                            for mu in SIZES], 1)
        faster = [mu for mu, x in zip(SIZES, ratios_of(v, "split", "prove_expected_ms", SIZES)) if x < 1]
        N[f"{tag}:faster-count"] = str(len(faster))
    # the levels of the two ladders: where Flock's has more, and the queries per level
    more = [len(rows[(128, mu, "split")]["config"]["log_inv_rates"]) - l for mu, l in zip(SIZES, levels)]
    if any(x < 0 for x in more):
        fail(f"levels of Flock's ladder beyond those of BEEP-Ligerito: {more}")
    N["128:fewer-levels"] = str(sum(x > 0 for x in more))
    for mu in SIZES:
        qs = rows[(128, mu, "split")]["config"]["queries"]
        q02, q001 = rows[(128, mu, beep02)]["config"]["queries"], rows[(128, mu, beep)]["config"]["queries"]
        if not (q02[0] == qs[0] and all(x < y for x, y in zip(q02[1:], qs[1:])) and all(x < y for x, y in zip(q001, qs))):
            fail(f"2^{mu}: queries {q02}, {q001} (Flock: {qs})")

    # ---- Ligerito over GF(2^128) at 128 bits, with the bound of DKT26: what its fold challenges cost
    rates = [c["context"]["pow_hashes_per_ms_parallel"] for name, c in cells.items()
             if c.get("context") and c["context"].get("pow_hashes_per_ms_parallel")]
    rate_par = statistics.median(rates)
    N["run:hashes-per-s-m"] = m(fmt(down(rate_par * 1000 / 1e6, 0), 0))
    fold_hashes = lambda r: sum(g["work"] for g in r["pow_grinds"]["fold"])
    for eta in DKT_ETAS:
        tag = f"mca128:{eta}"
        res = [dkt128[mu][f"dkt-{eta}"] for mu in SIZES]
        N[f"{tag}:fold-hashes-log2"] = rng([log2(fold_hashes(r)) for r in res], 1)
        N[f"{tag}:fold-grind-log2"] = rng([log2(g["work"]) for r in res for g in r["config"]["grinds"]["fold"]], 1)
        # how much larger its proofs are than those of BEEP-Ligerito at the slack 0.001
        N[f"{tag}:size-more-pct"] = rng([100 * (r["proof_bytes"] / rows[(128, mu, beep)]["proof_bytes"] - 1)
                                         for mu, r in zip(SIZES, res)], 0)
        # the time of its searches at the hash rate of the run, in seconds: at the first and at the last size
        secs = [fold_hashes(r) / rate_par / 1000 for r in res]
        N[f"{tag}:search-s-first"] = m(fmt(secs[0], 2 if secs[0] < 1 else 1))
        N[f"{tag}:search-s-last"] = m(fmt(secs[-1], 0))
        N[f"{tag}:search-min-last"] = m(fmt(secs[-1] / 60, 0 if secs[-1] >= 600 else 1))
        # where a cell ran it with its proofs of work: the prover as measured (median), against BEEP-Ligerito
        for mu in SIZES:
            r = rows.get((128, mu, f"dkt-{eta}"))
            if r is not None:
                N[f"{tag}:measured-ms:{mu}"] = m(ms(r["prove_ms"]))
                N[f"{tag}:expected-ms:{mu}"] = m(ms(r["prove_expected_ms"]))
    for mu in SIZES:
        N[f"128:prove-ms:{mu}"] = m(ms(rows[(128, mu, beep)]["prove_expected_ms"]))

    # ---- a lower security level: at LOW_BITS bits the baseline with the bound of DKT26 has BEEP's proof size
    low = [(rows[(LOW_BITS, mu, f"dkt-{LOW_ETA}")], rows[(LOW_BITS, mu, beep)]) for mu in SIZES]
    N["low:bits"], N["low:eta"] = str(LOW_BITS), LOW_ETA
    N["low:size-diff-pct"] = m(fmt(up(max(abs(100 * (b["proof_bytes"] / a["proof_bytes"] - 1)) for a, b in low), 1), 1))
    N["low:prove-ratio"] = rng([b["prove_expected_ms"] / a["prove_expected_ms"] for a, b in low], 2)
    N["low:verify-ratio"] = rng([b["verify_ms"] / a["verify_ms"] for a, b in low], 2)
    N["low:fold-hashes-log2-max"] = m(fmt(up(max(log2(fold_hashes(a)) for a, _ in low), 1), 1))
    N["low:fold-hashes-max"] = pow2(fmt(up(max(log2(fold_hashes(a)) for a, _ in low), 1), 1))
    N["low:pow-ms-max"] = m(fmt(up(max(a["pow_expected_ms"] for a, _ in low), 1), 1))
    if any(fold_hashes(b) > 0 for _, b in low):
        fail("BEEP-Ligerito has a proof of work on a fold challenge at the lower security level")

    out = {
        "generated_by": "paper/scripts/tables128.py",
        "runs": [RUN, *RERUNS, AGAIN],
        "binaries": data.get("binaries", []),
        "numbers": N,
        "tables": T,
        "errors_info": info,
        "warnings": WARNINGS,
    }
    target = PAPER / "tables" / "tables128.json"
    target.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(f"wrote {target}: {len(N)} numbers, {len(T)} tables, {len(WARNINGS)} warnings")
    if "--print" in sys.argv:
        for name, table in T.items():
            print(f"\n== {name}")
            for line in table:
                print("  " + " | ".join(c.strip("$") for c in line))
        print()
        for key in sorted(N):
            print(f"  {key:32} {N[key]}")


if __name__ == "__main__":
    main()
