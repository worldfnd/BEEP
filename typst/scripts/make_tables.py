#!/usr/bin/env python3
"""The tables and the quoted numbers of the Experiments section of the BEEP paper (typst/deep+.typ).

[AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request; research, unaudited; please review]
[AI-revised (claude-fable-5-2), 2026-11-13: the run 20261113b (five variants, the affine ladder at its least
certified slack), the affine column from the wider search, the parts of a proof per level with the Merkle
leaves apart from the inner paths, and the proofs of work at the cost that the bench measures per search]
[AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: the run 20261113c, with smaller rates (ten
instances: rates 1/2 to 1/16); the numbers of the accounting variant `beepaff` (a BEEP ladder whose fold
challenges are charged the error of the affine fold), which no table of the paper uses; a check that every
number that the section quotes exists]
[AI-revised (claude-fable-5-2), 2026-11-14, at the author's request: the run 20261113e, with thirteen instances
(also 2^16 to 2^18 words); BEEP-Ligerito has no sample on its first commitment, a prover with one pass per fold
round, and proofs of work with a threshold, whose grinding is printed as log2 of the expected hashes; the time
table follows the new prover; a new table with what each of the three changes gives (`steps`)]
[AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("try to bring the affine version to a similar
level of optimization as BEEP", "remove the sample on the first commitment for the affine version"): the run
20261114g; the affine variant of the tables is now `anf` (`anf-small`) of the bench, i.e. Flock's affine ladder
with no out of domain sample on its first commitment and with our prover; Flock's affine variant as it ships
(`affine`, `affine-small`) and the two changes one at a time (`afast`, `anfref`) are in a new table (`asteps`);
the time table has the fold rounds of the affine prover; checks of what the text says about the provers, of the
configurations of the affine variants, and of the page faults of every process]
[AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("numbers for n=2^15 and rate 1/8 for table
4"): a fourteenth instance, `eighth15` (2^15 words, first level of rate 1/8); the rows of a folder `<run>-add*`
next to the run, with the same bench binary, are added for the shapes that the run does not have]
[AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("run experiments for 100 bits of security,
same parameter regimes as for 128 bits of security"): the tables `params100` and `main100` and the numbers
`100:...` of the run of the same cells at 100 bits (`measured_tables_100`), and what changes in the comparison of
one fold (`fold_numbers_100`); `load_run` is the part of `measured_tables` that reads a run]
[AI-revised (claude-fable-5-2), 2026-11-15, for the same request: the run at 100 bits is now `100bits-3`, made at
night with less unused memory than for the run at 128 bits. Which of its times can be used is decided by a rule
that was fixed before the run was read (page faults per proof, and the time without proofs of work against the
run at 128 bits), not by the flag for compressed memory; this rule is looser than the guard of the run at 128
bits, and the README says what would fail under that guard. The checks of its times that the text quotes
(against the times with proofs of work, between two processes, for the processes with compressed memory, single
proofs against medians); the smoke run before the campaign; `up` and `down`, which round a number that the text
quotes as a bound in the safe direction (six numbers of the run at 128 bits move by one unit)]

    python3 scripts/make_tables.py            # writes tables/experiments.json (from the folder typst/)
    python3 scripts/make_tables.py --print    # also prints every table and number
    python3 scripts/make_tables.py --results ../7-beep-ligerito/bench_results/three-way-<label>/results.json
    python3 scripts/make_tables.py --recompute   # run the fold comparison again (about a minute; it is cached
                                                 # in tables/fold_comparison.json, keyed by its two scripts)
    python3 scripts/make_tables.py --out PATH    # write somewhere else (a preview)
    python3 scripts/make_tables.py --results100 ../7-beep-ligerito/bench_results/three-way-<label>/results.json
                                                 # another run at 100 bits (default: the run 100bits-3)

The section reads tables/experiments.json: `tables` holds the rows of each table, as cells of Typst markup,
and `numbers` the numbers that the text quotes, by key. A key that is not there prints a red "pending" in the
paper, so no number of the section is typed by hand.

Two sources:
  * ../7-beep-ligerito/scripts/beep_params.py, for the error of one fold under each analysis (no measurement);
  * the results.json that ../7-beep-ligerito/scripts/collect.py writes for a run of the comparison of
    Ligerito variants (default: the run 20261114g). Without it the measured tables are empty and their
    numbers are pending.

The script prints a WARNING for every inconsistency that it finds (a BEEP level that fails the exact recheck,
proof sizes that differ between the two processes of a cell, a cell that did not run on AC power, a cell whose
peak footprint exceeds its resident memory, a prover that takes many page faults per proof, a statement of the
text about the provers that the run does not support). Standard library only; runs on Python 3.9.
"""
import hashlib
import importlib.util
import json
import sys
from math import ceil, floor, log2
from pathlib import Path

HERE = Path(__file__).resolve().parent
TYPST = HERE.parent
REPO = TYPST.parent
DEFAULT_RESULTS = REPO / "7-beep-ligerito" / "bench_results" / "three-way-20261114g" / "results.json"
OUT = TYPST / "tables" / "experiments.json"

spec = importlib.util.spec_from_file_location("beep_params", REPO / "7-beep-ligerito" / "scripts" / "beep_params.py")
bp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bp)

WARNINGS = []


def warn(msg):
    WARNINGS.append(msg)
    print("WARNING", msg)


# ------------------------------------------------------------------ formatting
def m(x):
    """A number in math mode."""
    return f"${x}$"


def f1(x):
    return f"{x:.1f}"


def up(x, digits=0):
    """`x` rounded up to `digits` decimals: for a number that the text quotes as an upper bound ("within",
    "at most", "below"), so that the sentence holds for the number as printed."""
    q = 10 ** digits
    return f"{ceil(x * q - 1e-9) / q:.{digits}f}"


def down(x, digits=0):
    """`x` rounded down to `digits` decimals: for a number that the text quotes as a lower bound ("at least")."""
    q = 10 ** digits
    return f"{floor(x * q + 1e-9) / q:.{digits}f}"


def bits(x):
    return m(f1(x)) if x is not None else "--"


def pow2(e):
    return f"$2^({e})$"


def rate(lr):
    return f"$1\\/{1 << lr}$"


def ms(x):
    if x is None:
        return None
    return f"{x:.1f}" if x < 100 else f"{x:.0f}"


def kib(nbytes):
    return f"{nbytes / 1024:.1f}"


def ratio(a, b):
    return f"{a / b:.2f}"


def rng(values, fmt=lambda v: f"{v:.2f}"):
    """A range `a to b`, or one value when both ends print the same."""
    lo, hi = fmt(min(values)), fmt(max(values))
    return lo if lo == hi else f"{lo} to {hi}"


# ------------------------------------------------------------------ the error of one fold (no measurement)
def comparison_rows(recompute=False, lam=128):
    """bp.comparison(), cached in tables/fold_comparison.json (tables/fold_comparison_<lam>.json for a target
    of `lam` bits other than 128): the search for the affine certificates takes a few minutes. The cache is
    keyed by the hashes of the two scripts that produce it."""
    sources = [REPO / "7-beep-ligerito" / "scripts" / "beep_params.py",
               REPO / "7-beep-ligerito" / "flock" / "scripts" / "affine_fold_params.py"]
    key = hashlib.sha256(b"".join(p.read_bytes() for p in sources)).hexdigest()
    cache = TYPST / "tables" / ("fold_comparison.json" if lam == 128 else f"fold_comparison_{lam}.json")
    if cache.exists() and not recompute:
        data = json.loads(cache.read_text())
        if data.get("sources_sha256") == key:
            rows = data["rows"]
            for r in rows:  # JSON turns the integer keys of this dict into strings
                r["beep_points_bits_at_least_threshold"] = {
                    int(k): v for k, v in r["beep_points_bits_at_least_threshold"].items()}
            return rows
    rows = bp.comparison(lam=lam)
    cache.parent.mkdir(exist_ok=True)
    cache.write_text(json.dumps({"generated_by": "typst/scripts/make_tables.py; do not edit by hand",
                                 "sources_sha256": key, "rows": rows}, indent=1, sort_keys=True) + "\n")
    return rows


def fold_tables(numbers, recompute=False):
    rows = comparison_rows(recompute)
    table = []
    last = None
    for r in rows:
        b = r["beep"]
        affine = r["affine_round_bits"]
        head = (r["log_n"], r["log_inv_rate"])
        first = head != last
        last = head
        table.append([
            pow2(r["log_n"]) if first else "",
            rate(r["log_inv_rate"]) if first else "",
            bits(r["udr_fold_bits"]) if first else "",
            m(r["eta"]),
            m(r["list_size"]),
            bits(r["bchks_bits"]),
            bits(r["dkt_bits"]),
            bits(r["deepfri_bits"]),
            bits(affine),
            m(b["samples"]),
            bits(b["sample_bits"]),
            bits(b["fold_bits"]),
        ])
    by_eta = lambda eta: [r for r in rows if r["eta"] == eta]
    for eta in bp.ETAS:
        sel = by_eta(eta)
        numbers[f"fold:bchks:{eta}"] = rng([r["bchks_bits"] for r in sel], f1)
        numbers[f"fold:dkt:{eta}"] = rng([r["dkt_bits"] for r in sel], f1)
        certified = [r for r in sel if r["affine_round_bits"] is not None]
        numbers[f"fold:affine-certified:{eta}"] = str(len(certified)) if certified else "none"
        shipped = [r for r in sel if r["affine_shipped_bits"] is not None]
        numbers[f"fold:affine-shipped:{eta}"] = str(len(shipped)) if shipped else "none"
        if certified:
            numbers[f"fold:affine:{eta}"] = rng([r["affine_round_bits"] for r in certified], f1)
            numbers[f"fold:affine-grind:{eta}"] = rng([r["affine_grinding_bits"] for r in certified], lambda v: str(v))
            numbers[f"fold:affine-points:{eta}"] = ", ".join(
                pow2(e) for e in sorted({r["log_n"] for r in certified}))
            # BEEP on the codes where the affine fold has a bound
            numbers[f"fold:beep-grind-there:{eta}"] = rng(
                [r["beep"]["fold_grinding_bits"] for r in certified], lambda v: str(v))
        for r in sel:  # the search never does worse than the script that Flock ships
            if r["affine_shipped_bits"] is not None and (
                    r["affine_script_bits"] is None or r["affine_script_bits"] < r["affine_shipped_bits"] - 1e-6):
                warn(f"fold comparison, {r['label']} at eta {eta}: the wider search is behind Flock's script")
        numbers[f"fold:beep-fold:{eta}"] = rng([r["beep"]["fold_bits"] for r in sel], f1)
        numbers[f"fold:beep-grind:{eta}"] = rng([r["beep"]["fold_grinding_bits"] for r in sel], lambda v: str(v))
        numbers[f"fold:beep-m:{eta}"] = rng([r["beep"]["samples"] for r in sel], lambda v: str(v))
    numbers["fold:shapes"] = str(len(bp.SHAPES))
    if numbers.get("fold:affine-certified:0.02") != str(len(bp.SHAPES)):
        warn("the text says that the affine fold has a bound for every code at eta = 0.02: no longer true")
    both = [r["affine_script_bits"] - r["affine_paper_bits"] for r in rows
            if r["affine_script_bits"] is not None and r["affine_paper_bits"] is not None]
    if both:
        numbers["fold:affine-paper-loss"] = rng(both, f1)
    if any((r["affine_script_bits"] is None) != (r["affine_paper_bits"] is None) for r in rows):
        warn("the two forms of the affine bound are not certified for the same codes: check the footnote")
    numbers["fold:affine-max-m"] = str(max(bp.AFFINE_MULTIPLICITIES))
    numbers["fold:beep-vs-udr"] = f1(max(r["udr_fold_bits"] - r["beep"]["fold_bits"] for r in rows))
    numbers["fold:rows"] = str(len(rows))
    numbers["fold:deepfri"] = rng([r["deepfri_bits"] for r in rows], f1)
    numbers["fold:deepfri-max"] = f1(max(r["deepfri_bits"] for r in rows))
    numbers["fold:beep-m"] = rng([r["beep"]["samples"] for r in rows], lambda v: str(v))
    numbers["fold:points3-max"] = up(max(r["beep_points_bits_at_least_threshold"][3] for r in rows), 1)
    numbers["fold:udr"] = rng([r["udr_fold_bits"] for r in rows], f1)
    numbers["fold:beep-fold"] = rng([r["beep"]["fold_bits"] for r in rows], f1)
    numbers["fold:beep-points-min"] = down(min(r["beep"]["sample_bits"] for r in rows), 1)
    numbers["fold:beep-grind"] = rng([r["beep"]["fold_grinding_bits"] for r in rows], lambda v: str(v))
    numbers["fold:affine-grind"] = rng(
        [r["affine_grinding_bits"] for r in rows if r["affine_grinding_bits"] is not None], lambda v: str(v))
    numbers["fold:affine-uncertified"] = str(sum(1 for r in rows if r["affine_round_bits"] is None))
    numbers["fold:points3"] = rng([r["beep_points_bits_at_least_threshold"][3] for r in rows], f1)
    numbers["fold:points4"] = rng([r["beep_points_bits_at_least_threshold"][4] for r in rows], f1)
    numbers["fold:points5"] = rng([r["beep_points_bits_at_least_threshold"][5] for r in rows], f1)
    # the example that the text walks through: level 0 of 2^24 words at rate 1/2
    ex = {r["eta"]: r for r in rows if (r["log_n"], r["log_inv_rate"]) == (19, 1)}
    for eta, r in ex.items():
        numbers[f"ex:queries:{eta}"] = str(r["queries"])
        numbers[f"ex:list:{eta}"] = str(r["list_size"])
        numbers[f"ex:bchks:{eta}"] = f1(r["bchks_bits"])
        numbers[f"ex:dkt:{eta}"] = f1(r["dkt_bits"])
        numbers[f"ex:beep-points:{eta}"] = f1(r["beep"]["sample_bits"])
        numbers[f"ex:beep-fold:{eta}"] = f1(r["beep"]["fold_bits"])
        numbers[f"ex:beep-m:{eta}"] = str(r["beep"]["samples"])
        numbers[f"ex:beep-grind:{eta}"] = str(r["beep"]["fold_grinding_bits"])
        if r["affine_round_bits"] is not None:
            numbers[f"ex:affine:{eta}"] = f1(r["affine_round_bits"])
            numbers[f"ex:affine-grind:{eta}"] = str(r["affine_grinding_bits"])
    any_row = next(iter(ex.values()))
    numbers["ex:udr-queries"] = str(any_row["udr_queries"])
    numbers["ex:udr-fold"] = f1(any_row["udr_fold_bits"])
    numbers["ex:line-bound-log"] = f1(log2(ex["0.02"]["line_bound"]))

    # BEEP over larger fields: what the rule selects
    fields = []
    for qbits in (128, 192, 256):
        first = True
        for label, ln, lr, c, mu in (bp.SHAPES[1], bp.SHAPES[3]):
            for eta in ("0.02", "0.001"):
                lv = bp.beep_level(ln, lr, mu, eta, 128, qbits)
                sel = lv["selected"]
                fields.append([
                    pow2(qbits) if first else "",
                    pow2(ln), rate(lr), m(eta),
                    m(sel["samples"]),
                    bits(log2(sel["threshold"])),
                    bits(sel["sample_bits"]),
                    bits(sel["fold_bits"]),
                    m(sel["fold_grinding_bits"]),
                ])
                first = False
                numbers[f"fields:m:{qbits}:{ln}:{eta}"] = str(sel["samples"])
                numbers[f"fields:grind:{qbits}:{ln}:{eta}"] = str(sel["fold_grinding_bits"])
    for qbits in (128, 192, 256):
        ms_ = [int(v) for k, v in numbers.items() if k.startswith(f"fields:m:{qbits}:")]
        gs = [int(v) for k, v in numbers.items() if k.startswith(f"fields:grind:{qbits}:")]
        numbers[f"fields:m:{qbits}"] = rng(ms_, lambda v: str(v))
        numbers[f"fields:grind:{qbits}"] = rng(gs, lambda v: str(v))
    return {"fold": table, "fields": fields}


# ------------------------------------------------------------------ the measured comparison
# The affine variant of the tables is `anf` of the bench (since the run 20261114g): Flock's affine ladder with no
# out of domain sample on its first commitment (the fold rounds of its first level are then ground for the list
# of the code) and with our prover, which makes one pass per fold round. `anf-small` is the same at the least
# slack of each level. Flock's affine variant as it ships is `affine` (`affine-small`); `afast` has our prover
# alone and `anfref` the missing sample alone (the table `asteps`).
AFFINE, AFFINE_SMALL = "anf", "anf-small"
VARIANTS = [("split", "Ligerito (Flock)"),
            (AFFINE, "affine, $eta = 0.02$"),
            (AFFINE_SMALL, "affine, least $eta$"),
            ("beep-0.02", "BEEP, $eta = 0.02$"),
            ("beep-0.001", "BEEP, $eta = 0.001$")]
# The four affine provers of the bench at one slack, in the order of the table `asteps`: Flock's variant as it
# ships, with our prover, without the sample on the first commitment, and with both changes. With the suffix
# `-small` they run at the least slack of each level.
AFFINE_STEPS = ["affine", "afast", "anfref", "anf"]
AFFINE_SUFFIXES = [("", "0.02"), ("-small", "least")]
# (out of domain samples on the first commitment, our prover) of each of them
AFFINE_KIND = {"affine": (1, False), "afast": (1, True), "anfref": (0, False), "anf": (0, True)}
FLOCK_AFFINE_PROVER = tuple(f + s for f, (_, ours) in AFFINE_KIND.items() if not ours for s, _ in AFFINE_SUFFIXES)
OUR_AFFINE_PROVER = tuple(f + s for f, (_, ours) in AFFINE_KIND.items() if ours for s, _ in AFFINE_SUFFIXES)
# A prover of ours that takes this many page faults per proof (median of its repetitions) ran short of memory:
# with enough free memory it takes fewer than ten. For Flock's provers, which allocate tables in every proof,
# the limit is this plus twice the pages of a message.
FAULTS_PER_PROOF_MAX = 100
PAGE_BYTES = 16384
# The instances, in the order of the tables: by rate, then by size.
CELLS = ["fast16", "fast17", "fast18", "fast20", "fast22", "fast24", "fast25", "slim22", "slim24",
         "eighth15", "eighth22", "eighth24", "sixteenth22", "sixteenth24"]
MAIN_CELL = "fast24"
# The variants of the bench that undo one change of BEEP-Ligerito each (run 20261113e), for the table `steps`:
# `beepb` has the out of domain sample on the first commitment, `beepref` the prover with separate passes,
# `beepbits` proofs of work with a whole number of bits, and `beepold` all three (BEEP-Ligerito as in the runs
# 20261113b and 20261113c).
STEP_VARIANTS = ["beep", "beepb", "beepref", "beepbits", "beepold"]
# The runs in which the prover of the affine variant was slower with proofs of work than without, for a reason
# that we did not find, and the later runs of the same cells (see 7-beep-ligerito/README.md).
ANOMALY_RUNS = ["three-way-20261113b", "three-way-20261113b-check1"]
# (The run 20261114f is not one of them: its bench binary had a defect in the buffers of our affine prover, which
# left the large instances short of memory; see 7-beep-ligerito/README.md.)
LATER_RUNS = ["three-way-20261113c", "three-way-20261113d", "three-way-20261113e", "three-way-20261114g"]
# Groups of instances for the ranges of the text, by (log2 words, log inverse rate of the first level).
GROUPS = {
    "big": lambda ln, lr: lr == 1 and ln >= 24,
    "mid": lambda ln, lr: lr == 1 and 20 <= ln <= 22,
    "short": lambda ln, lr: lr == 1 and ln <= 18,
    "long": lambda ln, lr: ln >= 20,
    "half": lambda ln, lr: lr == 1,
    "low": lambda ln, lr: lr >= 2,
    # the long messages at the rates 1/8 and 1/16
    "lowest": lambda ln, lr: lr >= 3 and ln >= 20,
}
# The accounting variant of the bench (not a row of any table of the paper): each BEEP ladder with its fold
# challenges ground for the error of the affine fold where that has a certificate.
HYBRID_ETAS = ["0.02", "0.001"]
# The slack of every level of Flock's own configurations at 128 bits (flock-core/configs/ligerito/*.toml:
# every level has `eta = 0.02`). The split configuration that the bench prints does not carry it.
SPLIT_ETA = "0.02"
PARALLEL_MIN_HASHES = 1 << 13  # flock-transcript: a search of at least 2^13 expected hashes runs on every thread


def cell_rate(row):
    """The log inverse rate of the first level of the shape of a row (the bench prints it since the run
    20261113c; before, `fast` is 1/2 and `slim` is 1/4)."""
    if row.get("l0_rate") is not None:
        return row["l0_rate"]
    return 1 if row["profile"] == "fast" else 2


def cell_label(row):
    return pow2(row["log_n"]), rate(cell_rate(row))


def join_and(parts, comma_last=False):
    """`a`, `a and b`, `a, b and c`; with `comma_last`, a comma also before the last `and`."""
    parts = list(parts)
    if len(parts) <= 1:
        return "".join(parts)
    last = (", and " if comma_last else " and ")
    return ", ".join(parts[:-1]) + last + parts[-1]


def shapes_phrase(shapes):
    """`2^25 words at rate 1/2, and 2^24 words at rates 1/8 and 1/16`, for (log_n, log inverse rate) pairs."""
    by_size = {}
    for ln, lr in shapes:
        by_size.setdefault(ln, []).append(lr)
    parts = []
    for ln in sorted(by_size, reverse=True):
        rs = sorted(by_size[ln])
        parts.append(f"{pow2(ln)} words at {'rate' if len(rs) == 1 else 'rates'} " + join_and(rate(r) for r in rs))
    return join_and(parts, comma_last=any(" and " in x for x in parts))


def shapes_by_rate(shapes):
    """`2^16, 2^17 and 2^18 words at rate 1/2, and 2^22 and 2^24 words at the rates 1/4 and 1/8`, for
    (log_n, log inverse rate) pairs: the rates with the same sizes share a part."""
    by_rate = {}
    for ln, lr in shapes:
        by_rate.setdefault(lr, []).append(ln)
    groups = []
    for lr in sorted(by_rate):
        sizes = tuple(sorted(by_rate[lr]))
        if groups and groups[-1][0] == sizes:
            groups[-1][1].append(lr)
        else:
            groups.append((sizes, [lr]))
    parts = [join_and(pow2(ln) for ln in sizes) + " words at "
             + ("rate " if len(rs) == 1 else "the rates ") + join_and(rate(r) for r in rs) for sizes, rs in groups]
    return join_and(parts, comma_last=True)


def slack(x):
    """A slack as the bench prints it (a float), in the shortest decimal form."""
    return repr(float(x))


def grind_work(g):
    """The expected hashes of one proof of work, from an entry of `grinds` or of `pow_grinds`."""
    return float(g["work"]) if "work" in g else float(1 << g["bits"])


def grind_bits(g):
    """The grinding of one proof of work as the tables print it: its bits, or, for a proof of work with a
    threshold, log2 of its expected hashes with one decimal."""
    if g.get("target") is None:
        return str(g["bits"])
    return f"{log2(grind_work(g)):.1f}"


def affine_residuals(path, variants=FLOCK_AFFINE_PROVER):
    """The rows of a run that one of the affine provers proves (`variants`; by default those of Flock's prover,
    which before the run 20261114g are `affine` and `affine-small`), each as a dict: `pct`, how much longer the
    prover takes with proofs of work than the time that the tables quote, in percent of that time (collect.py,
    pow_model_residual_ms); `shared`, whether its process also runs the other provers; `excess`, in a shared
    process, `pct` minus the median of the same number for the other provers of the process; `idle`, the idle
    share of the machine when the process started (None in the runs that did not record it); `process`, its
    process. The rows of a process that had part of its memory compressed are left out."""
    if not path.exists():
        return None
    rows = json.loads(path.read_text())["rows"]
    pct = lambda r: 100 * r["pow_model_residual_ms"] / r["prove_expected_ms"]
    usable = [r for r in rows if r.get("pow_model_residual_ms") is not None and r.get("prove_expected_ms")]
    out = []
    for r in usable:
        if r["variant"] not in variants:
            continue
        mem = r.get("memory") or {}
        if any((mem.get(side) or {}).get("limited") for side in ("pow", "nopow")):
            continue
        process = r.get("process", r["cell"])
        others = sorted(pct(x) for x in usable if x.get("process", x["cell"]) == process
                        and x["variant"] in ("split", "beep-0.02", "beep-0.001"))
        mid = (others[len(others) // 2] if len(others) % 2 else
               0.5 * (others[len(others) // 2 - 1] + others[len(others) // 2])) if others else None
        out.append({"pct": pct(r), "shared": bool(others), "excess": pct(r) - mid if others else None,
                    "idle": (mem.get("pow") or {}).get("idle_before_pct"),
                    "cell": r["cell"], "variant": r["variant"], "process": process})
    return out


def level_etas(variant, cfg):
    if variant == "split":
        return [SPLIT_ETA] * len(cfg["log_inv_rates"])
    if "levels" in cfg:
        return [slack(lv["eta"]) for lv in cfg["levels"]]
    return [slack(e) for e in cfg["etas"]]


def merkle_levels(row):
    """Per level of a proof: the bytes of the Merkle leaves that its queries open (the opened columns of the
    committed table), of the inner nodes of their authentication paths, and of the cap of its tree. From the
    configuration, by Flock's rules (pcs/stratified.rs): a level with Q queries on a block of 2^d positions
    absorbs the 2^c nodes at depth c = min(floor(log2 Q), d), every path has d - c inner nodes of 32 bytes, and a
    leaf is one column of 2^k field elements of 16 bytes. The bench measures the same parts on the proofs
    (`breakdown_levels`); the caller checks one against the other."""
    cfg = row["config"]
    ks = [cfg["initial_k"]] + list(cfg["recursive_ks"])
    cols = [row["log_n"] - cfg["initial_k"]] + list(cfg["recursive_log_msg_cols"])
    out = []
    for li, lr in enumerate(cfg["log_inv_rates"]):
        d, q = cols[li] + lr, cfg["queries"][li]
        cap = min(q.bit_length() - 1, d)
        out.append({"queries": q, "leaf_elements": 1 << ks[li], "path_nodes": d - cap, "log_block": d,
                    "leaves": q * (1 << ks[li]) * 16, "paths": q * (d - cap) * 32, "cap": (1 << cap) * 32})
    return out


# What each of the two processes of a row measures (collect.py): the process with the proofs of work, and its
# twin without them.
POW_FIELDS = ("prove_ms", "prove_ms_reps", "verify_ms", "pow_expected_ms", "pow_rate_only_ms", "pow_hashes_mean",
              "pow_hashes_per_ms_parallel", "pow_hashes_per_ms_sequential", "timings_ms", "commit_ms", "threads", "reps")
NOPOW_FIELDS = ("prove_nopow_ms", "prove_nopow_ms_reps", "timings_nopow_ms")


def take_process(row, rerun, side):
    """Replace, in a row, what one of its two processes measured (`side`: "pow" or "nopow") by the same process
    of a rerun, and derive again the quoted time and the check of the model. That check is M - (time without
    proofs of work) - (expected time of the proofs of work), where M, the median of the measured times minus
    the excess hashes of each repetition, belongs to the process with the proofs of work."""
    m_of = lambda x: x["pow_model_residual_ms"] + x["prove_nopow_ms"] + x["pow_expected_ms"]
    m_pow = m_of(rerun) if side == "pow" else m_of(row)
    for f in (POW_FIELDS if side == "pow" else NOPOW_FIELDS):
        row[f] = rerun[f]
    row["memory"][side] = rerun["memory"][side]
    if row.get("counters") and rerun.get("counters"):
        row["counters"][side] = rerun["counters"][side]
    row["prove_expected_ms"] = row["prove_nopow_ms"] + row["pow_expected_ms"]
    row["pow_model_residual_ms"] = m_pow - row["prove_nopow_ms"] - row["pow_expected_ms"]


def machine_state(processes):
    """The state of the machine before each process of a run, from the line of `top` that run_cells.zsh records:
    the unused memory and the memory in the compressor, in GB (ranges over the processes), and the hours of
    the first start and of the last end."""
    import re
    out, unused, compressor = {}, [], []
    gb = lambda value, unit: int(value) / (1 if unit == "G" else 1024)
    for c in processes.values():
        top = c.get("meta", {}).get("top_before", "")
        for found, into in ((re.search(r"(\d+)([MG]) unused", top), unused),
                            (re.search(r"(\d+)([MG]) compressor", top), compressor)):
            if found:
                into.append(gb(*found.groups()))
    if unused:
        out["unused-gb"] = rng(unused, f1)
    if compressor:
        out["compressor-gb"] = rng(compressor, f1)
    starts = sorted(c["meta"]["start"] for c in processes.values() if c.get("meta", {}).get("start"))
    ends = sorted(c["meta"]["end"] for c in processes.values() if c.get("meta", {}).get("end"))
    if starts and ends:
        out["hours"] = f"{starts[0][11:16]} to {ends[-1][11:16]}"
    return out


def load_run(results_path):
    """The results of a run, with what the folders next to it change: the processes of its reruns
    (`<run>-rerun*`) where the run had memory compressed, and the shapes of its additions (`<run>-add*`).
    Returns (data, rows by (cell, variant), processes, reran, added): `reran` lists (row, side, folder) for the
    processes taken from a rerun, and `added` (shape, folder) for the shapes taken from an addition."""
    data = json.loads(results_path.read_text())
    for w in data.get("warnings", []):
        warn("collect.py: " + w)
    rows = {(r["cell"], r["variant"]): r for r in data["rows"]}
    processes = dict(data["cells"])
    # Reruns: every folder `<run>-rerun*` next to the run (the convention of the campaign reports of
    # 5-implementation), with the same bench binary. A rerun measures again the two processes of a row (with
    # and without proofs of work). We take a process of a rerun where the process of the run had part of its
    # memory compressed or swapped and that of the rerun did not; the proofs are deterministic, so the rerun
    # must have the same configuration and the same proof size.
    binary_of = lambda d: (d.get("binaries") or [""])[0].split()[1:2]
    is_limited = lambda mem: bool(mem and mem["limited"])
    reran = []
    for rp in sorted(results_path.parent.parent.glob(results_path.parent.name + "-rerun*/results.json")):
        rd = json.loads(rp.read_text())
        if binary_of(rd) != binary_of(data):
            warn(f"{rp.parent.name} used another bench binary: not merged")
            continue
        for w in rd.get("warnings", []):
            warn(f"collect.py ({rp.parent.name}): " + w)
        for r in rd["rows"]:
            key = (r["cell"], r["variant"])
            old = rows.get(key)
            if old is None or old["proof_bytes"] != r["proof_bytes"] or old["config"] != r["config"]:
                warn(f"{rp.parent.name}: {key} is not a row of the run with the same configuration and proof: not merged")
                continue
            if any(x.get(f) is None for x in (old, r) for f in ("pow_model_residual_ms", "prove_nopow_ms", "pow_expected_ms")):
                warn(f"{rp.parent.name}: {key} lacks one of its two processes: not merged")
                continue
            for side in ("pow", "nopow"):
                if is_limited(old["memory"][side]) and not is_limited(r["memory"][side]):
                    take_process(old, r, side)
                    name = r["process"] + ("-nopow" if side == "nopow" else "")
                    processes[name] = rd["cells"][name]
                    reran.append((key, side, rp.parent.name))
    # More shapes: every folder `<run>-add*` next to the run, with the same bench binary, adds the rows of the
    # shapes that the run does not have (a shape that was measured on its own after the run, through the same
    # driver). The processes of such a shape are `<shape>[.<process>][-nopow]`. A later folder (in the order of
    # the names) replaces an earlier one for the same shape: `-add2` is a second measurement of the shape of
    # `-add1`, with the idle condition of the gate before every cell.
    shape_of_process = lambda name: (name[:-len("-nopow")] if name.endswith("-nopow") else name).split(".")[0]
    run_shapes = {c for c, _ in rows}
    added_from = {}
    for ap in sorted(results_path.parent.parent.glob(results_path.parent.name + "-add*/results.json")):
        ad = json.loads(ap.read_text())
        if binary_of(ad) != binary_of(data):
            warn(f"{ap.parent.name} used another bench binary: not merged")
            continue
        for w in ad.get("warnings", []):
            warn(f"collect.py ({ap.parent.name}): " + w)
        new_shapes = sorted({r["cell"] for r in ad["rows"]} - run_shapes)
        for key in [k for k in rows if k[0] in new_shapes]:
            del rows[key]
        for name in [n for n in processes if shape_of_process(n) in new_shapes]:
            del processes[name]
        for r in ad["rows"]:
            if r["cell"] in new_shapes:
                rows[(r["cell"], r["variant"])] = r
        for name, c in ad["cells"].items():
            if shape_of_process(name) in new_shapes:
                processes[name] = c
        for c in new_shapes:
            added_from[c] = ap.parent.name
    added = sorted(added_from.items())
    return data, rows, processes, reran, added


def measured_tables(results_path, numbers):
    tables = {"params": [], "main": [], "bytes": [], "bytes_all": [], "time": [], "steps": [], "asteps": [],
              "hybrid": []}
    if not results_path.exists():
        warn(f"no results at {results_path}: the measured tables are empty and their numbers are pending")
        return tables
    data, rows, processes, reran, added = load_run(results_path)
    binary_of = lambda d: (d.get("binaries") or [""])[0].split()[1:2]
    is_limited = lambda mem: bool(mem and mem["limited"])
    numbers["run:added-count"] = {0: "no", 1: "one", 2: "two"}.get(len(added), str(len(added)))
    cells = [c for c in CELLS if (c, "split") in rows]
    if not cells:
        warn("the results have no cell of the comparison")
        return tables
    for c, folder in added:
        if c not in cells:
            warn(f"{folder}: the shape {c} is not one of the instances of the tables (CELLS)")
    if added:
        numbers["run:added-shapes"] = shapes_phrase(
            [(rows[(c, "split")]["log_n"], cell_rate(rows[(c, "split")])) for c, _ in added if (c, "split") in rows])
        if len(added) != 1:
            warn(f"the text speaks of one instance that was measured on its own: {added}")
    for c in cells:
        for v, _ in VARIANTS:
            if (c, v) not in rows:
                warn(f"{c}: no row for {v}")

    # ---- sanity: the exact recheck of every BEEP level, the power source, the memory of every process
    for (cell, variant), r in rows.items():
        if variant.startswith("beep-"):
            levels = r["config"]["levels"]
            for li, lv in enumerate(levels):
                nxt = levels[li + 1] if li + 1 < len(levels) else None
                bad = bp.check_level(lv, level_index=li, next_level=nxt, last=nxt is None)
                if bad:
                    warn(f"{cell} {variant} level {li}: " + "; ".join(bad))
            # how the ladder grinds: the numerators of its ground challenges and its thresholds, exactly
            bad = bp.check_grinds(r["config"])
            if bad:
                warn(f"{cell} {variant}: " + "; ".join(bad))
            if "grinds" not in r["config"] or not all(g.get("target") for g in r["config"]["grinds"]["fold"]):
                warn(f"{cell} {variant}: the text says that its fold challenges have proofs of work with a threshold")
            if r["config"]["levels"][0]["ood_samples"] != 0:
                warn(f"{cell} {variant}: the text says that it has no sample on its first commitment")
    # The affine variants, against what the text says about them. Flock's variant as it ships has one out of
    # domain sample on its first commitment, and `anf` and `anfref` have none. A variant with our prover has the
    # configuration and the proof size of the one with Flock's prover (the bench also checks, before it times
    # them, that the two provers write the same proof). Without the sample, the configuration differs in the
    # samples and in the fold grinding of the first level, which does not decrease, and in nothing else.
    # (scripts/beep_params.py --check redoes the grinding of every level from its certificates.)
    strip = lambda cfg: {k: (v[1:] if k in ("ood_samples", "fold_grinding_bits") else v) for k, v in cfg.items()}
    for suffix, _ in AFFINE_SUFFIXES:
        for cell in sorted({c for (c, v) in rows}):
            fam = {f: rows.get((cell, f + suffix)) for f in AFFINE_STEPS}
            if not all(fam.values()):
                if any(fam.values()):
                    warn(f"{cell}: only some of {[f + suffix for f in AFFINE_STEPS]} ran")
                continue
            for f, r in fam.items():
                if r["config"]["ood_samples"][0] != AFFINE_KIND[f][0]:
                    warn(f"{cell} {f + suffix}: {r['config']['ood_samples'][0]} out of domain samples on its first "
                         "commitment: not what the text says")
            for ours, flock in (("afast", "affine"), ("anf", "anfref")):
                if fam[ours]["config"] != fam[flock]["config"] or fam[ours]["proof_bytes"] != fam[flock]["proof_bytes"]:
                    warn(f"{cell}: {ours + suffix} and {flock + suffix} differ in their configuration or proof size")
            a, n = fam["affine"]["config"], fam["anf"]["config"]
            if strip(a) != strip(n):
                warn(f"{cell}: anf{suffix} differs from affine{suffix} in more than the first level's samples and fold grinding")
            if n["fold_grinding_bits"][0] < a["fold_grinding_bits"][0]:
                warn(f"{cell}: anf{suffix} grinds the fold rounds of its first level less than affine{suffix}")
            if abs(fam["anf"]["proof_bytes"] - fam["affine"]["proof_bytes"]) > 64:
                warn(f"{cell}: the proofs of anf{suffix} and affine{suffix} differ by more than 64 bytes")
    # A process whose peak footprint exceeds its resident memory had part of its memory compressed or swapped
    # (the rule of the campaign reports: by more than 2 % and 32 MiB). A row is "limited" when this happens to
    # one of its two processes, with or without proofs of work: the first gives the verifier times and the
    # cost of the searches, the second the prover times. Its times are then printed in parentheses and left
    # out of every range of the text. `processes` holds the processes that the rows use (after the reruns).
    perturbed = []
    for name, c in processes.items():
        meta, t = c.get("meta", {}), c.get("time", {})
        if not (meta.get("power_before", "").startswith("AC") and meta.get("power_after", "").startswith("AC")):
            warn(f"cell {name} did not run on AC power ({meta.get('power_before')}, {meta.get('power_after')})")
        fp, rss = t.get("peak_footprint_bytes"), t.get("max_rss_bytes")
        if fp and rss and fp > 1.02 * rss and fp - rss > 32 << 20:
            perturbed.append(name)
            warn(f"cell {name}: peak footprint {fp / 2**30:.2f} GiB above its resident memory {rss / 2**30:.2f} GiB")
    limited = {key for key, r in rows.items() if any(is_limited(r["memory"][k]) for k in ("pow", "nopow"))}
    lim = lambda c, *variants: any((c, v) in limited for v in variants)
    par = lambda text, c, *variants: f"({text})" if lim(c, *variants) else text
    numbers["run:memory-limited-processes"] = str(len(perturbed))
    numbers["run:limited-rows"] = str(len(limited))
    # (the state of the machine during the run itself: not for the shapes that were added later)
    later = {c for c, _ in added}
    numbers.update({f"run:{k}": v for k, v in machine_state(
        {n: c for n, c in processes.items() if n.split(".")[0].replace("-nopow", "") not in later}).items()})
    if limited:
        warn(f"memory-limited rows {sorted(limited)}: their times are in parentheses in the tables, and the text of "
             "the section says that no process that the tables use had its memory compressed")
    # The page faults of a proof (the median over the repetitions of a prover; the bench counts them since the
    # run 20261113d). Our provers (BEEP-Ligerito, its controls, and our affine prover) take their tables from
    # Flock's buffer pool, so a proof takes no page fault unless the machine is short of memory: the affine
    # provers of the large instances took thousands per proof in the run 20261114f. Flock's provers allocate
    # tables in every proof: its split prover takes about as many faults as a message has pages for 2^20 words
    # and fewer, in every run.
    for key, r in rows.items():
        ours = key[1].startswith(("beep", "control", "afast")) or key[1] in (AFFINE, AFFINE_SMALL)
        pages = (16 << r["log_n"]) / PAGE_BYTES
        for side in ("pow", "nopow"):
            c = (r.get("counters") or {}).get(side)
            if c and c["median"]["faults"] > (FAULTS_PER_PROOF_MAX if ours else 2 * pages + FAULTS_PER_PROOF_MAX):
                warn(f"{key} ({side}): {c['median']['faults']:.0f} page faults per proof: its process ran short of memory")
    # the processes that come from a rerun, for the text: how many, of which instance and variant, how large
    numbers["run:reran-count"] = {0: "no", 1: "one", 2: "two", 3: "three"}.get(len(reran), str(len(reran)))
    if reran:
        labels = dict(VARIANTS)
        what = sorted({(key, side) for key, side, _ in reran})
        # (the text of the run 20261113e spoke of one such process; that of the run 20261114g of none)
        warn(f"the text says that no process had part of its memory compressed, and it mentions no rerun: the "
             f"reruns give {what}")
        (c0, v0), _ = what[0]
        size0, rate0 = cell_label(rows[(c0, v0)])
        numbers["run:reran-what"] = f"{labels.get(v0, v0).split(',')[0]} for {size0} words at rate {rate0}"
        numbers["run:reran-footprint"] = f1(rows[(c0, v0)]["memory"]["nopow"]["peak_footprint_bytes"] / 2 ** 30)
    fps = [c["time"]["peak_footprint_bytes"] / 2 ** 30 for c in processes.values()
           if c.get("time", {}).get("peak_footprint_bytes")]
    if fps:
        numbers["run:footprint-max"] = f1(max(fps))

    machine = data.get("machine", {})
    numbers["run:date"] = machine.get("date", "")[:10]
    numbers["run:cpu"] = machine.get("machdep.cpu.brand_string", "")
    numbers["run:memory-gb"] = str(round(int(machine.get("hw.memsize", "0")) / 2 ** 30))
    numbers["run:cores"] = f"{machine.get('hw.perflevel0.physicalcpu', '')} performance and " \
                           f"{machine.get('hw.perflevel1.physicalcpu', '')} efficiency cores"
    numbers["run:processes"] = str(len(processes))
    first = rows[(cells[0], "split")]
    numbers["run:threads"] = str(first["threads"])
    numbers["run:reps"] = str(first["reps"])
    binary = next((line for line in data.get("binaries", []) if line.startswith("ligerito_three_way")), "")
    numbers["run:binary"] = binary.split()[1] if binary else ""
    loads = [float(c["meta"]["load_before"].split()[0]) for c in processes.values() if "load_before" in c.get("meta", {})]
    if loads:
        numbers["run:load"] = rng(loads, f1)
    # the shapes whose variants each have their own process
    split_shapes = sorted({r["cell"] for r in rows.values() if r["process"] != r["cell"]}, key=cells.index)
    numbers["run:one-process-shapes"] = shapes_by_rate(
        [(rows[(c, "split")]["log_n"], cell_rate(rows[(c, "split")])) for c in split_shapes])
    # into how many processes the variants of such a shape are split (each of them runs twice, with and without
    # proofs of work)
    per_shape = {len({r["process"] for (cc, _), r in rows.items() if cc == c}) for c in split_shapes}
    if len(per_shape) == 1:
        n_proc = per_shape.pop()
        numbers["run:processes-per-split-shape"] = {2: "two", 3: "three", 4: "four", 5: "five", 6: "six"}.get(n_proc, str(n_proc))
    elif per_shape:
        warn(f"the shapes whose variants are split over several processes do not all have the same number of them: {per_shape}")
    # the shapes whose split configuration is Flock's derivation at a rate that Flock does not ship
    derived = [c for c in cells if rows[(c, "split")].get("split_derived")]
    derived_rates = sorted({cell_rate(rows[(c, "split")]) for c in derived})
    numbers["run:derived-rates"] = join_and(rate(r) for r in derived_rates)
    numbers["run:instances"] = str(len(cells))
    shape_of = {c: (rows[(c, "split")]["log_n"], cell_rate(rows[(c, "split")])) for c in cells}
    numbers["run:shapes"] = shapes_by_rate(shape_of.values())
    in_group = lambda c, g: GROUPS[g](*shape_of[c])
    for g in GROUPS:
        if not any(in_group(c, g) for c in cells):
            warn(f"no instance in the group `{g}` of the text")
    idle = [mem["idle_before_pct"] for r in rows.values() for mem in r["memory"].values()
            if mem and mem.get("idle_before_pct") is not None]
    if idle:
        numbers["run:idle-min"] = down(min(idle))
    all_rates = sorted({cell_rate(rows[(c, "split")]) for c in cells})
    numbers["run:rates"] = join_and(rate(r) for r in all_rates)
    if derived and set(derived_rates) & {1, 2}:
        warn("a split configuration at rate 1/2 or 1/4 is derived: the text says that those are Flock's own")
    numbers["run:variants-per-process"] = str(len({v for (c, v) in rows if c == cells[0]}))

    # ---- the proofs of work: the cost of a search, from the calibration of every process
    overheads, par_rates = [], []
    for name, c in processes.items():
        ctx = c.get("context") or {}
        rate_par = ctx.get("pow_hashes_per_ms_parallel")
        if not rate_par or name in perturbed:
            continue
        par_rates.append(rate_par)
        for k in ctx.get("pow_calibration") or []:
            if grind_work(k) >= PARALLEL_MIN_HASHES:
                overheads.append(1000 * (k["ms"] - k["hashes"] / rate_par) / k["searches"])
    if par_rates:
        numbers["run:pow-rate"] = rng([v / 1000 for v in par_rates], lambda v: f"{v:.0f}")
    if overheads:
        overheads.sort()
        numbers["run:pow-overhead-us"] = f"{overheads[len(overheads) // 2]:.0f}"
    # A check of the quoted prover times: the time measured with the proofs of work, minus the quoted time and
    # the hashes of that repetition beyond their expectation (collect.py, pow_model_residual_ms), in percent of
    # the quoted time. For the variants of the tables: not the controls, not the accounting variant.
    paper_variants = {v for v, _ in VARIANTS}
    res = {"others": [], "beep": []}
    for (c, v), r in rows.items():
        if (c, v) not in limited and v in paper_variants and r.get("pow_model_residual_ms") is not None:
            res["beep" if v.startswith("beep-") else "others"].append(
                (100 * r["pow_model_residual_ms"] / r["prove_expected_ms"], c, v))
    for key, vals in res.items():
        if vals:
            numbers[f"run:residual-pct-max:{key}"] = up(max(abs(x[0]) for x in vals))
    slow_affine = [x for x in res["others"] if x[2] != "split" and x[0] >= 10]
    if slow_affine:
        warn(f"the affine prover is 10 % or more slower with proofs of work than what the tables quote in "
             f"{[(c, v, round(x)) for x, c, v in slow_affine]}: the text says that this run does not show it")
    # The same check for every affine prover of this run, by prover: Flock's (`affine`, `anfref`) and ours
    # (`afast`, `anf`), at both slacks.
    added_paths = sorted({results_path.parent.parent / folder / "results.json" for _, folder in added})
    added_shapes = {c for c, _ in added}
    for key, variants in (("flock", FLOCK_AFFINE_PROVER), ("ours", OUR_AFFINE_PROVER)):
        vals = affine_residuals(results_path, variants) or []
        vals += [x for path in added_paths for x in (affine_residuals(path, variants) or []) if x["cell"] in added_shapes]
        if vals:
            numbers[f"run:affine-residual-pct-max:{key}"] = up(max(abs(x['pct']) for x in vals))
            numbers[f"run:affine-residual-rows:{key}"] = str(len(vals))
            slow = [(x["cell"], x["variant"], round(x["pct"])) for x in vals if x["pct"] >= 10]
            if slow:
                warn(f"affine provers ({key}) that are 10 % or more slower with proofs of work than what the "
                     f"tables quote: {slow}; the text says that this run has none")
    if res["beep"]:
        mid = sorted(x[0] for x in res["beep"])
        numbers["run:residual-beep-median"] = f"{(mid[len(mid) // 2] if len(mid) % 2 else 0.5 * (mid[len(mid) // 2 - 1] + mid[len(mid) // 2])):.0f}"
        numbers["run:residual-beep-positive"] = str(sum(1 for x in res["beep"] if x[0] > 0))
        numbers["run:residual-beep-rows"] = str(len(res["beep"]))
        worst = max(res["beep"], key=lambda x: abs(x[0]))
        numbers["run:residual-beep-worst-share"] = f"{100 * rows[(worst[1], worst[2])]['pow_expected_ms'] / rows[(worst[1], worst[2])]['prove_expected_ms']:.0f}"
    # The earlier runs in which the affine prover, and only it, was slower with proofs of work in the processes
    # that it shares with the other provers; and the later runs (see 7-beep-ligerito/README.md).
    bench = results_path.parent.parent
    early = [x for run in ANOMALY_RUNS for x in (affine_residuals(bench / run / "results.json") or []) if x["shared"]]
    if early:
        numbers["anomaly:pct"] = rng([x["pct"] for x in early], lambda v: f"{v:.0f}")
        numbers["anomaly:excess"] = rng([x["excess"] for x in early], lambda v: f"{v:.0f}")
        numbers["anomaly:runs"] = {1: "one", 2: "two", 3: "three"}.get(
            sum(1 for run in ANOMALY_RUNS if (bench / run / "results.json").exists()), "several")
        if min(x["excess"] for x in early) < 10:
            warn("an affine row of the earlier runs is less than 10 % slower than the other provers of its process: "
                 "check the footnote on the affine prover")
    later = [(run, affine_residuals(bench / run / "results.json")) for run in LATER_RUNS]
    later = [(run, vals) for run, vals in later if vals]
    if later:
        numbers["anomaly:later-runs"] = {1: "one", 2: "two", 3: "three", 4: "four"}.get(len(later), str(len(later)))
        shared = [dict(x, run=run) for run, vals in later for x in vals if x["shared"]]
        own = [dict(x, run=run) for run, vals in later for x in vals if not x["shared"]]
        if shared:
            numbers["anomaly:later-excess-max"] = up(max(x['excess'] for x in shared))
            numbers["anomaly:later-shared-processes"] = str(len({(x["run"], x["process"]) for x in shared}))
            if max(x["excess"] for x in shared) >= 10:
                warn("a later run shows the affine prover 10 % slower than the other provers of its process")
        # the processes with affine provers alone (one row of Flock's prover each before the run 20261114g, two
        # since): those in which Flock's prover is 10 % slower with proofs of work
        slow = [x for x in own if x["pct"] >= 10]
        slow_processes = {(x["run"], x["process"]) for x in slow}
        numbers["anomaly:later-own-slow"] = {0: "none", 1: "one", 2: "two"}.get(len(slow_processes), str(len(slow_processes)))
        numbers["anomaly:later-own-processes"] = str(len({(x["run"], x["process"]) for x in own}))
        if slow:
            numbers["anomaly:later-own-pct"] = rng([x["pct"] for x in slow], lambda v: f"{v:.0f}")
            idle_slow = [x["idle"] for x in slow if x["idle"] is not None]
            idle_rest = sorted(x["idle"] for x in own if x["pct"] < 10 and x["idle"] is not None)
            if idle_slow and idle_rest:
                numbers["anomaly:later-own-idle"] = rng(idle_slow, lambda v: f"{v:.0f}")
                numbers["anomaly:later-own-idle-rest"] = f"{idle_rest[len(idle_rest) // 2]:.0f}"
        if len(slow_processes) != 1 or len(slow) != 1:
            warn(f"{len(slow_processes)} processes ({len(slow)} rows) of the later runs with affine provers alone are "
                 "slow with proofs of work: the footnote on the affine prover speaks of one")
        if results_path.parent.name not in [run for run, _ in later]:
            warn("the run of the tables is not one of the later runs of the footnote on the affine prover")
    under = [100 * (1 - r["pow_rate_only_ms"] / r["pow_expected_ms"]) for (c, v), r in rows.items()
             if (c, v) not in limited and v.startswith("beep-") and r.get("pow_expected_ms") and r.get("pow_rate_only_ms")]
    if under:
        numbers["run:pow-rate-only-short"] = rng(under, lambda v: f"{v:.0f}")

    # ---- the parameters of every variant at the main cell
    cell = MAIN_CELL if (MAIN_CELL, "split") in rows else cells[0]
    numbers["params:cell"] = pow2(rows[(cell, "split")]["log_n"])
    for variant, label in VARIANTS:
        r = rows.get((cell, variant))
        if r is None:
            continue
        cfg = r["config"]
        ks = [cfg["initial_k"]] + cfg["recursive_ks"]
        cols = [r["log_n"] - cfg["initial_k"]] + cfg["recursive_log_msg_cols"]
        etas = level_etas(variant, cfg)
        grinds_all = r.get("pow_grinds") or {}
        levels = len(cfg["log_inv_rates"])
        # the grinding of a level's challenges: with a threshold for BEEP-Ligerito (`grinds`), else whole bits
        thr = cfg.get("grinds")
        grind = lambda kind, li: grind_bits(thr[kind][li]) if thr else str(cfg[kind + "_grinding_bits"][li])
        for li, lr in enumerate(cfg["log_inv_rates"]):
            samples = cfg.get("samples")
            lv = cfg["levels"][li] if "levels" in cfg else None
            # the split ladder commits to a folded table over GF(2^256) as two tables: one of its row bits
            # is not a fold round
            folds = ks[li] - (1 if variant == "split" and li > 0 else 0)
            batches = li + 1 < levels or variant == "split"
            tables["params"].append([
                label if li == 0 else "",
                m(li), rate(lr), pow2(cols[li] + lr), m(etas[li]), pow2(ks[li]),
                m(cfg["queries"][li]),
                m(folds),
                m(grind("fold", li)),
                m(samples[li]) if samples else "--",
                m(lv["threshold"] - lv["line_bound"]) if lv else "--",
                # a level with no sample on its commitment and no queries before it batches no claims (the first
                # level of BEEP-Ligerito, and of the affine variant as we run it)
                m(grind("claim_batch" if not thr else "claim", li)) if (cfg["ood_samples"][li] or li > 0) else "--",
                m(grind("consistency_batch" if not thr else "consistency", li)) if batches else "--",
            ])
        if variant in (AFFINE, AFFINE_SMALL):
            numbers[f"params:etas:{variant}"] = ", ".join(etas)
            numbers[f"params:fold-grind:{variant}"] = rng(cfg["fold_grinding_bits"], lambda v: str(v))
            # a first level without a sample has no proof of work for the batching of claims (the table prints
            # "--" there): the proof must have fewer of them than that of Flock's variant as it ships
            shipped = rows.get((cell, "affine" + variant[len(AFFINE):]))
            if shipped and cfg["ood_samples"][0] == 0:
                n_here = len(grinds_all.get("claim") or [])
                n_shipped = len((shipped.get("pow_grinds") or {}).get("claim") or [])
                if n_here >= n_shipped:
                    warn(f"{cell} {variant}: {n_here} proofs of work on the batching of claims, {n_shipped} with the "
                         "sample on the first commitment: the table says that its first level batches no claims")
        if variant.startswith("beep-"):
            numbers[f"params:fold-grind:{variant}"] = rng([log2(grind_work(g)) for g in thr["fold"]], f1)
            numbers[f"params:samples:{variant}"] = rng(cfg["samples"], lambda v: str(v))
            numbers[f"params:ood0:{variant}"] = str(cfg["ood_samples"][0])
        else:
            numbers[f"params:ood0:{variant}"] = str(cfg["ood_samples"][0])
        numbers[f"params:levels:{variant}"] = str(levels)
        numbers[f"params:searches:{variant}"] = str(sum(1 for v in grinds_all.values() for g in v if grind_work(g) > 1))
    numbers["params:qgrind"] = rng([b for r in rows.values() for b in r["config"]["query_grinding_bits"]], lambda v: str(v))
    # the least slack of the affine ladder, over every shape: at its first level, and at its last
    small = [level_etas(AFFINE_SMALL, rows[(c, AFFINE_SMALL)]["config"]) for c in cells if (c, AFFINE_SMALL) in rows]
    if small:
        numbers["params:affine-small-first"] = rng([float(e[0]) for e in small], lambda v: slack(v))
        numbers["params:affine-small-last"] = rng([float(e[-1]) for e in small], lambda v: slack(v))
        numbers["params:affine-slacks"] = ", ".join(bp.AFFINE_SLACKS)
    # the fold grinding of each kind of ladder, over every shape: whole bits for the affine ladders (also at the
    # first level alone, and at the later ones), log2 of the expected hashes for BEEP-Ligerito (and the whole
    # bits that the same challenges would need)
    for variant in ("affine", "affine-small", AFFINE, AFFINE_SMALL, "beep-0.02", "beep-0.001"):
        cfgs = [rows[(c, variant)]["config"] for c in cells if (c, variant) in rows]
        if not cfgs:
            continue
        if variant.startswith("beep-"):
            numbers[f"rng-fold-grind:{variant}"] = rng([log2(grind_work(g)) for cfg in cfgs for g in cfg["grinds"]["fold"]], f1)
            numbers[f"rng-fold-grind-bits:{variant}"] = rng([b for cfg in cfgs for b in cfg["fold_grinding_bits"]], lambda v: str(v))
        else:
            numbers[f"rng-fold-grind:{variant}"] = rng([b for cfg in cfgs for b in cfg["fold_grinding_bits"]], lambda v: str(v))
            numbers[f"rng-fold-grind0:{variant}"] = rng([cfg["fold_grinding_bits"][0] for cfg in cfgs], lambda v: str(v))
    # What the missing sample on the first commitment costs the affine ladder: the bits of grinding that the fold
    # rounds of its first level gain, over every shape, and the expected hashes of a proof (in percent).
    for ours, shipped in ((AFFINE, "affine"), (AFFINE_SMALL, "affine-small")):
        both = [(rows[(c, ours)], rows[(c, shipped)]) for c in cells if (c, ours) in rows and (c, shipped) in rows]
        if both:
            numbers[f"rng-fold-grind0-extra:{ours}"] = rng(
                [x["config"]["fold_grinding_bits"][0] - y["config"]["fold_grinding_bits"][0] for x, y in both], lambda v: str(v))
            numbers[f"rng-pow-extra-pct:{ours}"] = rng(
                [100 * (x["pow_expected_hashes"] / y["pow_expected_hashes"] - 1) for x, y in both], lambda v: f"{v:.0f}")
            if any(level_etas(ours, x["config"]) != level_etas(shipped, y["config"]) for x, y in both):
                warn(f"{ours} and {shipped} do not have the same slack at every level")
    # the part of the hashes of a proof that are not on its queries, for the variants that grind in whole bits
    nonq = []
    for c in cells:
        for variant in ("split", AFFINE, AFFINE_SMALL):
            g = (rows.get((c, variant)) or {}).get("pow_grinds")
            if g:
                total = sum(grind_work(x) for kind in g.values() for x in kind)
                nonq.append(100 * (total - sum(grind_work(x) for x in g["queries"])) / total)
    if nonq:
        numbers["rng-nonquery-pct:whole-bits"] = rng(nonq, lambda v: f"{v:.0f}")
        numbers["nonquery-pct-max:whole-bits"] = f"{max(nonq):.0f}"
    # What a threshold could save them, at most, in percent of the opening: less than half of the hashes of
    # every search that is not one of the queries (a search of g bits tries 2^g < 2 M hashes for a numerator M),
    # at the rate of the searches on one thread (the slower one).
    gains = []
    for c in cells:
        for variant in ("split", AFFINE, AFFINE_SMALL):
            r = rows.get((c, variant))
            if not r or not r.get("pow_grinds") or not r.get("prove_expected_ms") or lim(c, variant):
                continue
            g = r["pow_grinds"]
            other = sum(grind_work(x) for kind in ("fold", "claim", "consistency") for x in g[kind])
            gains.append(100 * (other / 2 / r["pow_hashes_per_ms_sequential"]) / r["prove_expected_ms"])
    if gains:
        numbers["threshold-gain-max-pct:whole-bits"] = f"{max(gains):.0f}" if max(gains) >= 1 else f"{max(gains):.1f}"
    # the least slack of the affine ladder, per instance: at its first level, and at every level
    for c in cells:
        if (c, AFFINE_SMALL) in rows:
            etas = level_etas(AFFINE_SMALL, rows[(c, AFFINE_SMALL)]["config"])
            numbers[f"affine-small-eta0:{c}"] = etas[0]
            numbers[f"affine-small-etas:{c}"] = etas[0] if len(set(etas)) == 1 else ", ".join(etas)
    if ("fast16", AFFINE_SMALL) in rows and ("fast16", AFFINE) in rows and \
            level_etas(AFFINE_SMALL, rows[("fast16", AFFINE_SMALL)]["config"]) != \
            level_etas(AFFINE, rows[("fast16", AFFINE)]["config"]):
        warn("the text says that for 2^16 words the affine ladder at its least slack is the one at 0.02")
    # the out of domain samples on the first commitment: one in Flock's variants as they ship, none in
    # BEEP-Ligerito and in the affine variant of the tables
    ood_variants = ["split", "affine", "affine-small"] + [v for v, _ in VARIANTS if v != "split"]
    ood0 = {v: {rows[(c, v)]["config"]["ood_samples"][0] for c in cells if (c, v) in rows} for v in ood_variants}
    want0 = {v: (1 if v in ("split", "affine", "affine-small") else 0) for v in ood_variants}
    if any(x and x != {want0[v]} for v, x in ood0.items()):
        warn(f"the text says that Flock's variants have one out of domain sample on the first commitment, and that "
             f"the affine variant of the tables and BEEP-Ligerito have none: {ood0}")
    if any(b for c in cells for b in rows[(c, "split")]["config"]["fold_grinding_bits"]):
        warn("the text says that Ligerito (Flock) has no fold grinding: no longer true")

    # ---- the main table
    for cell in cells:
        base = rows[(cell, "split")]
        size, r0 = cell_label(base)
        numbers[f"commit:{cell}"] = ms(base["commit_ms"])
        for i, (variant, label) in enumerate(VARIANTS):
            r = rows.get((cell, variant))
            if r is None:
                continue
            mark = "\\*" if variant == "split" and r.get("split_derived") else ""
            tables["main"].append([
                size if i == 0 else "", r0 if i == 0 else "",
                label + mark,
                m(kib(r["proof_bytes"])),
                par(m(ms(r["prove_expected_ms"])), cell, variant) if r["prove_expected_ms"] is not None else "--",
                par(m(ms(r["prove_nopow_ms"])), cell, variant) if r["prove_nopow_ms"] is not None else "--",
                m(f"{r['pow_expected_hashes'] / 1e6:.2f}"),
                par(m(f"{r['verify_ms']:.2f}"), cell, variant),
            ])
            numbers[f"size:{cell}:{variant}"] = kib(r["proof_bytes"])
            numbers[f"pow:{cell}:{variant}"] = f"{r['pow_expected_hashes'] / 1e6:.2f}"
            thr = r["config"].get("grinds")
            numbers[f"fold-grind0:{cell}:{variant}"] = grind_bits(thr["fold"][0]) if thr else str(r["config"]["fold_grinding_bits"][0])
            numbers[f"queries0:{cell}:{variant}"] = str(r["config"]["queries"][0])
            if lim(cell, variant):
                continue
            if r["prove_expected_ms"] is not None:
                numbers[f"provex:{cell}:{variant}"] = ms(r["prove_expected_ms"])
                numbers[f"nopow:{cell}:{variant}"] = ms(r["prove_nopow_ms"])
            numbers[f"verify:{cell}:{variant}"] = f"{r['verify_ms']:.2f}"

    TIME_FIELDS = ("prove_expected_ms", "prove_nopow_ms", "verify_ms")

    def ratios(a, b, field, only_rate=None, group=None):
        vals = []
        for cell in cells:
            ra, rb = rows.get((cell, a)), rows.get((cell, b))
            if field in TIME_FIELDS and lim(cell, a, b):
                continue
            if only_rate is not None and cell_rate(rows[(cell, "split")]) != only_rate:
                continue
            if group is not None and not in_group(cell, group):
                continue
            if ra and rb and ra.get(field) and rb.get(field):
                vals.append(ra[field] / rb[field])
        return vals

    # The pairs of variants that the text compares: BEEP-Ligerito with the other variants of the tables, these
    # among themselves, the affine variant of the tables and BEEP-Ligerito with Flock's affine variant as it
    # ships, and the affine provers that differ in one change (our prover; the sample on the first commitment).
    pairs = [("beep-0.02", "split"), ("beep-0.001", "split"), ("beep-0.02", AFFINE), ("beep-0.001", AFFINE),
             ("beep-0.001", AFFINE_SMALL), (AFFINE_SMALL, AFFINE), (AFFINE, "split"),
             (AFFINE_SMALL, "split"), ("beep-0.001", "beep-0.02"),
             ("beep-0.02", "affine"), ("beep-0.001", "affine-small"), ("beep-0.02", "afast"),
             (AFFINE, "affine"), (AFFINE_SMALL, "affine-small"), ("afast", "affine"), ("afast-small", "affine-small"),
             ("anfref", "affine"), ("anfref-small", "affine-small"), (AFFINE, "afast"), (AFFINE_SMALL, "afast-small"),
             # Flock's two variants as they ship; and both variants with the sample on the first commitment
             # (BEEP-Ligerito with it against the affine variant with our prover and with it)
             ("affine", "split"), ("affine-small", "split"), ("beepb-0.02", "afast"), ("beepb-0.001", "afast-small")]
    for a, b in pairs:
        for field, key in (("proof_bytes", "size"), ("prove_expected_ms", "provex"), ("prove_nopow_ms", "nopow"),
                           ("verify_ms", "verify"), ("pow_expected_hashes", "pow")):
            vals = ratios(a, b, field)
            # the same over the instances of one rate: `rng-provex@4:beep-0.02:affine` is at rate 1/16
            fmt = (lambda v: f"{v:.1f}") if key == "pow" else (lambda v: f"{v:.2f}")
            for lr in all_rates:
                at = ratios(a, b, field, lr)
                if at:
                    numbers[f"rng-{key}@{lr}:{a}:{b}"] = rng(at, fmt)
            # and over the groups of instances of the text: `rng-provex[big]:beep-0.02:affine`
            for g in GROUPS:
                at = ratios(a, b, field, group=g)
                if at:
                    numbers[f"rng-{key}[{g}]:{a}:{b}"] = rng(at, fmt)
                    if key == "size" and max(at) < 1:
                        numbers[f"rng-saving[{g}]:{a}:{b}"] = rng([100 * (1 - v) for v in at], lambda v: f"{v:.0f}")
            if vals:
                numbers[f"rng-{key}:{a}:{b}"] = rng(vals, fmt)
                # the saving, in percent, when the first is smaller than the second everywhere
                if key == "size" and max(vals) < 1:
                    numbers[f"rng-saving:{a}:{b}"] = rng([100 * (1 - v) for v in vals], lambda v: f"{v:.0f}")
            for cell in cells:
                ra, rb = rows.get((cell, a)), rows.get((cell, b))
                if field in TIME_FIELDS and lim(cell, a, b):
                    continue
                if ra and rb and ra.get(field) and rb.get(field):
                    numbers[f"ratio-{key}:{cell}:{a}:{b}"] = fmt(ra[field] / rb[field])
                    if key == "size":
                        numbers[f"saving:{cell}:{a}:{b}"] = f"{100 * (1 - ra[field] / rb[field]):.0f}"
    commits = [rows[(c, "split")]["commit_ms"] for c in cells if not lim(c, "split")]
    if commits:
        numbers["rng-commit"] = rng(commits, lambda v: ms(v))
    numbers["cells:sizes"] = ", ".join(sorted({pow2(rows[(c, 'split')]['log_n']) for c in cells if c.startswith('fast')}))
    # What the text says about the provers, checked. (1) BEEP-Ligerito is slower than the affine variant of the
    # tables in every instance with the proofs of work at their expected cost, and not faster without them. (2) Against
    # Flock's affine variant as it ships, BEEP-Ligerito is faster without proofs of work in every instance; with
    # them it is not slower for the long messages at rate 1/2 (group `big`), and slower elsewhere. (3) Each of
    # our two changes makes the affine prover faster, alone and after the other one, in every instance. (4)
    # Ligerito (Flock) is never the fastest variant of the tables.
    for c in cells:
        ok = lambda *vs: all((c, v) in rows and not lim(c, v) and rows[(c, v)].get("prove_expected_ms")
                             and rows[(c, v)].get("prove_nopow_ms") for v in vs)
        t = lambda v: rows[(c, v)]["prove_expected_ms"]
        n = lambda v: rows[(c, v)]["prove_nopow_ms"]
        for x, y in (("beep-0.02", AFFINE), ("beep-0.001", AFFINE_SMALL)):
            # with the proofs of work: slower in every instance; without them the text gives a range, which
            # starts at 1.00 for the shortest message: here a clearly faster BEEP-Ligerito would be news
            if ok(x, y) and (t(x) <= t(y) or n(x) < 0.97 * n(y)):
                warn(f"{c}: {x} is not slower than {y} (with proofs of work {t(x):.1f} and {t(y):.1f} ms, without "
                     f"{n(x):.2f} and {n(y):.2f} ms): the text says that it is, in every instance")
        for x, y in (("beep-0.02", "affine"), ("beep-0.001", "affine-small")):
            if not ok(x, y):
                continue
            if n(x) >= n(y):
                warn(f"{c}: without proofs of work {x} is not faster than {y} (Flock's variant as it ships): the text "
                     "says that it is")
            if in_group(c, "big") and t(x) > t(y):
                warn(f"{c}: {x} is slower than {y} (Flock's variant as it ships): the text says that it is not, for "
                     "the long messages at rate 1/2")
            if not in_group(c, "big") and t(x) <= t(y):
                warn(f"{c}: {x} is not slower than {y} (Flock's variant as it ships): the text says that it is, "
                     "outside the long messages at rate 1/2")
        for suffix, _ in AFFINE_SUFFIXES:
            for x, y in (("afast", "affine"), ("anfref", "affine"), ("anf", "afast"), ("anf", "anfref")):
                if ok(x + suffix, y + suffix) and t(x + suffix) >= t(y + suffix):
                    warn(f"{c}: {x + suffix} ({t(x + suffix):.2f} ms) is not faster than {y + suffix} "
                         f"({t(y + suffix):.2f} ms): the text says that each of our two changes helps")
        shown_t = {v: t(v) for v, _ in VARIANTS if ok(v)}
        if shown_t and min(shown_t, key=shown_t.get) == "split":
            warn(f"{c}: Ligerito (Flock) has the fastest prover")
    # size differences in bytes between BEEP at 0.02 and the affine ladder at 0.02
    diff = [rows[(c, "beep-0.02")]["proof_bytes"] - rows[(c, AFFINE)]["proof_bytes"]
            for c in cells if (c, "beep-0.02") in rows and (c, AFFINE) in rows]
    if diff:
        numbers[f"rng-size-diff-kib:beep-0.02:{AFFINE}"] = rng([d / 1024 for d in diff], f1)
        numbers[f"size-diff-kib-max:beep-0.02:{AFFINE}"] = up(max(abs(d) for d in diff) / 1024, 1)
    # what the missing sample changes in the proof of the affine variant, in bytes
    diff = [rows[(c, shipped)]["proof_bytes"] - rows[(c, ours)]["proof_bytes"]
            for ours, shipped in ((AFFINE, "affine"), (AFFINE_SMALL, "affine-small"))
            for c in cells if (c, ours) in rows and (c, shipped) in rows]
    if diff:
        numbers["rng-first-sample-bytes:affine"] = rng(diff, lambda v: str(int(v)))

    # ---- the parts of a proof: every part of the protocol, with the Merkle leaves (the opened columns) apart
    # from the inner nodes of the paths, per level, for the main cell; and a summary for every shape
    def pct(part, total):
        return f"{100 * part / total:.1f}"

    other = ["fold_answers", "round_messages", "binding_answers", "final_message", "nonces"]
    levels_of = {}
    for (c, variant), r in rows.items():
        derived = merkle_levels(r)
        measured = r.get("breakdown_levels")
        b = r["breakdown"]
        if measured is None:
            warn(f"{c} {variant}: the bench did not print the parts of its levels: derived from the configuration")
            measured = derived
        for li, (d, x) in enumerate(zip(derived, measured)):
            if (d["queries"], d["leaves"], d["paths"], d["cap"]) != (x["queries"], x["leaves"], x["paths"], x["cap"]):
                warn(f"{c} {variant} level {li}: the measured Merkle parts differ from the rules of the script")
        if len(derived) != len(measured):
            warn(f"{c} {variant}: {len(measured)} levels measured, {len(derived)} in the configuration")
        lv = [dict(d, **x) for d, x in zip(derived, measured)]
        sums = (sum(x["leaves"] for x in lv), sum(x["paths"] for x in lv), sum(x["cap"] for x in lv))
        if sums != (b["opened_rows"], b["merkle_paths"], b["caps"]):
            warn(f"{c} {variant}: the Merkle parts of the levels do not add up to those of the proof")
        if sum(sums) + sum(b[k] for k in other) != r["proof_bytes"]:
            warn(f"{c} {variant}: the parts of the proof do not add up to its size")
        levels_of[(c, variant)] = lv

    cell = MAIN_CELL if (MAIN_CELL, "split") in rows else cells[0]
    shown = [(v, label) for v, label in VARIANTS if (cell, v) in rows]
    max_levels = max(len(levels_of[(cell, v)]) for v, _ in shown)

    def part_row(label, sub, getter):
        return [label, sub] + [m(kib(val)) if val is not None else "--" for val in (getter(v) for v, _ in shown)]

    for li in range(max_levels):
        level = lambda v, key, li=li: levels_of[(cell, v)][li][key] if li < len(levels_of[(cell, v)]) else None
        tables["bytes"].append(part_row(f"level ${li}$", "leaves", lambda v: level(v, "leaves")))
        tables["bytes"].append(part_row("", "inner paths", lambda v: level(v, "paths")))
    simple = [("all levels", "caps", "caps"), ("fold rounds", "round messages", "round_messages"),
              ("", "sample answers", "fold_answers"), ("code switches", "binding values", "binding_answers"),
              ("end", "final message", "final_message"), ("proofs of work", "nonces", "nonces")]
    for label, sub, key in simple:
        tables["bytes"].append(part_row(label, sub, lambda v, key=key: rows[(cell, v)]["breakdown"][key]))
    tables["bytes"].append(["*total*", ""] + [m(kib(rows[(cell, v)]["proof_bytes"])) for v, _ in shown])
    numbers["bytes:cell"] = pow2(rows[(cell, "split")]["log_n"])
    numbers["bytes:variants"] = str(len(shown))
    # the first level is the same commitment in every variant: its leaves and its paths have one size
    first_levels = {(levels_of[(cell, v)][0]["leaf_elements"], levels_of[(cell, v)][0]["path_nodes"]) for v, _ in shown}
    if len(first_levels) != 1:
        warn("the leaves or the paths of the first level differ between the variants: check the text")
    leaf0, path0 = sorted(first_levels)[0]
    numbers["bytes:leaf0-elements"] = str(leaf0)
    numbers["bytes:leaf0-bytes"] = str(leaf0 * 16)
    numbers["bytes:path0-nodes"] = str(path0)
    numbers["bytes:path0-bytes"] = str(path0 * 32)
    numbers["bytes:cap0-depth"] = str(levels_of[(cell, "split")][0]["log_block"] - path0)
    numbers["bytes:log-block0"] = str(levels_of[(cell, "split")][0]["log_block"])
    numbers["bytes:queries0-split"] = str(levels_of[(cell, "split")][0]["queries"])
    for v, _ in shown:
        lv, total = levels_of[(cell, v)], rows[(cell, v)]["proof_bytes"]
        b = rows[(cell, v)]["breakdown"]
        later = sum(x["leaves"] + x["paths"] for x in lv[1:])
        numbers[f"bytes:queries:{v}"] = str(sum(x["queries"] for x in lv))
        numbers[f"bytes:queries0:{v}"] = str(lv[0]["queries"])
        numbers[f"bytes:level0-kib:{v}"] = kib(lv[0]["leaves"] + lv[0]["paths"])
        numbers[f"bytes:level0-pct:{v}"] = f"{100 * (lv[0]['leaves'] + lv[0]['paths']) / total:.0f}"
        numbers[f"bytes:later-kib:{v}"] = kib(later)
        numbers[f"bytes:levels:{v}"] = str(len(lv))
        numbers[f"bytes:rounds-kib:{v}"] = kib(b["round_messages"])
        numbers[f"bytes:answers-kib:{v}"] = kib(b["fold_answers"])
        numbers[f"bytes:rest-kib:{v}"] = kib(total - b["opened_rows"] - b["merkle_paths"])
    later_of = lambda v: sum(x["leaves"] + x["paths"] for x in levels_of[(cell, v)][1:])
    if (cell, AFFINE) in rows:
        numbers[f"bytes:later-ratio:split:{AFFINE}"] = f"{later_of('split') / later_of(AFFINE):.1f}"
        # the text compares the levels of the split ladder and of the affine ladder with the same index
        a, s_ = levels_of[(cell, AFFINE)], levels_of[(cell, "split")]
        same = all((x["log_block"], x["leaf_elements"]) == (y["log_block"], y["leaf_elements"]) for x, y in zip(a, s_))
        if not same:
            warn("the common levels of the split and affine ladders do not have the same block length and rows "
                 f"at {cell}: the text of the parts of a proof says that they do")
        numbers["bytes:extra-levels:split"] = str(len(s_) - len(a))
        if not all(x["queries"] <= y["queries"] for x, y in zip(a[1:], s_[1:])):
            warn("an affine level makes more queries than the split level of the same index: check the text")
    if (cell, "beep-0.02") in rows and (cell, AFFINE) in rows:
        dq = [abs(x["queries"] - y["queries"]) for x, y in zip(levels_of[(cell, "beep-0.02")], levels_of[(cell, AFFINE)])]
        numbers[f"bytes:query-diff:beep-0.02:{AFFINE}"] = str(sum(dq))
    # over every shape: the queries of BEEP at 0.02 against those of the affine ladder at 0.02
    dqs = []
    for c in cells:
        if (c, "beep-0.02") in rows and (c, AFFINE) in rows:
            dqs.append(sum(x["queries"] for x in levels_of[(c, AFFINE)]) - sum(x["queries"] for x in levels_of[(c, "beep-0.02")]))
    if dqs:
        numbers[f"rng-query-diff:{AFFINE}:beep-0.02"] = rng(dqs, lambda v: str(v))
        numbers[f"query-diff-max:{AFFINE}:beep-0.02"] = str(max(dqs))
        if min(dqs) < 0:
            warn("BEEP at 0.02 makes more queries than the affine ladder at 0.02 in some shape: check the text")
        # at no level does BEEP at 0.02 make more queries than the affine ladder at 0.02 (the text says that the
        # affine variant makes "up to" so many more)
        for c in cells:
            if (c, "beep-0.02") in rows and (c, AFFINE) in rows:
                qa = [x["queries"] for x in levels_of[(c, AFFINE)]]
                qb = [x["queries"] for x in levels_of[(c, "beep-0.02")]]
                if any(y > x for x, y in zip(qa, qb)):
                    warn(f"{c}: BEEP at 0.02 makes more queries than the affine ladder at some level ({qb} against {qa})")

    # the summary: leaves, inner paths and the rest, for every shape and variant
    leaf_pct, path_pct, merkle_pct, level0_pct, rest_kib = [], [], [], [], []
    for c in cells:
        size, r0 = cell_label(rows[(c, "split")])
        for i, (v, label) in enumerate(VARIANTS):
            r = rows.get((c, v))
            if r is None:
                continue
            lv, b, total = levels_of[(c, v)], r["breakdown"], r["proof_bytes"]
            leaves, paths = b["opened_rows"], b["merkle_paths"]
            rest = total - leaves - paths
            tables["bytes_all"].append([
                size if i == 0 else "", r0 if i == 0 else "", label,
                m(sum(x["queries"] for x in lv)),
                m(kib(leaves)), m(pct(leaves, total)), m(kib(paths)), m(pct(paths, total)),
                m(kib(rest)), m(pct(rest, total)), m(kib(total)),
            ])
            leaf_pct.append(100 * leaves / total)
            path_pct.append(100 * paths / total)
            merkle_pct.append(100 * (leaves + paths + b["caps"]) / total)
            level0_pct.append(100 * (lv[0]["leaves"] + lv[0]["paths"]) / total)
            rest_kib.append(rest / 1024)
            numbers[f"leaves-pct:{c}:{v}"] = f"{100 * leaves / total:.0f}"
            numbers[f"paths-pct:{c}:{v}"] = f"{100 * paths / total:.0f}"
    numbers["rng-leaves-pct"] = rng(leaf_pct, lambda x: f"{x:.0f}")
    numbers["rng-paths-pct"] = rng(path_pct, lambda x: f"{x:.0f}")
    numbers["rng-merkle-pct"] = rng(merkle_pct, f1)
    numbers["rng-level0-pct"] = rng(level0_pct, lambda x: f"{x:.0f}")
    numbers["rng-rest-kib"] = rng(rest_kib, f1)
    # the leaf and the path of the first level, for every shape (the same in every variant)
    for c in cells:
        x = levels_of[(c, "split")][0]
        numbers[f"leaf0-bytes:{c}"] = str(x["leaf_elements"] * 16)
        numbers[f"path0-bytes:{c}"] = str(x["path_nodes"] * 32)
    ratios0 = [levels_of[(c, "split")][0]["leaf_elements"] * 16 / (levels_of[(c, "split")][0]["path_nodes"] * 32) for c in cells]
    numbers["rng-leaf-over-path0"] = rng(ratios0, f1)
    for a, b_ in (("beep-0.001", AFFINE), ("beep-0.001", AFFINE_SMALL), ("beep-0.001", "split"),
                  (AFFINE, "split"), (AFFINE_SMALL, AFFINE)):
        for key, field in (("leaves", "opened_rows"), ("paths", "merkle_paths")):
            vals = [rows[(c, a)]["breakdown"][field] / rows[(c, b_)]["breakdown"][field]
                    for c in cells if (c, a) in rows and (c, b_) in rows]
            if vals:
                numbers[f"rng-{key}:{a}:{b_}"] = rng(vals)

    answers_kib, answers_pct = [], []
    for c in cells:
        for variant in ("beep-0.02", "beep-0.001"):
            r = rows.get((c, variant))
            if r:
                answers_kib.append(r["breakdown"]["fold_answers"] / 1024)
                answers_pct.append(100 * r["breakdown"]["fold_answers"] / r["proof_bytes"])
    if answers_kib:
        numbers["rng-answers-kib"] = rng(answers_kib, f1)
        numbers["rng-answers-pct"] = rng(answers_pct, f1)

    # ---- where the time of the BEEP prover goes (medians of the phases, in the process without proofs of
    # work), against the control with no samples, and against the prover with separate passes (`beepref`).
    # The prover computes the answers to the samples in the pass that folds the table, so the cost of the
    # samples is the time of its fold rounds minus that of the control. Next to them, the fold rounds and the
    # whole opening of the affine variant of the tables (at 0.02 in the rows of 0.02, at its least slack in the
    # others), whose prover times its phases in the same way.
    fold_time = lambda t: t["folds"] + t["fold_answers"]
    comparator = {"0.02": AFFINE, "0.001": AFFINE_SMALL}
    for c in cells:
        base = rows[(c, "split")]
        size, r0 = cell_label(base)
        first = True
        for eta in ("0.02", "0.001"):
            r, ctl = rows.get((c, f"beep-{eta}")), rows.get((c, f"control-{eta}"))
            if not (r and ctl and r.get("timings_nopow_ms") and ctl.get("timings_nopow_ms")):
                continue
            t, tc = r["timings_nopow_ms"], ctl["timings_nopow_ms"]
            samples = fold_time(t) - fold_time(tc)
            ref = rows.get((c, f"beepref-{eta}"))
            direct = (fold_time(ref["timings_nopow_ms"]) - fold_time(tc)) if ref and ref.get("timings_nopow_ms") else None
            fold_pow = sum(grind_work(g) for g in r["pow_grinds"]["fold"])
            rest = t["total"] - fold_time(t)
            used = (f"beep-{eta}", f"control-{eta}", f"beepref-{eta}")
            aff = rows.get((c, comparator[eta]))
            ta = (aff or {}).get("timings_nopow_ms")
            tables["time"].append([
                size if first else "", r0 if first else "", m(eta),
                par(m(ms(samples)), c, *used[:2]),
                par(m(ms(fold_time(tc))), c, used[1]),
                par(m(ms(rest)), c, used[0]),
                par(m(ms(r["prove_nopow_ms"])), c, used[0]),
                par(m(ms(ctl["prove_nopow_ms"])), c, used[1]),
                par(m(ms(fold_time(ta))), c, comparator[eta]) if ta else "--",
                par(m(ms(aff["prove_nopow_ms"])), c, comparator[eta]) if ta else "--",
                m(f"{fold_pow / 1e6:.2f}"),
                par(m(ms(r["pow_expected_ms"])), c, used[0]) if r["pow_expected_ms"] is not None else "--",
            ])
            first = False
            numbers[f"time-foldpow-share:{c}:{eta}"] = f"{100 * fold_pow / r['pow_expected_hashes']:.0f}"
            if abs(t["total"] - r["prove_nopow_ms"]) > 0.02 * r["prove_nopow_ms"] + 0.05:
                warn(f"{c} beep-{eta}: the phases add up to {t['total']:.2f} ms, the opening takes {r['prove_nopow_ms']:.2f} ms")
            if samples <= 0:
                warn(f"{c} beep-{eta}: the fold rounds are not slower than those of the control")
            if ta is None:
                warn(f"{c}: the affine prover of {comparator[eta]} did not time its phases")
            elif abs(ta["total"] - aff["prove_nopow_ms"]) > 0.02 * aff["prove_nopow_ms"] + 0.05:
                warn(f"{c} {comparator[eta]}: the phases add up to {ta['total']:.2f} ms, the opening takes {aff['prove_nopow_ms']:.2f} ms")
            if ta is not None and not lim(c, comparator[eta], *used[:2]):
                # the fold rounds of the three provers: the affine variant, BEEP-Ligerito, and the control
                numbers[f"time-affine-folds:{c}:{eta}"] = ms(fold_time(ta))
                numbers[f"time-affine-total:{c}:{eta}"] = ms(aff["prove_nopow_ms"])
                numbers[f"time-beep-folds:{c}:{eta}"] = ms(fold_time(t))
                numbers[f"time-folds-vs-affine:{c}:{eta}"] = ratio(fold_time(t), fold_time(ta))
                numbers[f"time-affine-folds-vs-control:{c}:{eta}"] = ratio(fold_time(ta), fold_time(tc))
                numbers[f"time-affine-vs-control:{c}:{eta}"] = ratio(aff["prove_nopow_ms"], ctl["prove_nopow_ms"])
                numbers[f"time-affine-extra:{c}:{eta}"] = ms(fold_time(ta) - fold_time(tc))
                if aff.get("pow_expected_ms") is not None and aff.get("prove_expected_ms"):
                    numbers[f"time-affine-pow-ms:{c}:{eta}"] = ms(aff["pow_expected_ms"])
                    numbers[f"time-affine-pow-share:{c}:{eta}"] = f"{100 * aff['pow_expected_ms'] / aff['prove_expected_ms']:.0f}"
            if lim(c, *used):
                continue
            numbers[f"time-pow-ms:{c}:{eta}"] = ms(r["pow_expected_ms"]) if r["pow_expected_ms"] is not None else ""
            numbers[f"time-samples:{c}:{eta}"] = ms(samples)
            numbers[f"time-folds:{c}:{eta}"] = ms(fold_time(tc))
            numbers[f"time-control:{c}:{eta}"] = ms(ctl["prove_nopow_ms"])
            numbers[f"time-overhead:{c}:{eta}"] = ratio(r["prove_nopow_ms"], ctl["prove_nopow_ms"])
            numbers[f"time-samples-share:{c}:{eta}"] = f"{100 * samples / r['prove_nopow_ms']:.0f}"
            if direct is not None:
                numbers[f"time-samples-direct:{c}:{eta}"] = ms(direct)
                numbers[f"time-samples-speedup:{c}:{eta}"] = f"{direct / samples:.1f}"
                numbers[f"time-overhead-direct:{c}:{eta}"] = ratio(ref["prove_nopow_ms"], ctl["prove_nopow_ms"])
            if r["pow_expected_ms"] is not None and r["prove_expected_ms"]:
                numbers[f"time-pow-share:{c}:{eta}"] = f"{100 * r['pow_expected_ms'] / r['prove_expected_ms']:.0f}"

    # ---- what each change of BEEP-Ligerito gives: the prover with one change undone at a time (`beepb`: with
    # the out of domain sample on the first commitment; `beepref`: separate passes; `beepbits`: proofs of work
    # with a whole number of bits), with all three undone (`beepold`), and the affine variant at its slack
    for c in cells:
        size, r0 = cell_label(rows[(c, "split")])
        first = True
        for eta in ("0.02", "0.001"):
            fam = {f: rows.get((c, f"{f}-{eta}")) for f in STEP_VARIANTS}
            aff = rows.get((c, comparator[eta]))
            # Flock's affine variant as it ships, which has none of the three choices: the comparison of like
            # with like for `beepold`
            shipped = rows.get((c, "affine" if eta == "0.02" else "affine-small"))
            if not all(fam.values()) or not aff or any(x.get("prove_expected_ms") is None for x in fam.values()):
                continue
            b = fam["beep"]
            for f, x in fam.items():
                # the variants differ in what the text says, and in nothing else
                same_levels = [dict(lv, ood_samples=0, ood_bits=0) for lv in x["config"]["levels"]] == \
                              [dict(lv, ood_samples=0, ood_bits=0) for lv in b["config"]["levels"]]
                ood0 = x["config"]["levels"][0]["ood_samples"]
                whole = all(g.get("target") is None for g in x["pow_grinds"]["fold"])
                want = {"beep": (0, False), "beepb": (1, False), "beepref": (0, False), "beepbits": (0, True),
                        "beepold": (1, True)}[f]
                if not same_levels or (min(ood0, 1), whole) != want:
                    warn(f"{c} {f}-{eta}: not the configuration that the table of the changes describes")
                if abs(x["proof_bytes"] - b["proof_bytes"]) > 64:
                    warn(f"{c} {f}-{eta}: its proof differs from that of BEEP-Ligerito by more than 64 bytes")
            tables["steps"].append([
                size if first else "", r0 if first else "", m(eta),
                *[par(m(ms(fam[f]["prove_expected_ms"])), c, f"{f}-{eta}") for f in STEP_VARIANTS],
                par(m(ms(aff["prove_expected_ms"])), c, comparator[eta]),
            ])
            first = False
            numbers[f"step-bits-hashes-pct:{c}:{eta}"] = f"{100 * (fam['beepbits']['pow_expected_hashes'] / b['pow_expected_hashes'] - 1):.0f}"
            if lim(c, comparator[eta], *[f"{f}-{eta}" for f in STEP_VARIANTS]):
                continue
            for f, x in fam.items():
                numbers[f"step-ms:{f}:{c}:{eta}"] = ms(x["prove_expected_ms"])
                numbers[f"step-vs-affine:{f}:{c}:{eta}"] = ratio(x["prove_expected_ms"], aff["prove_expected_ms"])
                if shipped and shipped.get("prove_expected_ms") and not lim(c, shipped["variant"]):
                    numbers[f"step-vs-shipped:{f}:{c}:{eta}"] = ratio(x["prove_expected_ms"], shipped["prove_expected_ms"])
            numbers[f"step-first-ms:{c}:{eta}"] = ms(fam["beepb"]["prove_nopow_ms"] - b["prove_nopow_ms"])
            numbers[f"step-passes-ms:{c}:{eta}"] = ms(fam["beepref"]["prove_nopow_ms"] - b["prove_nopow_ms"])
            numbers[f"step-bits-ms:{c}:{eta}"] = ms(fam["beepbits"]["prove_expected_ms"] - b["prove_expected_ms"])
            numbers[f"step-first-pct:{c}:{eta}"] = f"{100 * (fam['beepb']['prove_expected_ms'] / b['prove_expected_ms'] - 1):.0f}"
            numbers[f"step-passes-pct:{c}:{eta}"] = f"{100 * (fam['beepref']['prove_expected_ms'] / b['prove_expected_ms'] - 1):.0f}"
            numbers[f"step-bits-pct:{c}:{eta}"] = f"{100 * (fam['beepbits']['prove_expected_ms'] / b['prove_expected_ms'] - 1):.0f}"
            numbers[f"step-all:{c}:{eta}"] = ratio(fam["beepold"]["prove_expected_ms"], b["prove_expected_ms"])
    # What the text says about the three choices, checked: for 2^22 and 2^24 words at the rates 1/8 and 1/16
    # (group `lowest`) the threshold saves at least 5 % at slack 0.02; for the short messages at rate 1/2 the
    # sample on the first commitment and the threshold change the prover time by at most half a millisecond.
    for c in cells:
        for eta in ("0.02", "0.001"):
            fam = {f: rows.get((c, f"{f}-{eta}")) for f in STEP_VARIANTS}
            if not all(fam.values()) or any(x.get("prove_expected_ms") is None for x in fam.values()) \
                    or lim(c, *[f"{f}-{eta}" for f in STEP_VARIANTS]):
                continue
            t = {f: x["prove_expected_ms"] for f, x in fam.items()}
            if eta == "0.02" and in_group(c, "lowest") and t["beepbits"] < 1.05 * t["beep"]:
                warn(f"{c}: at slack 0.02 the threshold saves less than 5 %: the text says that it matters for the "
                     "long messages at the rates 1/8 and 1/16")
            if in_group(c, "short") and max(abs(t["beepb"] - t["beep"]), abs(t["beepbits"] - t["beep"])) > 0.5:
                warn(f"{c} at slack {eta}: the first sample or the threshold changes the prover time by more than "
                     "0.5 ms: the text says a few tenths of a millisecond at most for the short messages")
    # ---- what each of our two changes gives the affine variant: Flock's variant as it ships (`affine`), with
    # our prover (`afast`), without the sample on its first commitment (`anfref`), and with both (`anf`, the
    # affine variant of the tables), at 0.02 and at the least slack of each level; next to them, BEEP-Ligerito
    # at the slack of the same rows of the other tables.
    beep_of = {"0.02": "beep-0.02", "least": "beep-0.001"}
    for c in cells:
        size, r0 = cell_label(rows[(c, "split")])
        first = True
        for suffix, label in AFFINE_SUFFIXES:
            fam = {f: rows.get((c, f + suffix)) for f in AFFINE_STEPS}
            b = rows.get((c, beep_of[label]))
            if not all(fam.values()) or not b or any(x.get("prove_expected_ms") is None for x in fam.values()):
                continue
            names = [f + suffix for f in AFFINE_STEPS]
            tables["asteps"].append([
                size if first else "", r0 if first else "", "least" if label == "least" else m(label),
                *[par(m(ms(fam[f]["prove_expected_ms"])), c, f + suffix) for f in AFFINE_STEPS],
                par(m(ms(b["prove_expected_ms"])), c, beep_of[label]) if b.get("prove_expected_ms") is not None else "--",
            ])
            first = False
            if lim(c, *names):
                continue
            shipped, x_fast, x_ref, x_both = (fam[f] for f in AFFINE_STEPS)
            for f in AFFINE_STEPS:
                numbers[f"astep-ms:{f}:{c}:{label}"] = ms(fam[f]["prove_expected_ms"])
                numbers[f"astep-nopow-ms:{f}:{c}:{label}"] = ms(fam[f]["prove_nopow_ms"])
            saving = lambda x, y: f"{100 * (1 - x['prove_expected_ms'] / y['prove_expected_ms']):.0f}"
            numbers[f"astep-prover-pct:{c}:{label}"] = saving(x_fast, shipped)
            numbers[f"astep-sample-pct:{c}:{label}"] = saving(x_both, x_fast)
            numbers[f"astep-both-pct:{c}:{label}"] = saving(x_both, shipped)
            numbers[f"astep-speedup:{c}:{label}"] = ratio(shipped["prove_expected_ms"], x_both["prove_expected_ms"])
            numbers[f"astep-prover-ms:{c}:{label}"] = ms(shipped["prove_nopow_ms"] - x_fast["prove_nopow_ms"])
            numbers[f"astep-sample-ms:{c}:{label}"] = ms(x_fast["prove_nopow_ms"] - x_both["prove_nopow_ms"])
            # the fold rounds of our prover against the rest of Flock's (which does not time its phases): the
            # two provers share everything but the fold rounds, so the difference of the openings is theirs
            tf, tb = x_fast.get("timings_nopow_ms"), x_both.get("timings_nopow_ms")
            if tf and tb:
                numbers[f"astep-ood-ms:{c}:{label}"] = ms(tf["ood"] - tb["ood"])
                flock_folds = fold_time(tf) + shipped["prove_nopow_ms"] - x_fast["prove_nopow_ms"]
                numbers[f"astep-folds-flock-ms:{c}:{label}"] = ms(flock_folds)
                numbers[f"astep-folds-ours-ms:{c}:{label}"] = ms(fold_time(tf))
                numbers[f"astep-folds-speedup:{c}:{label}"] = f"{flock_folds / fold_time(tf):.1f}"
    for label in ("0.02", "least"):
        for key in ("astep-prover-pct", "astep-sample-pct", "astep-both-pct", "astep-speedup", "astep-folds-speedup"):
            for g in [None] + list(GROUPS):
                vals = [float(v) for k, v in numbers.items()
                        if k.startswith(key + ":") and k.endswith(":" + label)
                        and k[len(key) + 1:-len(label) - 1] in cells
                        and (g is None or in_group(k[len(key) + 1:-len(label) - 1], g))]
                if vals:
                    fmt = (lambda v: f"{v:.0f}") if key.endswith("-pct") else \
                          (lambda v: f"{v:.1f}") if key == "astep-folds-speedup" else (lambda v: f"{v:.2f}")
                    numbers[f"rng-{key}{'' if g is None else '[' + g + ']'}:{label}"] = rng(vals, fmt)
    # The noise between two processes: without proofs of work, an affine prover at slack 0.02 and the same
    # prover at the least slack do the same work up to their queries, in two processes (for the instances whose
    # variants are split) or in one. Per instance, the range over the four provers of how much longer the first
    # takes, in percent; and the largest absolute value outside the instances that the text names.
    family_diff = {}
    for c in cells:
        pairs_c = [(rows.get((c, f)), rows.get((c, f + "-small"))) for f in AFFINE_STEPS]
        vals = [100 * (x["prove_nopow_ms"] / y["prove_nopow_ms"] - 1) for x, y in pairs_c
                if x and y and x.get("prove_nopow_ms") and y.get("prove_nopow_ms")]
        if len(vals) == len(AFFINE_STEPS):
            family_diff[c] = vals
            numbers[f"affine-family-diff-pct:{c}"] = rng(vals, lambda v: f"{v:.0f}")
    NOISY = ("sixteenth24",)
    if family_diff:
        rest = [abs(v) for c, vals in family_diff.items() if c not in NOISY and c in split_shapes for v in vals]
        if rest:
            numbers["affine-family-diff-pct-max:other-split"] = up(max(rest))
        for c in NOISY:
            if c in family_diff and min(family_diff[c]) < 2:
                warn(f"{c}: the affine provers at slack 0.02 are not all slower than those at the least slack "
                     f"({family_diff[c]}): the text says that their process was slow")
        for c, vals in family_diff.items():
            if c not in NOISY and c in split_shapes and max(abs(v) for v in vals) >= 4:
                warn(f"{c}: the affine provers at the two slacks differ by {max(abs(v) for v in vals):.1f} % without "
                     "proofs of work: the text names only " + ", ".join(NOISY))
    # If the fold rounds of a level with a sample also had to carry the list (see the third limitation of the
    # text): the bits of fold grinding that each level after the first would gain, over every shape.
    # Also what this would cost the prover: the expected hashes that the fold searches of those levels gain, at
    # the rate of the searches on one thread, in percent of the opening. (A few of them, at the least slack and
    # at the smallest rates, would reach the 2^13 hashes of a search on every thread, which is faster per hash:
    # for those this is an upper bound.)
    for variant in (AFFINE, AFFINE_SMALL):
        extra, cost = [], []
        for c in cells:
            r = rows.get((c, variant))
            if not r:
                continue
            cfg = r["config"]
            ks = [cfg["initial_k"]] + list(cfg["recursive_ks"])
            col = r["log_n"]
            hashes = 0
            for li, (k, lr, eta) in enumerate(zip(ks, cfg["log_inv_rates"], cfg["etas"])):
                col -= k
                if li == 0:
                    continue
                lv = bp.affine_level(col + lr, lr, col, k, slack(eta))
                if lv is None:
                    warn(f"{c} {variant} level {li}: no certificate")
                    continue
                if lv["grinding"] != cfg["fold_grinding_bits"][li]:
                    warn(f"{c} {variant} level {li}: fold grinding {cfg['fold_grinding_bits'][li]}, recomputed {lv['grinding']}")
                L = bp.johnson_list_simple(lr, slack(eta))
                with_list = max(bp.affine_round_grinding(x["bits"], candidates=L)[1] for x in lv["rounds"])
                extra.append(with_list - lv["grinding"])
                hashes += k * ((1 << with_list) - (1 << lv["grinding"]))
            if r.get("pow_hashes_per_ms_sequential") and r.get("prove_expected_ms") and not lim(c, variant):
                cost.append(100 * hashes / r["pow_hashes_per_ms_sequential"] / r["prove_expected_ms"])
        if extra:
            numbers[f"rng-fold-grind-list-extra:{variant}"] = rng(extra, lambda v: str(v))
        if cost:
            numbers[f"rng-list-extra-pct:{variant}"] = rng(cost, lambda v: f"{v:.0f}" if v >= 1 else f"{v:.1f}")
            numbers[f"list-extra-pct-max:{variant}"] = f"{max(cost):.0f}"
    for eta in ("0.02", "0.001"):
        for key in ("step-first-pct", "step-passes-pct", "step-bits-pct", "step-bits-hashes-pct", "step-all",
                    "step-vs-affine:beepb", "step-vs-affine:beepold", "step-vs-affine:beep",
                    "step-vs-shipped:beepold", "step-vs-shipped:beep", "time-samples-speedup",
                    "time-samples-share", "time-overhead-direct"):
            for g in [None] + list(GROUPS):
                vals = [float(v) for k, v in numbers.items()
                        if k.startswith(key + ":") and k.endswith(":" + eta) and v
                        and k[len(key) + 1:-len(eta) - 1] in cells
                        and (g is None or in_group(k[len(key) + 1:-len(eta) - 1], g))]
                if vals:
                    fmt = (lambda v: f"{v:.0f}") if key.endswith("-pct") or key.endswith("-share") else \
                          (lambda v: f"{v:.1f}") if key.endswith("speedup") else (lambda v: f"{v:.2f}")
                    numbers[f"rng-{key}{'' if g is None else '[' + g + ']'}:{eta}"] = rng(vals, fmt)
    # ---- the accounting variant `beepaff-<eta>`: the BEEP ladder with its fold challenges ground for the
    # error of the affine fold where that has a certificate (7-beep-ligerito/scripts/beep_params.py,
    # --beep-affine-charge). Not a sound configuration, and not in any table of the paper: the numbers answer
    # "what if the fold challenge were charged the affine error (+2L) in place of delta n + 1 (+2L)".
    for c in cells:
        size, r0 = cell_label(rows[(c, "split")])
        first = True
        for eta in HYBRID_ETAS:
            b, h = rows.get((c, f"beep-{eta}")), rows.get((c, f"beepaff-{eta}"))
            if not (b and h):
                continue
            aff = rows.get((c, comparator[eta]))
            if h["proof_bytes"] != b["proof_bytes"]:
                warn(f"{c}: the accounting variant at {eta} has another proof size than BEEP")
            if h["config"]["samples"] != b["config"]["samples"] or h["config"]["queries"] != b["config"]["queries"]:
                warn(f"{c}: the accounting variant at {eta} differs from BEEP in more than its fold grinding")
            gb, gh = b["config"]["fold_grinding_bits"], h["config"]["fold_grinding_bits"]
            if any(x > y for x, y in zip(gh, gb)):
                warn(f"{c}: the accounting variant at {eta} grinds more than BEEP at some level")
            bits = lambda g: ", ".join(str(x) for x in g)
            # the hybrid's own measurement, and the same from BEEP's time without proofs of work
            from_beep = (b["prove_nopow_ms"] + h["pow_expected_ms"]) if (
                b.get("prove_nopow_ms") is not None and h.get("pow_expected_ms") is not None) else None
            tables["hybrid"].append([
                size if first else "", r0 if first else "", m(eta),
                m(bits(gb)), m(bits(gh)),
                m(f"{b['pow_expected_hashes'] / 1e6:.2f}"), m(f"{h['pow_expected_hashes'] / 1e6:.2f}"),
                m(ms(b["prove_expected_ms"])) if b.get("prove_expected_ms") is not None else "--",
                m(ms(h["prove_expected_ms"])) if h.get("prove_expected_ms") is not None else "--",
                m(ms(from_beep)) if from_beep is not None else "--",
                m(ms(b["prove_nopow_ms"])) if b.get("prove_nopow_ms") is not None else "--",
                m(ms(aff["prove_expected_ms"])) if aff and aff.get("prove_expected_ms") is not None else "--",
                m(kib(h["proof_bytes"])),
            ])
            first = False
            numbers[f"hyb:fold-grind:{c}:{eta}"] = bits(gh)
            numbers[f"hyb:pow:{c}:{eta}"] = f"{h['pow_expected_hashes'] / 1e6:.2f}"
            if lim(c, f"beep-{eta}", f"beepaff-{eta}", comparator[eta]):
                continue
            if h.get("prove_expected_ms") is not None and b.get("prove_expected_ms") is not None:
                numbers[f"hyb:provex:{c}:{eta}"] = ms(h["prove_expected_ms"])
                numbers[f"hyb:saving-ms:{c}:{eta}"] = ms(b["prove_expected_ms"] - h["prove_expected_ms"])
                numbers[f"hyb:ratio-beep:{c}:{eta}"] = ratio(h["prove_expected_ms"], b["prove_expected_ms"])
                if aff and aff.get("prove_expected_ms"):
                    numbers[f"hyb:ratio-affine:{c}:{eta}"] = ratio(h["prove_expected_ms"], aff["prove_expected_ms"])
                if h.get("pow_model_residual_ms") is not None:
                    numbers[f"hyb:residual:{c}:{eta}"] = f"{h['pow_model_residual_ms']:.1f}"
    for eta in HYBRID_ETAS:
        for key in ("hyb:ratio-beep", "hyb:ratio-affine"):
            vals = [float(v) for k, v in numbers.items() if k.startswith(key + ":") and k.endswith(":" + eta)]
            if vals:
                numbers[f"rng-{key}:{eta}"] = rng(vals)
        gs = [int(x) for k, v in numbers.items() if k.startswith("hyb:fold-grind:") and k.endswith(":" + eta)
              for x in v.split(", ")]
        if gs:
            numbers[f"rng-hyb:fold-grind:{eta}"] = rng(gs, lambda v: str(v))
        hp = [float(v) for k, v in numbers.items() if k.startswith("hyb:pow:") and k.endswith(":" + eta)]
        if hp:
            numbers[f"rng-hyb:pow:{eta}"] = rng(hp)

    for eta in ("0.02", "0.001"):
        for key, fmt in (("time-overhead", None), ("time-foldpow-share", "{:.0f}"), ("time-pow-share", "{:.0f}"),
                         ("time-folds-vs-affine", None), ("time-affine-folds-vs-control", None),
                         ("time-affine-vs-control", None), ("time-affine-pow-share", "{:.0f}")):
            for g in [None] + list(GROUPS):
                vals = [float(v) for k, v in numbers.items()
                        if k.startswith(key + ":") and k.endswith(":" + eta) and v
                        and k[len(key) + 1:-len(eta) - 1] in cells
                        and (g is None or in_group(k[len(key) + 1:-len(eta) - 1], g))]
                if vals:
                    numbers[f"rng-{key}{'' if g is None else '[' + g + ']'}:{eta}"] = \
                        rng(vals) if fmt is None else rng(vals, lambda v: fmt.format(v))
    return tables


# ------------------------------------------------------------------ the comparison at 100 bits
# The run of the same cells at 100 bits of security (7-beep-ligerito/scripts/cells100.txt): Flock's profiles
# `fast100` and `slim100` for Ligerito (Flock), and the affine and BEEP ladders built for a round-by-round
# target of 100 bits. Its tables are `params100` and `main100`, and its numbers have the prefix `100:`.
# The first of these that exists: a clean run of the cells at 100 bits, else the run 20261114h, whose large
# instances ran on a machine that was short of memory.
RUNS_100 = ["three-way-100bits-3", "three-way-20261114h"]
# When the times of a row of the run at 100 bits cannot be used (see `measured_tables_100`).
FAULTS_BURST = 1000
SLOW_VS_128 = 1.08
RESULTS_100 = next((p for p in (REPO / "7-beep-ligerito" / "bench_results" / run / "results.json" for run in RUNS_100)
                    if p.exists()), REPO / "7-beep-ligerito" / "bench_results" / RUNS_100[-1] / "results.json")
BITS_100 = 100


def measured_tables_100(results_path, numbers, rows128):
    """The tables `params100` and `main100` and the numbers `100:...` of the run at 100 bits. `rows128`: the
    rows of the run at 128 bits (after its reruns and additions), for the comparison of the two targets."""
    tables = {"params100": [], "main100": []}
    if not results_path.exists():
        warn(f"no results at {results_path}: the tables at 100 bits are empty and their numbers are pending")
        return tables
    num = {}
    data, rows, processes, reran, added = load_run(results_path)
    cells = [c for c in CELLS if (c, "split") in rows]
    if not cells:
        warn("the results at 100 bits have no cell of the comparison")
        return tables
    for c in cells:
        for v, _ in VARIANTS:
            if (c, v) not in rows:
                warn(f"100 bits, {c}: no row for {v}")
    missing_cells = [c for c in CELLS if (c, "split") not in rows]
    if missing_cells:
        warn(f"100 bits: no rows for the instances {missing_cells}")

    # ---- sanity, as for the run at 128 bits: the target of every ladder, the exact recheck of every BEEP
    # level for it, the affine family, the power source, the memory and the page faults of every process
    for (cell, variant), r in rows.items():
        want = BITS_100
        if r["config"].get("target_bits") != want:
            warn(f"100 bits, {cell} {variant}: a ladder for {r['config'].get('target_bits')} bits")
        if variant.startswith("beep-"):
            levels = r["config"]["levels"]
            for li, lv in enumerate(levels):
                nxt = levels[li + 1] if li + 1 < len(levels) else None
                bad = bp.check_level(lv, lam=BITS_100, level_index=li, next_level=nxt, last=nxt is None)
                if bad:
                    warn(f"100 bits, {cell} {variant} level {li}: " + "; ".join(bad))
            bad = bp.check_grinds(r["config"], lam=BITS_100)
            if bad:
                warn(f"100 bits, {cell} {variant}: " + "; ".join(bad))
            if r["config"]["levels"][0]["ood_samples"] != 0:
                warn(f"100 bits, {cell} {variant}: the text says that it has no sample on its first commitment")
    strip = lambda cfg: {k: (v[1:] if k in ("ood_samples", "fold_grinding_bits") else v) for k, v in cfg.items()}
    for suffix, _ in AFFINE_SUFFIXES:
        for cell in sorted({c for (c, v) in rows}):
            fam = {f: rows.get((cell, f + suffix)) for f in AFFINE_STEPS}
            if not all(fam.values()):
                if any(fam.values()):
                    warn(f"100 bits, {cell}: only some of {[f + suffix for f in AFFINE_STEPS]} ran")
                continue
            for f, r in fam.items():
                if r["config"]["ood_samples"][0] != AFFINE_KIND[f][0]:
                    warn(f"100 bits, {cell} {f + suffix}: {r['config']['ood_samples'][0]} samples on its first commitment")
            for ours, flock in (("afast", "affine"), ("anf", "anfref")):
                if fam[ours]["config"] != fam[flock]["config"] or fam[ours]["proof_bytes"] != fam[flock]["proof_bytes"]:
                    warn(f"100 bits, {cell}: {ours + suffix} and {flock + suffix} differ in their configuration or proof size")
            if strip(fam["affine"]["config"]) != strip(fam["anf"]["config"]):
                warn(f"100 bits, {cell}: anf{suffix} differs from affine{suffix} in more than its first level")
    is_limited = lambda mem: bool(mem and mem["limited"])
    for name, c in processes.items():
        meta = c.get("meta", {})
        if not (meta.get("power_before", "").startswith("AC") and meta.get("power_after", "").startswith("AC")):
            warn(f"100 bits: cell {name} did not run on AC power")
    limited = {key for key, r in rows.items() if any(is_limited(r["memory"][k]) for k in ("pow", "nopow"))}
    num["run:limited-rows"] = str(len(limited))
    flagged = lambda t: bool(t.get("peak_footprint_bytes") and t.get("max_rss_bytes")
                             and t["peak_footprint_bytes"] > 1.02 * t["max_rss_bytes"]
                             and t["peak_footprint_bytes"] - t["max_rss_bytes"] > 32 << 20)
    num["run:limited-processes"] = str(sum(1 for c in processes.values() if flagged(c.get("time", {}))))
    # Which times can be used. The rule was fixed on November 15, 2026, before the run 100bits-3 was read. This
    # machine now has little unused memory at any hour, and a large process has part of its memory compressed
    # (the committed table, which a prover reads only at its queries). In a smoke run before the campaign (see
    # `smoke` below) one large cell with that flag set had the median times of the run 20261114g at 128 bits,
    # with up to 250 page faults per proof. So the flag of the campaign reports does not decide here, and the
    # limit on page faults is not the guard of the run at 128 bits (FAULTS_PER_PROOF_MAX = 100 for our provers)
    # but FAULTS_BURST, which was chosen after that smoke run: a looser test, which the README says. A row is
    # unusable if
    #   * a prover took a burst of page faults: more than FAULTS_BURST per proof in the median (for Flock's
    #     provers, which allocate tables in every proof, twice the pages of a message more: at 2^22 words and
    #     more this limit is far above what they take, so it tests nothing there), or
    #   * without proofs of work it is more than SLOW_VS_128 times as slow as the same variant in the run at 128
    #     bits, where a prover does at least the same work: it makes more queries there, and BEEP-Ligerito takes
    #     5 samples in some fold rounds where it takes 4 at 100 bits (so the test is one-sided). This compares
    #     the rows whose ladder is the same at the two targets: all but those of Ligerito (Flock) below rate
    #     1/2, where `slim100` gains one step of rate per level and `slim` two. (The rule as fixed left every
    #     row of Ligerito (Flock) out; those at rate 1/2 were added after the run was read, which can only
    #     reject more rows.)
    # Every time of an instance with an unusable row of the tables is in parentheses in the tables and out of
    # every range of the text, which names these instances.
    LADDER = ("initial_k", "recursive_ks", "recursive_log_msg_cols", "log_inv_rates")

    def vs_128(key, r):
        """The time of a row without proofs of work over that of the same row at 128 bits, when the two have
        the same ladder; else None."""
        ref = rows128.get(key)
        if not (ref and ref.get("prove_nopow_ms") and r.get("prove_nopow_ms")):
            return None
        if any(ref["config"].get(k) != r["config"].get(k) for k in LADDER):
            return None
        return r["prove_nopow_ms"] / ref["prove_nopow_ms"]

    def unusable(key, r):
        ours = key[1].startswith(("beep", "control", "afast")) or key[1] in (AFFINE, AFFINE_SMALL)
        pages = (16 << r["log_n"]) / PAGE_BYTES
        for side in ("pow", "nopow"):
            c = (r.get("counters") or {}).get(side)
            if c and c["median"]["faults"] > FAULTS_BURST + (0 if ours else 2 * pages):
                return f"{c['median']['faults']:.0f} page faults per proof ({side})"
        q = vs_128(key, r)
        if q is not None and q > SLOW_VS_128:
            return f"{q:.2f} times its time at 128 bits without proofs of work"
        return None

    for key, r in rows.items():
        if key[1] != "split" and key in rows128 and vs_128(key, r) is None:
            warn(f"100 bits, {key}: its ladder is not that of the run at 128 bits: the text says that the two "
                 "runs have the same ladders, up to those of Ligerito (Flock)")
    reasons = {key: why for key, r in rows.items() for why in [unusable(key, r)] if why}
    num["run:unusable-rows"] = str(len(reasons))
    shown_limited = sorted({k[0] for k in reasons if k[1] in dict(VARIANTS)}, key=CELLS.index)
    lim = lambda c, *variants: c in shown_limited or any((c, v) in reasons for v in variants)
    par = lambda text, c, *variants: f"({text})" if lim(c, *variants) else text
    shapes_of = lambda cs: shapes_by_rate([(rows[(c, "split")]["log_n"], cell_rate(rows[(c, "split")])) for c in cs])
    num["run:unusable-count"] = {0: "no", 1: "one", 2: "two", 3: "three"}.get(len(shown_limited), str(len(shown_limited)))
    if shown_limited:
        num["run:unusable-shapes"] = shapes_of(shown_limited)
        print("100 bits: instances whose times are not used: "
              + "; ".join(f"{k[0]} {k[1]}: {why}" for k, why in sorted(reasons.items()) if k[1] in dict(VARIANTS)))
    clean = [c for c in cells if c not in shown_limited]
    num["run:clean-count"] = str(len(clean))
    if clean:
        num["run:clean-shapes"] = shapes_of(clean)
    # The same check as numbers: over the rows of the tables that are used and have the ladder of the run at 128
    # bits, the time without proofs of work against that of that run; the same over the rows of the processes
    # with compressed memory (the flag of the campaign reports); and the most page faults per proof of a prover
    # of ours.
    shown = dict(VARIANTS)
    vs = {key: q for key, r in rows.items() if key[1] in shown and key[0] in clean
          for q in [vs_128(key, r)] if q is not None}
    if vs:
        num["run:nopow-vs-128"] = rng(list(vs.values()))
        num["run:nopow-vs-128-rows"] = str(len(vs))
        # the README says that the high end of this range is a row of the slow process `eighth24.affsmall-nopow`
        worst = max(vs, key=vs.get)
        num["run:nopow-vs-128-max"] = up(vs[worst], 2)
        if rows[worst]["process"] != "eighth24.affsmall":
            warn(f"100 bits: the largest time against the run at 128 bits is {worst}: the README says that it is "
                 "a row of the process eighth24.affsmall-nopow")
        # without the instance of less than a millisecond, whose times are the noisiest
        longer = [q for key, q in vs.items() if rows[key]["prove_nopow_ms"] >= 1]
        if longer:
            num["run:nopow-vs-128[1ms]"] = rng(longer)
    vs_flagged = [q for key, q in vs.items() if key in limited]
    if vs_flagged:
        num["run:flagged-nopow-vs-128"] = rng(vs_flagged)
    # (Flock's prover for Ligerito allocates its tables in every proof: about a message of page faults up to
    # 2^20 words, by design)
    for kind, pick in (("ours", lambda v: v.startswith(("beep", "control", "afast")) or v in (AFFINE, AFFINE_SMALL)),
                       ("flock-affine", lambda v: v.startswith(("affine", "anfref"))),
                       ("flock", lambda v: v == "split")):
        faults = [c["median"]["faults"] for key, r in rows.items() if pick(key[1]) for side in ("pow", "nopow")
                  for c in [(r.get("counters") or {}).get(side)] if c]
        if faults:
            num[f"run:faults-max:{kind}"] = f"{max(faults):.0f}"
        # the same for 2^22 words and more, where the limit of Flock's provers is thousands of page faults
        big = [c["median"]["faults"] for key, r in rows.items() if pick(key[1]) and r["log_n"] >= 22
               for side in ("pow", "nopow") for c in [(r.get("counters") or {}).get(side)] if c]
        if big:
            num[f"run:faults-max-big:{kind}"] = f"{max(big):.0f}"
    # the processes with compressed memory, which the text names: all those of 2^24 words at rate 1/16, and the
    # two of Ligerito (Flock) for 2^25 words at rate 1/2
    flagged_names = {name for name, c in processes.items() if flagged(c.get("time", {}))}
    named = {name for name in processes if name.startswith("sixteenth24.")} | {"fast25.split", "fast25.split-nopow"}
    if flagged_names != named:
        warn(f"100 bits: the processes with compressed memory are {sorted(flagged_names)}: the text names "
             f"{sorted(named)}")
    num["run:flagged-sixteenth24"] = str(sum(1 for name in flagged_names if name.startswith("sixteenth24.")))
    num["run:flagged-fast25"] = str(sum(1 for name in flagged_names if name.startswith("fast25.")))
    # Below the line of the flag (2 % of the resident memory), the processes whose peak footprint still exceeds
    # their resident memory by more than 32 MiB: the text counts them, and the README names them.
    excess = lambda t: (t.get("peak_footprint_bytes") or 0) - (t.get("max_rss_bytes") or 0)
    near = {name for name, c in processes.items() if name not in flagged_names and excess(c.get("time", {})) > 32 << 20}
    num["run:near-limited-processes"] = {0: "no", 1: "one", 2: "two", 3: "three"}.get(len(near), str(len(near)))
    if near != {"eighth24.split", "fast25.affine", "sixteenth22"}:
        warn(f"100 bits: the processes with more than 32 MiB of compressed memory below the flag are {sorted(near)}: "
             "the README names eighth24.split, fast25.affine and sixteenth22")
    if any(name.endswith("-nopow") for name in near):
        warn("100 bits: a process without proofs of work is among them: the README says that they only affect the "
             "verifier times and the check against the times with proofs of work")
    near_excess = [100 * excess(processes[n]["time"]) / processes[n]["time"]["max_rss_bytes"] for n in near]
    if near_excess:
        num["run:near-limited-pct-max"] = up(max(near_excess), 1)
        num["run:near-limited-pct"] = f"{down(min(near_excess), 1)} to {up(max(near_excess), 1)}"
    # The text says that in `slim100` the rate is halved from one level to the next and that in `slim` it is
    # divided by four (also in the configurations that Flock's code derives from them), and that the machine had
    # less unused memory than during the run at 128 bits.
    for c in cells:
        a, b = rows.get((c, "split")), rows128.get((c, "split"))
        if not (a and b):
            continue
        steps = lambda r: {y - x for x, y in zip(r["config"]["log_inv_rates"], r["config"]["log_inv_rates"][1:])}
        want = ({1}, {1}) if cell_rate(a) == 1 else ({1}, {2})
        if (steps(a), steps(b)) != want:
            warn(f"100 bits, {c}: the rate of Ligerito (Flock) gains {steps(a)} per level at 100 bits and {steps(b)} "
                 f"at 128 bits: the text says {want}")
    flagged_excess = [100 * excess(processes[n]["time"]) / processes[n]["time"]["max_rss_bytes"] for n in flagged_names]
    if flagged_excess:
        num["run:limited-pct"] = rng(flagged_excess, lambda x: f"{x:.0f}")
    # What the compressed memory does to single proofs. (1) In the flagged processes, the first proof of Ligerito
    # (Flock) over the median of the nine, with and without proofs of work; the largest such ratio over every
    # row of the run at 128 bits. (2) The share of the repetitions that take more than 1.2 times the median of
    # their row, over the rows of 5 ms and more: in the flagged processes, in the others, and in the run at 128
    # bits. (3) The page faults per proof of our provers in the flagged processes, and the most in the run at
    # 128 bits. (4) Over the rows of the tables in the flagged processes: how far the median without proofs of
    # work is above the fastest repetition, in percent.
    REPS = (("pow", "prove_ms_reps"), ("nopow", "prove_nopow_ms_reps"))
    med = lambda xs: sorted(xs)[len(xs) // 2]
    in_flagged = lambda r, side: (r["process"] + ("-nopow" if side == "nopow" else "")) in flagged_names
    first = [r[key][0] / med(r[key]) for (c, v), r in rows.items() if v == "split"
             for side, key in REPS if r.get(key) and in_flagged(r, side)]
    if first:
        num["run:flagged-first-proof-x:split"] = rng(first, f1)
        num["run:flagged-split-processes"] = {2: "two", 4: "four"}.get(len(first), str(len(first)))
    # the constants of the rule, for the README
    num["rule:faults-burst"] = str(FAULTS_BURST)
    num["rule:slow-pct"] = f"{100 * (SLOW_VS_128 - 1):.0f}"
    num["rule:slow-pct-2d"] = f"{100 * (SLOW_VS_128 - 1):02.0f}"
    num["rule:faults-128-guard"] = str(FAULTS_PER_PROOF_MAX)
    first128 = [r[key][0] / med(r[key]) for (c, v), r in rows128.items() if v == "split"
                for _, key in REPS if r.get(key)]
    if first128:
        num["run:first-proof-x-max-128:split"] = up(max(first128), 1)

    def slow_share(source, pick):
        reps = [(x, med(r[key])) for r in source.values() for side, key in REPS
                if r.get(key) and med(r[key]) >= 5 and pick(r, side) for x in r[key]]
        return (100 * sum(1 for x, m_ in reps if x > 1.2 * m_) / len(reps), len(reps)) if reps else None

    for tag, source, pick in (("flagged", rows, in_flagged), ("clean", rows, lambda r, side: not in_flagged(r, side)),
                              ("128", rows128, lambda r, side: True)):
        share = slow_share(source, pick)
        if share:
            num[f"run:slow-reps-pct:{tag}"] = f"{share[0]:.1f}"
            num[f"run:slow-reps-count:{tag}"] = str(share[1])
    is_ours = lambda v: v.startswith(("beep", "control", "afast")) or v in (AFFINE, AFFINE_SMALL)
    fl = [c_["median"]["faults"] for (c, v), r in rows.items() if is_ours(v) and v in shown
          for side, _ in REPS if in_flagged(r, side) for c_ in [(r.get("counters") or {}).get(side)] if c_]
    if fl:
        num["run:flagged-faults:ours"] = rng(fl, lambda x: f"{x:.0f}")
    fl128 = [c_["median"]["faults"] for (c, v), r in rows128.items() if is_ours(v)
             for side, _ in REPS for c_ in [(r.get("counters") or {}).get(side)] if c_]
    if fl128:
        num["run:faults-max-128:ours"] = f"{max(fl128):.0f}"
    # the sides of the rows of the tables where a prover of ours takes more page faults per proof than the guard
    # of the run at 128 bits (FAULTS_PER_PROOF_MAX), which this run does not apply (see FAULTS_BURST)
    over = sorted((c, v, side) for (c, v), r in rows.items() if is_ours(v) and v in shown for side, _ in REPS
                  for c_ in [(r.get("counters") or {}).get(side)] if c_ and c_["median"]["faults"] > FAULTS_PER_PROOF_MAX)
    num["run:over-128-guard"] = str(len(over))
    named_over = {("sixteenth24", v, side) for v in (AFFINE, AFFINE_SMALL, "beep-0.02", "beep-0.001")
                  for side in ("pow", "nopow")} | {("fast25", AFFINE, "pow")}
    if set(over) != named_over:
        warn(f"100 bits: the rows above the page-fault guard of the run at 128 bits are {over}: the README names "
             f"{sorted(named_over)}")
    spread = [100 * (med(r["prove_nopow_ms_reps"]) / min(r["prove_nopow_ms_reps"]) - 1) for (c, v), r in rows.items()
              if v in shown and r.get("prove_nopow_ms_reps") and in_flagged(r, "nopow")]
    if spread:
        num["run:flagged-median-over-min-pct-max"] = up(max(spread))
    # the same range of times against the run at 128 bits over every prover of the flagged processes (the README)
    vs_all = [q for key, r in rows.items() if key in limited for q in [vs_128(key, r)] if q is not None]
    if vs_all:
        num["run:flagged-nopow-vs-128:all"] = rng(vs_all)
        num["run:flagged-nopow-vs-128:all-rows"] = str(len(vs_all))
    num.update({f"run:{k}": v for k, v in machine_state(processes).items()})
    ends = lambda text: [float(x) for x in text.split(" to ")]
    if "run:unused-gb" in num and "run:unused-gb" in numbers \
            and max(ends(num["run:unused-gb"])) >= min(ends(numbers["run:unused-gb"])):
        warn("100 bits: the machine did not have less unused memory than during the run at 128 bits "
             f"({num['run:unused-gb']} against {numbers['run:unused-gb']} GB): the text says that it had")
    # The smoke run before the campaign (bench_results/smoke-100bits-20261115: the four affine provers at slack
    # 0.02 without proofs of work, for 2^24 words at rate 1/2 and at rate 1/16, run by hand): its times against
    # those of the run at 128 bits, its page faults per proof, and the memory of its two processes. The limit
    # FAULTS_BURST was chosen after it.
    import re
    smoke = results_path.parent.parent / "smoke-100bits-20261115"
    for cell in ("fast24", "sixteenth24"):
        out, err = smoke / f"{cell}.affine-nopow.out", smoke / f"{cell}.affine-nopow.err"
        if not (out.exists() and err.exists()):
            continue
        res = [json.loads(line[7:]) for line in out.read_text().splitlines() if line.startswith("RESULT ")]
        ratios = [r["prove_ms"] / rows128[(cell, r["variant"])]["prove_nopow_ms"] for r in res
                  if (cell, r["variant"]) in rows128]
        faults = [r["counters"]["median"]["faults"] for r in res if r.get("counters")]
        text = err.read_text()
        rss = int(re.search(r"(\d+)\s+maximum resident set size", text).group(1))
        fp = int(re.search(r"(\d+)\s+peak memory footprint", text).group(1))
        if len(ratios) != 4 or not faults:
            warn(f"the smoke run of {cell} does not have its four affine provers")
            continue
        num[f"smoke:{cell}:vs-128"] = rng(ratios)
        num[f"smoke:{cell}:faults-max"] = f"{max(faults):.0f}"
        num[f"smoke:{cell}:rss-gb"] = f1(rss / 2 ** 30)
        num[f"smoke:{cell}:footprint-gb"] = f1(fp / 2 ** 30)
        is_set = fp > 1.02 * rss and fp - rss > 32 << 20
        if is_set != (cell == "sixteenth24"):
            warn(f"the smoke run of {cell}: the flag for compressed memory is {'set' if is_set else 'not set'}: "
                 "the README says that it is set for 2^24 words at rate 1/16 only")
        if max(faults) > FAULTS_BURST or max(ratios) > SLOW_VS_128:
            warn(f"the smoke run of {cell} fails the rule for usable times")
    # The two processes without proofs of work that were a few percent slow (see the noise between two processes
    # below): how much longer their provers take than what the twin process with proofs of work gives, in percent
    # (minus the residual of the rows of that process).
    for name in ("slim24.affine", "eighth24.affsmall"):
        vals = [-100 * r["pow_model_residual_ms"] / r["prove_expected_ms"] for r in rows.values()
                if r["process"] == name and r.get("pow_model_residual_ms") is not None and r.get("prove_expected_ms")]
        if vals:
            num[f"run:nopow-slow-pct:{name}"] = rng(vals, lambda v: f"{v:.0f}")
            if min(vals) < 2:
                warn(f"100 bits, {name}: its provers are not all slower without proofs of work than what the "
                     f"twin process gives ({[round(v, 1) for v in vals]}): the README says that they are")
    # For these two, the ratio of BEEP-Ligerito to the affine variant if the time of the affine prover is the
    # one that its twin process gives (the measured time with proofs of work, corrected for its hashes).
    for c, x, y in (("slim24", "beep-0.02", AFFINE), ("eighth24", "beep-0.001", AFFINE_SMALL)):
        rx, ry = rows.get((c, x)), rows.get((c, y))
        if rx and ry and ry.get("pow_model_residual_ms") is not None and rx.get("prove_expected_ms"):
            twin = rx["prove_expected_ms"] / (ry["prove_expected_ms"] + ry["pow_model_residual_ms"])
            num[f"ratio-provex-twin:{c}:{x}:{y}"] = f"{twin:.2f}"
            # the README says that neither ratio is at an end of the range over the instances
            others = [rows[(cc, x)]["prove_expected_ms"] / rows[(cc, y)]["prove_expected_ms"] for cc in cells
                      if cc != c and (cc, x) in rows and (cc, y) in rows]
            for q in (twin, rx["prove_expected_ms"] / ry["prove_expected_ms"]):
                if others and not min(others) <= q <= max(others):
                    warn(f"100 bits, {c}: the ratio {q:.2f} of {x} to {y} is at an end of the range over the "
                         "instances: the README says that it is not")
    # The first run of these cells (20261114h, on a machine that was in use and short of memory): how much
    # slower its provers were without proofs of work, in percent, over the rows of the tables of the instances
    # with 2^22 words and more.
    first = results_path.parent.parent / "three-way-20261114h" / "results.json"
    if first.exists() and first != results_path:
        rows_h = load_run(first)[1]
        slow = [100 * (rows_h[key]["prove_nopow_ms"] / r["prove_nopow_ms"] - 1) for key, r in rows.items()
                if key[1] in shown and r["log_n"] >= 22 and key in rows_h
                and rows_h[key].get("prove_nopow_ms") and r.get("prove_nopow_ms")]
        if slow:
            slow.sort()
            num["run:first-run-slow-pct"] = rng(slow, lambda v: f"{v:.0f}")
            num["run:first-run-slow-pct-median"] = f"{slow[len(slow) // 2]:.0f}"
            num["run:first-run-slow-pct-max"] = up(slow[-1])
        if any(rows_h[key]["proof_bytes"] != r["proof_bytes"] or rows_h[key]["config"] != r["config"]
               for key, r in rows.items() if key in rows_h) or set(rows_h) != set(rows):
            warn("100 bits: the first run (20261114h) differs from this one in a proof size or a configuration: "
                 "the README says that they are the same")
    num["run:reran-count"] = {0: "no", 1: "one", 2: "two", 3: "three"}.get(len(reran), str(len(reran)))
    if reran:
        warn(f"100 bits: processes taken from a rerun: {sorted({(k, s) for k, s, _ in reran})}; the text mentions none")

    machine = data.get("machine", {})
    num["run:date"] = machine.get("date", "")[:10]
    num["run:processes"] = str(len(processes))
    num["run:instances"] = str(len(cells))
    first = rows[(cells[0], "split")]
    num["run:reps"] = str(first["reps"])
    binary = next((line for line in data.get("binaries", []) if line.startswith("ligerito_three_way")), "")
    num["run:binary"] = binary.split()[1] if binary else ""
    loads = [float(c["meta"]["load_before"].split()[0]) for c in processes.values() if "load_before" in c.get("meta", {})]
    if loads:
        num["run:load"] = rng(loads, f1)
    idle = [mem["idle_before_pct"] for r in rows.values() for mem in r["memory"].values()
            if mem and mem.get("idle_before_pct") is not None]
    if idle:
        num["run:idle-min"] = down(min(idle))
    shape_of = {c: (rows[(c, "split")]["log_n"], cell_rate(rows[(c, "split")])) for c in cells}
    in_group = lambda c, g: GROUPS[g](*shape_of[c])
    # the shapes whose split configuration Flock does not ship: at 100 bits, the rates below 1/4
    derived = [c for c in cells if rows[(c, "split")].get("split_derived")]
    num["run:derived-rates"] = join_and(rate(r) for r in sorted({cell_rate(rows[(c, "split")]) for c in derived}))
    if {cell_rate(rows[(c, "split")]) for c in derived} & {1, 2}:
        warn("100 bits: a split configuration at rate 1/2 or 1/4 is derived: the text says that those are Flock's own")
    # the grinding of the queries, per rate of the first level: none in `fast100`, 16 bits in `slim100`
    qgrind = {}
    for c in cells:
        for v, _ in VARIANTS:
            if (c, v) in rows:
                qgrind.setdefault(shape_of[c][1], set()).update(rows[(c, v)]["config"]["query_grinding_bits"])
    for lr, bits in qgrind.items():
        num[f"qgrind@{lr}"] = rng(sorted(bits), lambda v: str(v))
    if qgrind.get(1) != {0} or any(b != {16} for lr, b in qgrind.items() if lr != 1):
        warn(f"100 bits: the text says that the queries have no grinding at rate 1/2 and 16 bits at the other "
             f"rates: {qgrind}")

    # ---- the check of the quoted prover times, as at 128 bits
    paper_variants = {v for v, _ in VARIANTS}
    res = {"others": [], "beep": []}
    for (c, v), r in rows.items():
        if not lim(c, v) and v in paper_variants and r.get("pow_model_residual_ms") is not None \
                and r.get("prove_expected_ms"):
            res["beep" if v.startswith("beep-") else "others"].append(
                (100 * r["pow_model_residual_ms"] / r["prove_expected_ms"], r["prove_expected_ms"]))
    for key, vals in res.items():
        if vals:
            num[f"run:residual-pct-max:{key}"] = up(max(abs(x) for x, _ in vals))
            # the same for the proofs of 2 ms and more: a few tenths of a millisecond are several percent below
            longer = [abs(x) for x, t in vals if t >= 2]
            if longer:
                num[f"run:residual-pct-max[2ms]:{key}"] = up(max(longer))
    # The noise between two processes, as at 128 bits: without proofs of work, an affine prover at slack 0.02 and
    # the same prover at the least slack do the same work up to their queries. Per instance whose variants are
    # split over processes, over the four provers: how much longer the first takes, in percent (`:0.02`), and
    # how much longer the second takes (`:least`). The text names the instances where they differ by 4 % or more.
    split_shapes = sorted({r["cell"] for r in rows.values() if r["process"] != r["cell"]}, key=CELLS.index)
    NOISY = {"slim24": "0.02", "eighth24": "least"}
    quiet = []
    for c in split_shapes:
        pairs_c = [(rows.get((c, f)), rows.get((c, f + "-small"))) for f in AFFINE_STEPS]
        vals = [100 * (x["prove_nopow_ms"] / y["prove_nopow_ms"] - 1) for x, y in pairs_c
                if x and y and x.get("prove_nopow_ms") and y.get("prove_nopow_ms")]
        if len(vals) != len(AFFINE_STEPS):
            continue
        inv = [100 * (1 / (1 + v / 100) - 1) for v in vals]
        num[f"affine-family-diff-pct:{c}:0.02"] = rng(vals, lambda v: f"{v:.0f}")
        num[f"affine-family-diff-pct:{c}:least"] = rng(inv, lambda v: f"{v:.0f}")
        worst = max(abs(v) for v in vals + inv)
        if c in NOISY:
            slower = vals if NOISY[c] == "0.02" else inv
            if min(slower) < 2:
                warn(f"100 bits, {c}: the affine provers at slack {NOISY[c]} are not all slower than the others "
                     f"({[round(v, 1) for v in slower]}): the text says that their process was slow")
        else:
            quiet.append(worst)
            if worst >= 4:
                warn(f"100 bits, {c}: the affine provers at the two slacks differ by {worst:.1f} % without proofs "
                     "of work: the text names only " + ", ".join(NOISY))
    if quiet:
        num["affine-family-diff-pct-max:other-split"] = up(max(quiet))

    # ---- the parameters of every variant at the main cell (the columns of `params`)
    cell = MAIN_CELL if (MAIN_CELL, "split") in rows else cells[0]
    num["params:cell"] = pow2(rows[(cell, "split")]["log_n"])
    for variant, label in VARIANTS:
        r = rows.get((cell, variant))
        if r is None:
            continue
        cfg = r["config"]
        ks = [cfg["initial_k"]] + cfg["recursive_ks"]
        cols = [r["log_n"] - cfg["initial_k"]] + cfg["recursive_log_msg_cols"]
        etas = level_etas(variant, cfg)
        levels = len(cfg["log_inv_rates"])
        thr = cfg.get("grinds")
        grind = lambda kind, li: grind_bits(thr[kind][li]) if thr else str(cfg[kind + "_grinding_bits"][li])
        for li, lr in enumerate(cfg["log_inv_rates"]):
            samples = cfg.get("samples")
            lv = cfg["levels"][li] if "levels" in cfg else None
            folds = ks[li] - (1 if variant == "split" and li > 0 else 0)
            batches = li + 1 < levels or variant == "split"
            tables["params100"].append([
                label if li == 0 else "",
                m(li), rate(lr), pow2(cols[li] + lr), m(etas[li]), pow2(ks[li]),
                m(cfg["queries"][li]),
                m(folds),
                m(grind("fold", li)),
                m(samples[li]) if samples else "--",
                m(lv["threshold"] - lv["line_bound"]) if lv else "--",
                m(grind("claim_batch" if not thr else "claim", li)) if (cfg["ood_samples"][li] or li > 0) else "--",
                m(grind("consistency_batch" if not thr else "consistency", li)) if batches else "--",
            ])
        num[f"params:levels:{variant}"] = str(levels)
        num[f"params:queries0:{variant}"] = str(cfg["queries"][0])
        if (cell, variant) in rows128:
            num[f"params:queries0-128:{variant}"] = str(rows128[(cell, variant)]["config"]["queries"][0])
    # Over every shape: the fold grinding of the affine and BEEP ladders (the text says that there is none), the
    # grinding of their batching challenges, the samples and the threshold of BEEP-Ligerito.
    for variant in (AFFINE, AFFINE_SMALL, "beep-0.02", "beep-0.001"):
        cfgs = [rows[(c, variant)]["config"] for c in cells if (c, variant) in rows]
        if not cfgs:
            continue
        fold = [b for cfg in cfgs for b in cfg["fold_grinding_bits"]]
        batch = [b for cfg in cfgs for key in ("claim_batch_grinding_bits", "consistency_batch_grinding_bits")
                 for b in cfg[key]]
        num[f"fold-grind-max:{variant}"] = str(max(fold))
        num[f"batch-grind-max:{variant}"] = str(max(batch))
        if max(fold) or max(batch):
            warn(f"100 bits: {variant} grinds a fold or batching challenge ({max(fold)}, {max(batch)} bits): the "
                 "text says that it grinds none")
        if variant.startswith("beep-"):
            num[f"rng-samples:{variant}"] = rng([s for cfg in cfgs for s in cfg["samples"]], lambda v: str(v))
            over = [lv["threshold"] - lv["line_bound"] for cfg in cfgs for lv in cfg["levels"]]
            num[f"threshold-over-max:{variant}"] = str(max(over))
            # with thresholds, a ladder whose squeezes need no grinding has no proof of work on them
            if any(g.get("target") is not None or g.get("bits") for cfg in cfgs for kind in ("fold", "claim", "consistency")
                   for g in cfg["grinds"][kind]):
                warn(f"100 bits: {variant} has a proof of work on a fold or batching squeeze")
    # The samples of BEEP-Ligerito per fold round over both slacks and every instance, at 100 bits and in the run
    # at 128 bits. The text says that a prover does no more work at 100 bits: no level has more samples.
    for tag, source in (("rng-samples", rows), ("rng-samples-128", rows128)):
        vals = [s for c in cells for v in ("beep-0.02", "beep-0.001") if (c, v) in source
                for s in source[(c, v)]["config"]["samples"]]
        if vals:
            num[tag] = rng(vals, lambda v: str(v))
    for c in cells:
        for v in ("beep-0.02", "beep-0.001"):
            a, b = rows.get((c, v)), rows128.get((c, v))
            if a and b and any(x > y for x, y in zip(a["config"]["samples"], b["config"]["samples"])):
                warn(f"100 bits, {c} {v}: a level has more samples than at 128 bits "
                     f"({a['config']['samples']} against {b['config']['samples']})")
    # the largest numerator of a fold squeeze of BEEP-Ligerito, in bits: the text says that it is below 28
    nums = [lv["fold_numerator"] for c in cells for v in ("beep-0.02", "beep-0.001") if (c, v) in rows
            for lv in rows[(c, v)]["config"]["levels"]]
    if nums:
        num["beep-fold-numerator-bits-max"] = up(log2(max(nums)), 1)
        if max(nums) >= 1 << 28:
            warn("100 bits: a fold squeeze of BEEP-Ligerito has a numerator of 2^28 or more")

    # ---- the main table
    for cell in cells:
        base = rows[(cell, "split")]
        size, r0 = cell_label(base)
        for i, (variant, label) in enumerate(VARIANTS):
            r = rows.get((cell, variant))
            if r is None:
                continue
            mark = "\\*" if variant == "split" and r.get("split_derived") else ""
            tables["main100"].append([
                size if i == 0 else "", r0 if i == 0 else "",
                label + mark,
                m(kib(r["proof_bytes"])),
                par(m(ms(r["prove_expected_ms"])), cell, variant) if r["prove_expected_ms"] is not None else "--",
                par(m(ms(r["prove_nopow_ms"])), cell, variant) if r["prove_nopow_ms"] is not None else "--",
                m(f"{r['pow_expected_hashes'] / 1e6:.2f}"),
                par(m(f"{r['verify_ms']:.2f}"), cell, variant),
            ])
            num[f"size:{cell}:{variant}"] = kib(r["proof_bytes"])
            num[f"pow:{cell}:{variant}"] = f"{r['pow_expected_hashes'] / 1e6:.2f}"
            if lim(cell, variant):
                continue
            if r["prove_expected_ms"] is not None:
                num[f"provex:{cell}:{variant}"] = ms(r["prove_expected_ms"])
                num[f"nopow:{cell}:{variant}"] = ms(r["prove_nopow_ms"])
            num[f"verify:{cell}:{variant}"] = f"{r['verify_ms']:.2f}"

    TIME_FIELDS = ("prove_expected_ms", "prove_nopow_ms", "verify_ms")

    def ratios(a, b, field, group=None):
        vals = []
        for cell in cells:
            ra, rb = rows.get((cell, a)), rows.get((cell, b))
            if field in TIME_FIELDS and lim(cell, a, b):
                continue
            if group is not None and not in_group(cell, group):
                continue
            if ra and rb and ra.get(field) and rb.get(field):
                vals.append(ra[field] / rb[field])
        return vals

    pairs = [("beep-0.02", "split"), ("beep-0.001", "split"), ("beep-0.02", AFFINE), ("beep-0.001", AFFINE),
             ("beep-0.001", AFFINE_SMALL), (AFFINE_SMALL, AFFINE), (AFFINE, "split"), (AFFINE_SMALL, "split"),
             ("beep-0.001", "beep-0.02"), ("beep-0.02", "affine"), (AFFINE, "affine"), ("affine", "split")]
    for a, b in pairs:
        for field, key in (("proof_bytes", "size"), ("prove_expected_ms", "provex"), ("prove_nopow_ms", "nopow"),
                           ("verify_ms", "verify")):
            fmt = lambda v: f"{v:.2f}"
            for g in [None] + list(GROUPS):
                at = ratios(a, b, field, g)
                if at:
                    tag = "" if g is None else f"[{g}]"
                    num[f"rng-{key}{tag}:{a}:{b}"] = rng(at, fmt)
                    if key == "size" and max(at) < 1:
                        num[f"rng-saving{tag}:{a}:{b}"] = rng([100 * (1 - v) for v in at], lambda v: f"{v:.0f}")
            for cell in cells:
                ra, rb = rows.get((cell, a)), rows.get((cell, b))
                if field in TIME_FIELDS and lim(cell, a, b):
                    continue
                if ra and rb and ra.get(field) and rb.get(field):
                    num[f"ratio-{key}:{cell}:{a}:{b}"] = fmt(ra[field] / rb[field])
                    if key == "size":
                        num[f"saving:{cell}:{a}:{b}"] = f"{100 * (1 - ra[field] / rb[field]):.0f}"
    diff = [rows[(c, "beep-0.02")]["proof_bytes"] - rows[(c, AFFINE)]["proof_bytes"]
            for c in cells if (c, "beep-0.02") in rows and (c, AFFINE) in rows]
    if diff:
        num[f"size-diff-kib-max:beep-0.02:{AFFINE}"] = up(max(abs(d) for d in diff) / 1024, 1)
    # the least slack of the affine ladder is the one at 128 bits: a certificate does not depend on the target
    for c in cells:
        a, b = rows.get((c, AFFINE_SMALL)), rows128.get((c, AFFINE_SMALL))
        if a and b and level_etas(AFFINE_SMALL, a["config"]) != level_etas(AFFINE_SMALL, b["config"]):
            warn(f"100 bits, {c}: the least slacks of the affine ladder differ from those at 128 bits")

    # ---- against the run at 128 bits: the proof, the queries and the prover of every variant of the tables
    for v, _ in VARIANTS:
        size, prove, nopow, queries = [], [], [], []
        for c in cells:
            a, b = rows.get((c, v)), rows128.get((c, v))
            if not (a and b):
                continue
            size.append(a["proof_bytes"] / b["proof_bytes"])
            queries.append(sum(a["config"]["queries"]) / sum(b["config"]["queries"]))
            if a.get("prove_expected_ms") and b.get("prove_expected_ms") and not lim(c, v):
                prove.append(a["prove_expected_ms"] / b["prove_expected_ms"])
                nopow.append(a["prove_nopow_ms"] / b["prove_nopow_ms"])
        if size:
            num[f"rng-size-vs-128:{v}"] = rng(size)
            num[f"rng-saving-vs-128:{v}"] = rng([100 * (1 - x) for x in size], lambda x: f"{x:.0f}")
            num[f"rng-queries-vs-128:{v}"] = rng(queries)
        if prove:
            num[f"rng-provex-vs-128:{v}"] = rng(prove)
            num[f"rng-nopow-vs-128:{v}"] = rng(nopow)
        # the same saving at rate 1/2 and at the other rates (the text gives the two apart)
        for g in ("half", "low"):
            at = [100 * (1 - rows[(c, v)]["proof_bytes"] / rows128[(c, v)]["proof_bytes"]) for c in cells
                  if in_group(c, g) and (c, v) in rows and (c, v) in rows128]
            if at:
                num[f"rng-saving-vs-128[{g}]:{v}"] = rng(at, lambda x: f"{x:.0f}")
    # The text says why the saving is smaller at rate 1/2: there the queries have 16 bits of grinding at 128 bits
    # and none at 100 bits, and at the other rates they have 16 bits at both targets.
    for c in cells:
        for v in (AFFINE, AFFINE_SMALL, "beep-0.02", "beep-0.001"):
            a, b = rows.get((c, v)), rows128.get((c, v))
            if not (a and b):
                continue
            want = ({0}, {16}) if in_group(c, "half") else ({16}, {16})
            got = (set(a["config"]["query_grinding_bits"]), set(b["config"]["query_grinding_bits"]))
            if got != want:
                warn(f"100 bits, {c} {v}: query grinding {got} at 100 and 128 bits: the text says {want}")
    half = [float(x) for v in (AFFINE, "beep-0.02") for x in num.get(f"rng-saving-vs-128[half]:{v}", "").split(" to ") if x]
    low = [float(x) for v in (AFFINE, "beep-0.02") for x in num.get(f"rng-saving-vs-128[low]:{v}", "").split(" to ") if x]
    if half and low and max(half) >= min(low):
        warn("100 bits: the saving against 128 bits is not smaller at rate 1/2 than at the other rates")

    # ---- what the text says about the provers at 100 bits, checked: (1) at rate 1/2 the affine variant and
    # BEEP-Ligerito have no proof of work; (2) BEEP-Ligerito is not faster than the affine variant, and takes at
    # most 1.35 times as long, in every instance.
    for c in cells:
        for x, y in (("beep-0.02", AFFINE), ("beep-0.001", AFFINE_SMALL)):
            rx, ry = rows.get((c, x)), rows.get((c, y))
            if not (rx and ry) or lim(c, x, y):
                continue
            if shape_of[c][1] == 1 and (rx["pow_expected_hashes"] or ry["pow_expected_hashes"]):
                warn(f"100 bits, {c}: {x} or {y} has proofs of work at rate 1/2: the text says that they have none")
            q = rx["prove_expected_ms"] / ry["prove_expected_ms"]
            if not 0.9 <= q <= 1.35:
                warn(f"100 bits, {c}: {x} takes {q:.2f} times as long as {y}: the text says that the two are close "
                     "(the cost of the samples)")
    # (3) the text says that this ratio is largest for 2^24 and 2^25 words at rate 1/2, at both slacks
    for x, y in (("beep-0.02", AFFINE), ("beep-0.001", AFFINE_SMALL)):
        q = {c: rows[(c, x)]["prove_expected_ms"] / rows[(c, y)]["prove_expected_ms"] for c in cells
             if (c, x) in rows and (c, y) in rows and not lim(c, x, y)}
        top = set(sorted(q, key=q.get)[-2:])
        if top != {"fast24", "fast25"}:
            warn(f"100 bits: {x} against {y} is largest in {sorted(top)}: the text says for 2^24 and 2^25 words at "
                 "rate 1/2")
    numbers.update({f"100:{k}": v for k, v in num.items() if v not in ("", None)})
    return tables


def fold_numbers_100(numbers, recompute=False):
    """What changes in the comparison of one fold at 100 bits (the errors of `fold_tables` do not depend on the
    target): the grinding that each analysis needs, and what the rule of BEEP selects. Numbers `100:fold:...`."""
    rows = comparison_rows(recompute, lam=BITS_100)
    need = lambda bits: max(0, ceil(BITS_100 - bits - 1e-9))
    for eta in bp.ETAS:
        sel = [r for r in rows if r["eta"] == eta]
        numbers[f"100:fold:bchks-grind:{eta}"] = rng([need(r["bchks_bits"]) for r in sel], lambda v: str(v))
        numbers[f"100:fold:dkt-grind:{eta}"] = rng([need(r["dkt_bits"]) for r in sel], lambda v: str(v))
    numbers["100:fold:beep-m"] = rng([r["beep"]["samples"] for r in rows], lambda v: str(v))
    numbers["100:fold:beep-grind"] = rng([r["beep"]["fold_grinding_bits"] for r in rows], lambda v: str(v))
    numbers["100:fold:beep-fold"] = rng([r["beep"]["fold_bits"] for r in rows], f1)
    numbers["100:fold:beep-points-min"] = down(min(r["beep"]["sample_bits"] for r in rows), 1)
    over = [r["beep"]["threshold"] - r["line_bound"] for r in rows]
    numbers["100:fold:beep-threshold-over-max"] = str(max(over))
    certified = [r for r in rows if r["affine_grinding_bits"] is not None]
    if certified:
        numbers["100:fold:affine-grind"] = rng([r["affine_grinding_bits"] for r in certified], lambda v: str(v))


def main():
    args = sys.argv[1:]
    results = DEFAULT_RESULTS
    if "--results" in args:
        results = Path(args[args.index("--results") + 1])
    out_path = Path(args[args.index("--out") + 1]) if "--out" in args else OUT
    numbers = {}
    tables = fold_tables(numbers, "--recompute" in args)
    tables.update(measured_tables(results, numbers))
    # the same comparison at 100 bits: its own run, tables `params100` and `main100`, numbers `100:...`
    results100 = Path(args[args.index("--results100") + 1]) if "--results100" in args else RESULTS_100
    fold_numbers_100(numbers, "--recompute" in args)
    rows128 = load_run(results)[1] if results.exists() else {}
    tables.update(measured_tables_100(results100, numbers, rows128))
    numbers = {k: v for k, v in numbers.items() if v not in ("", None)}
    # Every `num("key")` of the section must be a number that this script wrote (a missing one prints
    # "pending" in the paper). The keys of the placeholder table are built in the section and are not checked.
    import re
    section = (TYPST / "deep+.typ").read_text()
    quoted = sorted(set(re.findall(r'num\("([^"]+)"\)', section)))
    missing = [k for k in quoted if k not in numbers and not k.startswith("other:")]
    for k in missing:
        warn(f"the section quotes num(\"{k}\"), which this script did not write")
    out_path.parent.mkdir(exist_ok=True)
    out = {
        "generated_by": "typst/scripts/make_tables.py; do not edit by hand",
        "results": str(results.relative_to(REPO)) if results.exists() and REPO in results.parents else str(results),
        "results100": str(results100.relative_to(REPO)) if results100.exists() and REPO in results100.parents
        else str(results100),
        "numbers": numbers,
        "tables": tables,
    }
    out_path.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(f"{out_path}: {len(numbers)} numbers, tables " + ", ".join(f"{k} ({len(v)} rows)" for k, v in tables.items()))
    if "--print" in args:
        for name, rows in tables.items():
            print(f"--- {name}")
            for row in rows:
                print("  " + " | ".join(row))
        for k in sorted(numbers):
            print(f"  {k} = {numbers[k]}")
    print(f"{len(quoted)} numbers quoted by the section, {len(missing)} missing")
    print(f"{len(WARNINGS)} warnings")


if __name__ == "__main__":
    main()
