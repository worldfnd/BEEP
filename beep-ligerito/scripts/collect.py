#!/usr/bin/env python3
"""Collect a run of the three-way Ligerito comparison into results.json.

[AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request; research, unaudited; please review]
[AI-revised (claude-fable-5-2), 2026-11-13, after an independent review: the searches of a proof are read from
the bench, which checks them against the nonces of its proofs, and a search costs what the bench measured for
searches of that many bits, not only its hashes at the rate of long searches]
[AI-revised (claude-fable-5-2), 2026-11-13, for the run 20261113c: the rate of L0 of every row]
[AI-revised (claude-fable-5-2), 2026-11-13, for the run 20261113e: searches against a threshold (`pow_grinds`):
a search has an expected work that need not be a power of two, and its cost is read from the calibration of
that same search]
[AI-revised (claude-fable-5-2), 2026-11-14: every row keeps what its prover used in both processes (`counters`:
CPU time, instructions, cycles, the part on performance cores, context switches; medians, from
benches/support/run_counters.rs) and the idle share of the machine when each process started]
[AI-revised (claude-fable-5-2), 2026-11-16, for the minimal run: `pow_expected_ms_by_kind`, the expected cost of
the proofs of work of a row by kind of search (fold challenges, claim batching, consistency batching, queries);
the four add up to `pow_expected_ms`]

    python3 scripts/collect.py bench_results/three-way-<label>

Reads machine.txt, binaries.txt, cells.tsv and cells/<name>.{out,err,meta} of the folder that
scripts/run_cells.zsh wrote, and writes results.json next to them: one row per cell and variant.

A cell `<shape>` runs with the proofs of work, and `<shape>-nopow` runs the same provers with
FLOCK_NO_GRIND=1. A cell may also be named `<shape>.<process>` (a rerun with one variant per process):
its rows are filed under the shape. For each variant the row of `<shape>` gets

    prove_ms            median prove time, with the proofs of work as they happened
    prove_nopow_ms      median prove time of the `-nopow` cell
    pow_expected_ms     the proofs of work at their expected cost. The bench times, in the same process, a few
                        hundred searches of every bit count that a variant uses (`pow_calibration`). A search
                        of b bits costs the mean time of those searches, corrected to 2^b hashes at the rate
                        of long searches (searches below 2^13 expected hashes run on one thread in
                        flock-transcript, the others on every thread and pay about 60 microseconds more)
    pow_rate_only_ms    the same with 2^b hashes at the rate of long searches alone (the rule of the first run)
    prove_expected_ms   prove_nopow_ms + pow_expected_ms: the prove time that the paper quotes
    pow_model_residual_ms  a check of the model: the median, over the repetitions with proofs of work, of the
                        measured time minus (prove_nopow_ms + pow_expected_ms + the hashes of that repetition
                        beyond their expectation, at the rate of long searches)

Standard library only; runs on Python 3.9.
"""
import json
import re
import sys
from pathlib import Path

PARALLEL_MIN_HASHES = 1 << 13  # flock-transcript, search_nonce


def read_kv(path):
    out = {}
    for line in path.read_text().splitlines():
        if ": " in line:
            key, value = line.split(": ", 1)
            out[key.strip()] = value.strip()
    return out


def read_time(err_text):
    """The fields of `/usr/bin/time -l` that the report uses."""
    out = {}
    m = re.search(r"^\s*([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", err_text, re.M)
    if m:
        out["real_s"], out["user_s"], out["sys_s"] = map(float, m.groups())
    for key, label in (
        ("max_rss_bytes", "maximum resident set size"),
        ("peak_footprint_bytes", "peak memory footprint"),
        ("instructions", "instructions retired"),
        ("cycles", "cycles elapsed"),
        ("swaps", "swaps"),
    ):
        m = re.search(r"^\s*(\d+)\s+" + re.escape(label), err_text, re.M)
        if m:
            out[key] = int(m.group(1))
    if "cycles" in out and out.get("user_s", 0) + out.get("sys_s", 0) > 0:
        out["effective_ghz"] = out["cycles"] / (out["user_s"] + out["sys_s"]) / 1e9
    return out


def pow_searches(config):
    """Every proof-of-work search of one proof, as a list of bit counts (0-bit searches hash nothing).
    Only for the outputs of the first bench (run 20261113), which did not print its searches: this list
    misses two searches of the split prover at its last level."""
    levels = len(config["log_inv_rates"])
    folds = [config["initial_k"]] + list(config["recursive_ks"])
    bits = []
    for li in range(levels):
        bits += [config["fold_grinding_bits"][li]] * folds[li]
        bits += [config["claim_batch_grinding_bits"][li]] * config["ood_samples"][li]
        bits.append(config["query_grinding_bits"][li])
        if li + 1 < levels:
            bits.append(config["consistency_batch_grinding_bits"][li])
            bits.append(config["claim_batch_grinding_bits"][li + 1])
    return [b for b in bits if b > 0]


def searches_of(res):
    """The bit counts of the searches of one proof (those of at least one bit), from the bench if it printed
    them (`pow_searches`: fold, claim, consistency, queries), else from the configuration."""
    if "pow_searches" in res:
        s = res["pow_searches"]
        return [b for kind in ("fold", "claim", "consistency", "queries") for b in s[kind] if b > 0]
    return pow_searches(res["config"])


def grind_key(entry):
    """The search of an entry of `pow_grinds` or of `pow_calibration`: leading zero bits, or a threshold."""
    if entry.get("target") is not None:
        return ("target", entry["target"])
    return ("bits", entry["bits"])


def grinds_of(res):
    """The searches of one proof that hash something, as (key, expected hashes): from `pow_grinds` (the bench
    since the run 20261113e), else from the bit counts of `searches_of`."""
    if "pow_grinds" in res:
        g = res["pow_grinds"]
        return [(grind_key(e), float(e["work"])) for kind in ("fold", "claim", "consistency", "queries")
                for e in g[kind] if e["work"] > 0]
    return [(("bits", b), float(1 << b)) for b in searches_of(res)]


def pow_expected(grinds, ctx):
    """(expected hashes, expected ms, expected ms at the rate of long searches alone, searches with no
    calibration) of the searches of one proof, given as (key, expected hashes)."""
    rate_par = ctx.get("pow_hashes_per_ms_parallel")
    rate_seq = ctx.get("pow_hashes_per_ms_sequential")
    cal = {grind_key(c): c for c in ctx.get("pow_calibration") or []}
    hashes, ms, ms_rate, missing = 0.0, 0.0, 0.0, set()
    for key, h in grinds:
        hashes += h
        if not (rate_par and rate_seq):
            continue
        rate = rate_par if h >= PARALLEL_MIN_HASHES else rate_seq
        ms_rate += h / rate
        c = cal.get(key)
        if c:
            ms += c["ms"] / c["searches"] + (h - c["hashes"] / c["searches"]) / rate
        else:
            missing.add(key)
            ms += h / rate
    if not (rate_par and rate_seq):
        return hashes, None, None, missing
    return hashes, ms, ms_rate, (missing if cal else set())


def memory(cell):
    """The memory of a process, and whether part of it was compressed or swapped: its peak footprint
    exceeds its resident memory by more than 2 % and 32 MiB (the rule of the campaign reports)."""
    t = cell.get("time", {})
    fp, rss = t.get("peak_footprint_bytes"), t.get("max_rss_bytes")
    limited = bool(fp and rss and fp > 1.02 * rss and fp - rss > 32 << 20)
    idle = re.search(r"([\d.]+)% idle", cell.get("meta", {}).get("top_before", ""))
    return {"peak_footprint_bytes": fp, "max_rss_bytes": rss, "limited": limited,
            "power": [cell.get("meta", {}).get("power_before"), cell.get("meta", {}).get("power_after")],
            "load_before": cell.get("meta", {}).get("load_before"),
            "idle_before_pct": float(idle.group(1)) if idle else None}


def counters(res):
    """What the prover of a variant used (`counters` of the bench, since the run 20261113d), without the
    values of every repetition."""
    c = (res or {}).get("counters")
    return {k: v for k, v in c.items() if k != "reps"} if c else None


def median(values):
    v = sorted(values)
    n = len(v)
    if n == 0:
        return None
    return v[n // 2] if n % 2 else 0.5 * (v[n // 2 - 1] + v[n // 2])


def parse_cell(folder, name):
    out_path = folder / "cells" / (name + ".out")
    if not out_path.exists():
        return None
    context, results = None, []
    for line in out_path.read_text().splitlines():
        if line.startswith("CONTEXT "):
            context = json.loads(line[len("CONTEXT "):])
        elif line.startswith("RESULT "):
            results.append(json.loads(line[len("RESULT "):]))
    err_path = folder / "cells" / (name + ".err")
    meta_path = folder / "cells" / (name + ".meta")
    return {
        "name": name,
        "context": context,
        "results": results,
        "time": read_time(err_path.read_text()) if err_path.exists() else {},
        "meta": read_kv(meta_path) if meta_path.exists() else {},
    }


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    folder = Path(sys.argv[1])
    statuses = {}
    tsv = folder / "cells.tsv"
    if tsv.exists():
        for line in tsv.read_text().splitlines()[1:]:
            parts = line.split("\t")
            statuses[parts[0]] = parts[1]  # the last attempt wins
    cells = {}
    for name in statuses:
        cell = parse_cell(folder, name)
        if cell is not None:
            cell["status"] = statuses[name]
            cells[name] = cell

    rows, warnings = [], []
    for name, cell in cells.items():
        if name.endswith("-nopow"):
            continue
        twin = cells.get(name + "-nopow")
        ctx = cell["context"] or {}
        if cell["status"] != "ok" or not cell["results"]:
            warnings.append(f"{name}: status {cell['status']}, {len(cell['results'])} results")
            continue
        if twin is None or twin["status"] != "ok":
            warnings.append(f"{name}: no usable -nopow twin")
        rate_par = ctx.get("pow_hashes_per_ms_parallel")
        rate_seq = ctx.get("pow_hashes_per_ms_sequential")
        for res in cell["results"]:
            variant = res["variant"]
            nopow = None
            if twin is not None:
                nopow = next((r for r in twin["results"] if r["variant"] == variant), None)
            grinds = grinds_of(res)
            exp_hashes, exp_ms, exp_ms_rate, missing = pow_expected(grinds, ctx)
            if missing:
                warnings.append(f"{name}/{variant}: no calibration for the searches {sorted(missing)}")
            # the same model per kind of search (the cost of a search does not depend on the others)
            by_kind = None
            if "pow_grinds" in res and exp_ms is not None:
                by_kind = {
                    kind: pow_expected([(grind_key(e), float(e["work"])) for e in res["pow_grinds"][kind]
                                        if e["work"] > 0], ctx)[1]
                    for kind in ("fold", "claim", "consistency", "queries")
                }
                if abs(sum(by_kind.values()) - exp_ms) > 1e-9 * max(exp_ms, 1.0):
                    warnings.append(f"{name}/{variant}: the proofs of work by kind do not add up")
            residual = None
            if nopow is not None and exp_ms is not None and rate_par:
                residual = median([
                    t - (nopow["prove_ms"] + exp_ms + (h - exp_hashes) / rate_par)
                    for t, h in zip(res["prove_ms_reps"], res["pow_hashes_reps"])
                ])
            if abs(exp_hashes - res["pow_expected_hashes"]) > 0.5 + 1e-9 * exp_hashes:
                warnings.append(
                    f"{name}/{variant}: expected hashes {exp_hashes:.0f} here, "
                    f"{res['pow_expected_hashes']:.0f} in the bench"
                )
            if nopow is not None and nopow["proof_bytes"] != res["proof_bytes"]:
                warnings.append(f"{name}/{variant}: proof bytes differ between the cell and its -nopow twin")
            row = {
                "cell": name.split(".")[0],
                "process": name,
                "memory": {"pow": memory(cell), "nopow": memory(twin) if twin is not None else None},
                "variant": variant,
                "log_n": res["log_n"],
                "profile": res["profile"],
                # the log inverse rate of L0, and whether the split configuration is Flock's derivation of the
                # profile at a rate that Flock does not ship (benches before the run 20261113c do not print them)
                "l0_rate": ctx.get("l0_rate", res["config"]["log_inv_rates"][0]),
                "split_derived": bool(ctx.get("split_derived", False)),
                "threads": ctx.get("threads"),
                "reps": ctx.get("reps"),
                "commit_ms": ctx.get("commit_ms"),
                "prove_ms": res["prove_ms"],
                "prove_ms_reps": res["prove_ms_reps"],
                "prove_nopow_ms": nopow["prove_ms"] if nopow else None,
                "prove_nopow_ms_reps": nopow["prove_ms_reps"] if nopow else None,
                "pow_expected_hashes": exp_hashes,
                "pow_expected_ms": exp_ms,
                "pow_expected_ms_by_kind": by_kind,
                "pow_rate_only_ms": exp_ms_rate,
                "pow_model_residual_ms": residual,
                "pow_hashes_mean": sum(res["pow_hashes_reps"]) / len(res["pow_hashes_reps"]),
                "pow_searches_work": [h for _, h in grinds],
                "pow_searches": res.get("pow_searches"),
                "pow_grinds": res.get("pow_grinds"),
                "breakdown_levels": res.get("breakdown_levels"),
                "pow_hashes_per_ms_parallel": rate_par,
                "pow_hashes_per_ms_sequential": rate_seq,
                "prove_expected_ms": (nopow["prove_ms"] + exp_ms) if (nopow and exp_ms is not None) else None,
                "verify_ms": res["verify_ms"],
                "proof_bytes": res["proof_bytes"],
                "breakdown": res["breakdown"],
                "config": res["config"],
                "timings_ms": res.get("timings_ms"),
                "timings_nopow_ms": nopow.get("timings_ms") if nopow else None,
                "counters": {"pow": counters(res), "nopow": counters(nopow)},
            }
            rows.append(row)
        if twin is not None and twin["context"] and ctx.get("commit_ms"):
            # The commitment does not depend on the grinding: both processes measure it.
            row_commit = [ctx["commit_ms"], twin["context"]["commit_ms"]]
            for row in rows:
                if row["process"] == name:
                    row["commit_ms_both"] = row_commit

    out = {
        "folder": str(folder),
        "machine": read_kv(folder / "machine.txt") if (folder / "machine.txt").exists() else {},
        "binaries": (folder / "binaries.txt").read_text().splitlines() if (folder / "binaries.txt").exists() else [],
        "cells": {
            name: {"status": c["status"], "context": c["context"], "time": c["time"], "meta": c["meta"]}
            for name, c in cells.items()
        },
        "rows": rows,
        "warnings": warnings,
    }
    (folder / "results.json").write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    print(f"{folder / 'results.json'}: {len(rows)} rows from {len(cells)} cells")
    for w in warnings:
        print("WARNING", w)
    for row in rows:
        exp = row["prove_expected_ms"]
        print(
            f"  {row['cell']:11} {row['variant']:14} proof {row['proof_bytes'] / 1024:7.1f} KiB  "
            f"prove {row['prove_ms']:7.1f} ms  no PoW {row['prove_nopow_ms'] or float('nan'):7.1f}  "
            f"expected {exp if exp is not None else float('nan'):7.1f}  verify {row['verify_ms']:.2f} ms  "
            f"PoW {row['pow_expected_hashes']:.2e} hashes"
        )


if __name__ == "__main__":
    main()
