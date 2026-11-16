#!/usr/bin/env python3
"""The cells of the comparison at 100 bits (scripts/cells100.txt), from those at 128 bits (scripts/cells.txt).

[AI-drafted (claude-fable-5-2), 2026-11-14, at the author's request ("run experiments for 100 bits of security,
same parameter regimes as for 128 bits of security"); research, unaudited; please review]

    python3 scripts/make_cells100.py            # writes scripts/cells100.txt (from the folder 7-beep-ligerito)
    python3 scripts/make_cells100.py --print    # prints it instead

Every cell of cells.txt becomes a cell with the same name, the same shape, the same rates of the affine and BEEP
ladders, the same slacks and the same variants (but `beepaff`, which has nothing to show when no fold challenge
is ground), and
  * `bits=100`: the affine and BEEP ladders are built for a round-by-round target of 100 bits;
  * `profile=fast100` in place of `fast` and `slim100` in place of `slim`: Flock's configurations at 100 bits
    (at the rates 1/8 and 1/16, Flock's derivation of `slim100` at that rate, as at 128 bits);
  * the fold grinding of the affine ladders for 100 bits (`fold=`, `fold_nf=`, `affine_fold=`,
    `affine_fold_nf=`), recomputed here from the certificates of every fold round (scripts/beep_params.py).
    The slacks of `affine_eta=` do not change: a certificate does not depend on the target.
The shapes (rows and columns per level) are read from the results of the run at 128 bits, and the bench checks
that the ladders at 100 bits have them. Standard library only; runs on Python 3.9.
"""
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RUNS = ["three-way-20261114g", "three-way-20261114g-add2"]  # where the shapes of the cells are recorded
LAM = 100

spec = importlib.util.spec_from_file_location("beep_params", HERE / "beep_params.py")
bp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bp)


def shapes():
    """(log_n, initial_k, recursive_ks, rates) of the affine ladder of every shape, from the runs at 128 bits."""
    out = {}
    for run in RUNS:
        path = ROOT / "bench_results" / run / "results.json"
        for r in json.loads(path.read_text())["rows"]:
            if r["variant"] in ("affine", "affine-small"):
                cfg = r["config"]
                out.setdefault(r["cell"], (r["log_n"], cfg["initial_k"], list(cfg["recursive_ks"]),
                                           list(cfg["log_inv_rates"])))
    return out


def fold_args(log_n, k0, ks, rates, etas):
    """The fold grinding per level at 100 bits of the affine ladder at the slacks `etas` (one per level), with
    and without the out of domain sample on the first commitment: `affine_level` and `affine_no_first_sample`
    of scripts/beep_params.py, as its `--check` redoes them for the rows of a run."""
    levels, c = [], log_n
    for li, (k, rate, eta) in enumerate(zip([k0] + ks, rates, etas)):
        c -= k
        lv = bp.affine_level(c + rate, rate, c, k, eta, lam=LAM)
        if lv is None:
            sys.exit(f"level {li}: no certificate at slack {eta}")
        lv.update(folds=k, log_msg_cols=c, log_inv_rate=rate, log_n_block=c + rate, eta=eta)
        levels.append(lv)
    fold = [lv["grinding"] for lv in levels]
    nf = bp.affine_no_first_sample(levels[0], lam=LAM)["grinding"]
    return fold, [nf] + fold[1:]


def convert(line, shape_of):
    words = line.split()
    name, rest = words[0], words[1:]
    shape = name.split(".")[0]
    shape = shape[:-len("-nopow")] if shape.endswith("-nopow") else shape
    if shape not in shape_of:
        sys.exit(f"{name}: no shape recorded for {shape}")
    log_n, k0, ks, rates = shape_of[shape]
    kv = {}
    order = []
    for w in rest:
        key, _, value = w.partition("=")
        kv[key] = value
        order.append(key)
    if [int(x) for x in kv["rates"].split(",")] != rates or int(kv["log_n"]) != log_n:
        sys.exit(f"{name}: the rates or the size differ from the recorded shape")
    kv["profile"] = {"fast": "fast100", "slim": "slim100"}[kv.get("profile", "fast")]
    if "profile" not in order:
        order.insert(order.index("log_n") + 1, "profile")
    kv["bits"] = str(LAM)
    order.insert(order.index("profile") + 1, "bits")
    lst = lambda v: ",".join(str(x) for x in v)
    if "fold" in kv:
        fold, fold_nf = fold_args(log_n, k0, ks, rates, ["0.02"] * len(rates))
        kv["fold"] = lst(fold)
        if "fold_nf" in kv:
            kv["fold_nf"] = lst(fold_nf)
    if "affine_eta" in kv:
        fold, fold_nf = fold_args(log_n, k0, ks, rates, kv["affine_eta"].split(","))
        kv["affine_fold"] = lst(fold)
        if "affine_fold_nf" in kv:
            kv["affine_fold_nf"] = lst(fold_nf)
    if "beepaff" in kv:
        del kv["beepaff"]
        order.remove("beepaff")
    if "variants" in kv:
        kv["variants"] = ",".join(v for v in kv["variants"].split(",") if v != "beepaff")
    return name + " " + " ".join(f"{k}={kv[k]}" for k in order)


def main():
    shape_of = shapes()
    out = [
        "# The cells of the comparison of Ligerito variants at 100 bits (research, unaudited).",
        "# [AI-drafted (claude-fable-5-2), 2026-11-14, at the author's request (\"run experiments for 100 bits of security,",
        "#  same parameter regimes as for 128 bits of security\"); please review]",
        "# Written by scripts/make_cells100.py from scripts/cells.txt: do not edit by hand. The same cells, with",
        "# bits=100, Flock's profiles fast100 and slim100 in place of fast and slim, the fold grinding of the affine",
        "# ladders for 100 bits, and without the variant beepaff. See cells.txt for the format and the variants.",
        "",
    ]
    for line in (HERE / "cells.txt").read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        out.append(convert(line, shape_of))
    text = "\n".join(out) + "\n"
    if "--print" in sys.argv[1:]:
        sys.stdout.write(text)
    else:
        (HERE / "cells100.txt").write_text(text)
        print(f"{HERE / 'cells100.txt'}: {len(out) - 7} cells")


if __name__ == "__main__":
    main()
