#!/usr/bin/env python3
"""Ligerito (Flock) against BEEP-Ligerito, side by side (research, unaudited).

[AI-drafted (claude-fable-5-2), 2026-11-17, at the author's request ("I want to compare the original Ligerito
from Flock and ours. How can I do that?"); please review]

    python3 scripts/compare.py                    the runs that the paper quotes (nothing is measured)
    python3 scripts/compare.py <run folder> ...   other runs; a later folder replaces the rows of an earlier one
    python3 scripts/compare.py --measure <label> --sizes 16,20 [--bits 128] [--reps 15] [--gate]
                                                  measures these sizes first (bench_results/three-way-<label>)
    --ours <variant>                              what "ours" is (default beep-0.001)

The two columns.

  * "Flock" is the variant `split` of the bench: Flock's prover and verifier, unchanged (VENDORED.md), on the
    parameters that Flock ships for the size (profile `fast` at 128 bits, `fast100` at 100 bits; Flock's own
    derivation of the profile for 2^14 elements, for which it ships none). Its fold challenges are in GF(2^256).
  * "ours" is `beep-0.001` unless `--ours` says otherwise: BEEP-Ligerito at the slack 0.001, every challenge in
    GF(2^128). Other variants of ours that a run may have: `beep-0.02` (BEEP-Ligerito at Flock's slack), and
    `dkt-<slack>`, `mcanf-0.02` (our Ligerito over GF(2^128) with no samples, at 100 bits).

In the bench both open the same commitment, and every proof is checked by its verifier. "prove" is the paper's
convention: the median time without proofs of work plus the expected time of the proofs of work (`collect.py`).
The second table has the two parts and the median time with the proofs of work as they happened.

`--measure` takes the lines of scripts/cells_dkt.txt for the sizes (2^14, 2^16, ..., 2^26 elements): Flock's
prover and ours in separate processes, each with and without proofs of work. It hands them to
scripts/run_cells.zsh and then to scripts/collect.py. Without `--gate` it is a quick look (5 s between the
processes, no wait for an idle machine). With `--gate` it goes through scripts/bench_gate.py with the settings
of the run that the paper quotes (80 % idle CPU before the run and before every process, 20 s between them, 15
repetitions): run it from a terminal, on AC power, and leave the machine alone. The driver's variables
(CAMPAIGN_COOLDOWN, CAMPAIGN_IDLE_EACH, ..., see scripts/run_cells.zsh) are passed on if they are set. A row
with a `*` had a process with part of its memory compressed, and its times are not to be used: Flock's prover
takes 10.7 GiB for 2^26 elements, and ours 9.2 GiB.

Standard library only; runs on Python 3.9.
"""
import argparse
import json
import math
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BENCH = ROOT / "bench_results"
FLOCK = "split"


def paper_runs():
    """The runs that the paper's tables read: RUN and RERUNS of ../paper/scripts/tables128.py."""
    text = (ROOT.parent / "paper" / "scripts" / "tables128.py").read_text()
    run = re.search(r'^RUN = "([^"]+)"', text, re.M)
    reruns = re.search(r"^RERUNS = \(([^)]*)\)", text, re.M)
    if not run or not reruns:
        sys.exit("cannot read RUN and RERUNS in paper/scripts/tables128.py: name the run folders")
    return [BENCH / name for name in [run.group(1)] + re.findall(r'"([^"]+)"', reruns.group(1))]


def load(folders):
    """Rows by (bits of security, log2 of the size, variant); a later folder replaces an earlier one."""
    rows, notes = {}, []
    for folder in folders:
        path = folder / "results.json"
        if not path.exists():
            sys.exit(f"{path} is missing: run `python3 scripts/collect.py {folder}` first")
        res = json.loads(path.read_text())
        machine = res.get("machine", {})
        notes.append(f"{folder.name}: {machine.get('date', '?')}, {machine.get('machdep.cpu.brand_string', '?')}, "
                     f"{machine.get('power', '?')}, cooldown {machine.get('cooldown', '?')}")
        notes += [f"  warning of collect.py: {w}" for w in res.get("warnings", [])]
        for row in res["rows"]:
            context = (res["cells"].get(row.get("process") or row["cell"]) or {}).get("context") or {}
            bits = context.get("target_bits") or re.search(r"-(\d+)$", row["cell"]).group(1)
            rows[(int(float(bits)), int(row["log_n"]), row["variant"])] = row
    return rows, notes


def limited(row):
    """True if a process of the row had part of its memory compressed (the rule of collect.py)."""
    return any((part or {}).get("limited") for part in (row.get("memory") or {}).values())


def commit(f, o):
    """The commitment: the mean over the processes of the two rows (the rule of the paper's table)."""
    values = []
    for row in (f, o):
        values += row.get("commit_ms_both") or [row["commit_ms"]]
    return sum(values) / len(values)


def down(x, digits):
    return math.floor(x * 10 ** digits) / 10 ** digits


def up(x, digits):
    return math.ceil(x * 10 ** digits) / 10 ** digits


def show(rows, bits, ours):
    sizes = sorted(n for (b, n, v) in rows if b == bits and v == FLOCK and (bits, n, ours) in rows)
    if not sizes:
        return False
    print(f"\n=== {bits} bits of security: Ligerito (Flock) [{FLOCK}] against ours [{ours}]")
    print("                  |      Ligerito (Flock)       |            ours             |    ours against Flock")
    print("  size    commit  | proof KiB   prove   verify  | proof KiB   prove   verify  |   proof   prove  verify")
    pairs = []
    for n in sizes:
        f, o = rows[(bits, n, FLOCK)], rows[(bits, n, ours)]
        mark = "*" if limited(f) or limited(o) else " "
        pairs.append((n, f, o, mark))
        print(f"  2^{n:<3}{mark}{commit(f, o):8.2f}  |"
              f" {f['proof_bytes'] / 1024:9.1f} {f['prove_expected_ms']:7.2f} {f['verify_ms']:8.3f}  |"
              f" {o['proof_bytes'] / 1024:9.1f} {o['prove_expected_ms']:7.2f} {o['verify_ms']:8.3f}  |"
              f" {100 * (o['proof_bytes'] / f['proof_bytes'] - 1):+6.1f}%  x{o['prove_expected_ms'] / f['prove_expected_ms']:.2f}"
              f"   x{o['verify_ms'] / f['verify_ms']:.2f}")
    print("  times in ms; commit: the commitment, the same computation for both (the mean over their processes);")
    print("  prove: the opening, without the commitment, with the proofs of work at their expected cost")
    print("\n  the prover in detail (ms)")
    print("          | without proofs of work  | expected time of them |  as measured with them")
    print("  size    |   Flock    ours  ratio  |    Flock      ours    |   Flock    ours  ratio")
    for n, f, o, mark in pairs:
        print(f"  2^{n:<3}{mark}  | {f['prove_nopow_ms']:7.2f} {o['prove_nopow_ms']:7.2f}  x{o['prove_nopow_ms'] / f['prove_nopow_ms']:.2f}  |"
              f" {f['pow_expected_ms']:8.2f}  {o['pow_expected_ms']:8.2f}    |"
              f" {f['prove_ms']:7.2f} {o['prove_ms']:7.2f}  x{o['prove_ms'] / f['prove_ms']:.2f}")
    clean = [(f, o) for _, f, o, mark in pairs if mark == " "]
    if len(clean) > 1:
        size =[100 * (1 - o["proof_bytes"] / f["proof_bytes"]) for f, o in clean]
        prove = [o["prove_expected_ms"] / f["prove_expected_ms"] for f, o in clean]
        verify = [o["verify_ms"] / f["verify_ms"] for f, o in clean]
        left = "" if len(clean) == len(pairs) else " (without the rows with a *)"
        print(f"\n  ours against Flock over {len(clean)} sizes{left}: proofs {down(min(size), 1):.1f} to {up(max(size), 1):.1f} % smaller,"
              f" prove x{down(min(prove), 2):.2f} to x{up(max(prove), 2):.2f}, verify x{down(min(verify), 2):.2f} to x{up(max(verify), 2):.2f}"
              " (lower ends rounded down, upper ends up)")
    if len(clean) < len(pairs):
        print("  * a process of this row had part of its memory compressed: its times are not to be used")
    return True


def measure(label, sizes, bits, reps, gate):
    pattern = re.compile(rf"m({'|'.join(str(n) for n in sizes)})-{bits}\.(split|fold)(-nopow)?\s")
    lines = [line for line in (HERE / "cells_dkt.txt").read_text().splitlines() if pattern.match(line)]
    if len(lines) != 4 * len(sizes):
        sys.exit(f"scripts/cells_dkt.txt has {len(lines)} cells for the sizes {sizes} at {bits} bits, not {4 * len(sizes)}: "
                 "it has 2^14, 2^16, ..., 2^26 at 100 and 128 bits (write a cells file for another size)")
    folder = Path(os.environ.get("CAMPAIGN_OUT") or BENCH / f"three-way-{label}")
    with tempfile.NamedTemporaryFile("w", suffix=".txt", prefix="cells_compare_", delete=False) as cells:
        cells.write("# written by scripts/compare.py --measure: lines of scripts/cells_dkt.txt\n" + "\n".join(lines) + "\n")
    env = dict(os.environ, CAMPAIGN_REPS=str(reps))
    command = ["zsh", str(HERE / "run_cells.zsh"), label, cells.name]
    if gate:
        # The settings of the run that the paper quotes (WORKLOG.md, phase BEEP-DKT-baseline).
        for key, value in (("CAMPAIGN_COOLDOWN", "20"), ("CAMPAIGN_IDLE_EACH", "1"), ("CAMPAIGN_IDLE_HOLD", "20")):
            env.setdefault(key, value)
        command = [sys.executable, str(HERE / "bench_gate.py"), "run", "--label", f"beep-{label}",
                   "--min-idle", "80", "--hold-seconds", "40", "--"] + command
    else:
        env.setdefault("CAMPAIGN_COOLDOWN", "5")
        print("a quick look: not through the gate (`--gate` for a measurement of record)", flush=True)
    if subprocess.run(command, env=env, cwd=ROOT).returncode != 0:
        sys.exit(f"the run failed: see {folder}/campaign.log")
    subprocess.run([sys.executable, str(HERE / "collect.py"), str(folder)], cwd=ROOT, check=True)
    return folder


def main():
    parser = argparse.ArgumentParser(description="Ligerito (Flock) against BEEP-Ligerito, side by side.")
    parser.add_argument("folders", nargs="*", type=Path, help="run folders (default: the runs of the paper)")
    parser.add_argument("--ours", default="beep-0.001", help="the variant of ours (default beep-0.001)")
    parser.add_argument("--measure", metavar="LABEL", help="measure first, into bench_results/three-way-LABEL")
    parser.add_argument("--sizes", default="20", help="with --measure: log2 of the sizes, e.g. 16,20,24")
    parser.add_argument("--bits", type=int, default=128, choices=(100, 128), help="with --measure: bits of security")
    parser.add_argument("--reps", type=int, default=15, help="with --measure: repetitions per process (default 15)")
    parser.add_argument("--gate", action="store_true", help="with --measure: through scripts/bench_gate.py")
    args = parser.parse_args()
    if args.measure:
        folders = [measure(args.measure, [int(s) for s in args.sizes.split(",")], args.bits, args.reps, args.gate)]
    else:
        folders = args.folders or paper_runs()
    rows, notes = load(folders)
    print("\n".join(notes))
    shown = [show(rows, bits, args.ours) for bits in sorted({b for (b, _, _) in rows}, reverse=True)]
    if not any(shown):
        variants = sorted({v for (_, _, v) in rows})
        sys.exit(f"no size has both `{FLOCK}` and `{args.ours}`; variants of these runs: {', '.join(variants)}")


if __name__ == "__main__":
    main()
