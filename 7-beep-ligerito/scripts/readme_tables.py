#!/usr/bin/env python3
"""The tables of README.md, as Markdown, from the tables that the paper reads.

[AI-drafted (claude-fable-5-2), 2026-11-14, at the author's request: so that the numbers of the README are
written by a script; research, unaudited; please review]
[AI-revised (claude-fable-5-2), 2026-11-14: the table `asteps` (the affine variant as it ships, with our prover,
without the sample on its first commitment, with both), and the affine columns of `time`]
[AI-revised (claude-fable-5-2), 2026-11-14: the table `main100` (the comparison at 100 bits)]

    python3 scripts/readme_tables.py            # prints the six tables (from the folder 7-beep-ligerito)
    python3 scripts/readme_tables.py main       # one of: main, main100, steps, asteps, time, hybrid

Reads ../typst/tables/experiments.json, which ../typst/scripts/make_tables.py writes from a run's results.json
(and from its reruns), and turns the Typst markup of its cells into plain text. Standard library only; runs on
Python 3.9.
"""
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent.parent / "typst" / "tables" / "experiments.json"

HEADERS = {
    "main": ["words", "rate", "variant", "proof (KiB)", "prove (ms)", "no grinding (ms)",
             "grinding (10^6 hashes)", "verify (ms)"],
    "main100": ["words", "rate", "variant", "proof (KiB)", "prove (ms)", "no grinding (ms)",
                "grinding (10^6 hashes)", "verify (ms)"],
    "steps": ["words", "rate", "eta", "BEEP", "first sample", "three passes", "whole bits", "all three", "affine"],
    "asteps": ["words", "rate", "eta", "affine as Flock ships it", "our prover", "no first sample", "both (the tables)",
               "BEEP"],
    "time": ["words", "rate", "eta", "samples", "folds", "rest", "total", "control", "affine: folds", "affine: total",
             "fold grinding (10^6 hashes)", "all grinding (ms)"],
    "hybrid": ["words", "rate", "eta", "fold bits, BEEP", "fold bits, affine charge", "hashes, BEEP (10^6)",
               "hashes, affine charge (10^6)", "prove, BEEP (ms)", "prove, affine charge (ms)",
               "the same from BEEP's time without grinding (ms)", "BEEP without grinding (ms)", "affine (ms)",
               "proof (KiB)"],
}
# the first columns that the paper leaves empty in the rows of a group, to fill again
LEADING = {"main": 2, "main100": 2, "steps": 2, "asteps": 2, "time": 2, "hybrid": 2}


def plain(cell):
    """A cell of Typst markup as plain text."""
    s = cell.replace("$", "").replace("\\/", "/").replace("\\*", "*")
    s = re.sub(r"\^\((\d+)\)", r"^\1", s)
    s = re.sub(r"#super\[(.*?)\]", r"\1", s)
    return s.strip()


def table(name, data):
    rows = data["tables"][name]
    out = ["| " + " | ".join(HEADERS[name]) + " |",
           "|" + "|".join(["---"] * LEADING[name] + ["---"] + ["---:"] * (len(HEADERS[name]) - LEADING[name] - 1)) + "|"]
    last = [""] * LEADING[name]
    for row in rows:
        cells = [plain(c) for c in row]
        for i in range(LEADING[name]):
            if cells[i]:
                last[i] = cells[i]
            cells[i] = last[i]
        if len(cells) != len(HEADERS[name]):
            sys.exit(f"table {name}: a row has {len(cells)} cells, the header has {len(HEADERS[name])}")
        out.append("| " + " | ".join(cells) + " |")
    return "\n".join(out)


def main():
    data = json.loads(SOURCE.read_text())
    names = sys.argv[1:] or list(HEADERS)
    for name in names:
        if name not in HEADERS:
            sys.exit(__doc__)
        source = data.get("results100", data["results"]) if name.endswith("100") else data["results"]
        print(f"<!-- {name}: scripts/readme_tables.py {name}, from {source} -->")
        print(table(name, data))
        print()


if __name__ == "__main__":
    main()
