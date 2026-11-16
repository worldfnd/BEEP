<!-- [AI-drafted (claude-opus-5-5), 2026-11-16, at the author's request ("Create a new repository called BEEP, in the folder albertgarretafontelles. It should contain: the BEEP paper (currently in the typst folder), Lean formalizations of Theorems 3.4 and Theorem 5.3, the BEEP-Ligerito variant we worked on"; then "If a lean implementation is missing, leave it out. We will work on it later"): this README and .gitignore; please review] -->

# BEEP: Better Elimination of Pretenders

**Research, unaudited.** The BEEP paper, the Lean formalization of one of its results, and the
implementation and measurements behind its Experiments section.

| folder | contents |
|---|---|
| `typst/` | the paper, `deep+.typ` (with `batch.typ`, `layout.typ`, `environments.typ`, `bibliography.bib`); `tables/experiments.json`, which the Experiments section reads, and `scripts/make_tables.py`, which writes it from the runs in `7-beep-ligerito/` |
| `lean/` | Lean 4 / Mathlib v4.30.0: Theorem 5.3 and Lemma 5.5 (affine folds for Reed-Solomon codes) in `BEEP/AffineMain.lean`. Theorem 3.4 is not formalized yet. See `lean/README.md` |
| `7-beep-ligerito/` | BEEP-Ligerito on a pinned copy of Flock (branch `affine-fold-f128`, MIT OR Apache-2.0, see `VENDORED.md`), compared with Flock's Ligerito and with affine Ligerito at 128 and 100 bits; the bench, the run scripts, the raw outputs of every run, and `WORKLOG.md`. See `7-beep-ligerito/README.md` |

## The paper

```sh
cd typst
typst compile deep+.typ /some/folder/outside/the/repository/beep.pdf     # Typst 0.15.1; 56 pages on 2026-11-16
python3 scripts/make_tables.py        # rewrites tables/experiments.json from the runs of record (Python 3.9, standard library)
```

No number of the Experiments section is typed by hand: the section reads `tables/experiments.json`
through `num("key")`, and a missing key prints a red "pending". The PDF is not tracked.

## The Lean formalization

```sh
lean/check.sh          # type-checks BEEP/AffineMain.lean with the Mathlib build of ~/math in lean, about 30 s
```

## BEEP-Ligerito

Every cargo command in `7-beep-ligerito/flock` sets that folder's own target directory: the shell on this
machine exports a `CARGO_TARGET_DIR` that belongs to another project, and building without the override
replaces that project's binaries.

```sh
cd 7-beep-ligerito/flock
export CARGO_TARGET_DIR=$PWD/../target RUSTFLAGS="-C target-cpu=native"
cargo test --offline --release -p flock-core --lib beep
```

Timed runs go through `7-beep-ligerito/scripts/bench_gate.py` (a machine-wide lock, `/tmp/bitz-bench.lock`, and
a wait for an idle CPU), on AC power, outside any sandbox; nothing else should be built or benchmarked while one
runs. The commands are in "Reproducing" of `7-beep-ligerito/README.md`.

## Where this comes from

The three folders were copied on November 16, 2026 from the repository `random-domain-ligerito` (commit
`a1208d1`, plus the uncommitted changes to `typst/deep+.typ` of that day), where the work was done; `lean/` was
`typst/lean/` there. The folder names `typst/` and `7-beep-ligerito/` are kept so that the paths in the scripts,
in the comments of the code (some of which are covered by the hashes that the runs record) and in the paper stay
valid. Changed in the copy: the gate of the timed runs is now `7-beep-ligerito/scripts/bench_gate.py` (a copy of
the one in `5-implementation/scripts` there); the comments and README of `lean/` cite the paper's current numbers
(Theorem 5.3 rather than Theorem 30); the paths in the READMEs; `7-beep-ligerito/WORKLOG.md` is new (the phases
of the work on that folder, from `5-implementation/WORKLOG.md` there). Checked after the copy: the paper compiles
to the same text, `make_tables.py` writes the same `experiments.json` with no warning, `beep_params.py --check`
passes on the run of record, and `lean/check.sh` passes. The Rust code was not rebuilt here; it is byte for byte
the code of the runs.

Files written or revised with an AI carry a marker (`[AI-drafted ...]`, `[AI-revised ...]`) that says by which
model, when and at whose request. The markers written before the copy describe the history in
`random-domain-ligerito`, and the paths they mention (such as `.claude/scratch/...`) are paths of that
repository.
