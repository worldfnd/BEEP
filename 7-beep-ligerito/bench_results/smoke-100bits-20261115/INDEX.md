<!-- [AI-drafted (claude-fable-5-2), 2026-11-15, at the author's request ("run experiments for 100 bits of security, same parameter regimes as for 128 bits of security"); please review] -->

# Smoke run before the campaign 100bits-3 (November 15, 2026, 01:08)

Two cells of `scripts/cells100.txt`, run by hand a few minutes before the campaign `three-way-100bits-3`, with
its bench binary (`80c4da9a5f673136`), 5 repetitions each, under `/usr/bin/time -l`. This is not a timed run:
no gate, no cool-down.

| files | cell |
|---|---|
| `fast24.affine-nopow.out`, `.err` | the four affine provers at slack 0.02, without proofs of work, for 2^24 words at rate 1/2 |
| `sixteenth24.affine-nopow.out`, `.err` | the same for 2^24 words at rate 1/16 |

`.out` is the output of the bench (one `RESULT` line per prover), and `.err` that of `time -l` (resident memory
and peak footprint of the process).

Why: the machine had 3 to 5 GB of unused memory, less than the largest cells take, and a watcher had waited 14
hours for more (`../three-way-100bits-2.gate.log`). The question was whether a campaign started in that state
would give usable times. The second cell has part of its memory compressed (the peak footprint is above the
resident memory), and its provers still take the times of the run 20261114g at 128 bits. The limit on page
faults of the rule for the run 100bits-3 (`FAULTS_BURST` in `../../../typst/scripts/make_tables.py`) was chosen
after this run.

`make_tables.py` reads this folder for the numbers `100:smoke:...` that `../../README.md` quotes in "The run at
100 bits".
