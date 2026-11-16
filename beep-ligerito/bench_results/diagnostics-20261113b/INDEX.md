<!-- [AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request: the index of the diagnostic runs of the affine prover's anomaly; written by a script from the outputs in this folder; please review] -->

# Diagnostic runs of November 13, 2026 (17:57 to 18:21)

Not measurements: these runs were launched by hand, without the gate (except f04 to f06) and without a
cool-down (except where stated), to look for the reason why the prover of the affine variant is slower in
the shared processes with proofs of work of the run `three-way-20261113b` (see `../../README.md`, "Flags").
The bench binary is the one of that run. Each file is the output of one process of
`ligerito_three_way`; the table has the medians of the prove times, in ms.

For comparison, in the run: at 2^20 words the affine prover has 9.0 ms with proofs of work and 6.3 ms without;
at 2^22 words 25.1 and 18.4; at 2^24 words 74.1 and 50.9.

| file | words | proofs of work | how it was launched | reps | affine | split | BEEP, 0.02 |
|---|---|---|---|---:|---:|---:|---:|
| `a01.out` | 2^22 | yes | variants=affine | 7 | 20.0 |  |  |
| `a02.out` | 2^22 | yes | variants=split,affine | 7 | 19.5 | 25.0 |  |
| `a03.out` | 2^22 | yes | variants=affine,beep (eta=0.02) | 7 | 19.1 |  | 31.3 |
| `a04.out` | 2^22 | yes | variants=beep,affine (eta=0.02) | 7 | 18.9 |  | 30.8 |
| `a05.out` | 2^22 | yes | variants=affine,affine-small | 7 | 19.1 |  |  |
| `a06.out` | 2^22 | yes | variants=split,affine,affine-small | 7 | 19.8 | 25.3 |  |
| `a07.out` | 2^22 | yes | variants=affine,beep (two slacks) | 7 | 18.8 |  | 30.5 |
| `a08.out` | 2^22 | yes | variants=affine,beep,control (two slacks) | 7 | 19.2 |  | 30.7 |
| `a09.out` | 2^22 | yes | variants=affine,beep,control (eta=0.02) | 7 | 18.8 |  | 31.1 |
| `a10.out` | 2^22 | yes | all seven provers, as the cell of the run | 7 | 19.9 | 27.6 | 31.5 |
| `a11.out` | 2^22 | no | variants=affine | 7 | 18.7 |  |  |
| `a12.out` | 2^22 | no | variants=split,affine | 7 | 18.4 | 24.0 |  |
| `a13.out` | 2^22 | no | variants=affine,beep (eta=0.02) | 7 | 18.1 |  | 23.6 |
| `a14.out` | 2^22 | no | all seven provers | 7 | 18.9 | 24.6 | 24.2 |
| `b01.out` | 2^22 | yes | all seven provers, outside the sandbox | 9 | 19.8 | 26.3 | 31.3 |
| `b02.out` | 2^22 | yes | variants=affine, outside the sandbox | 9 | 19.5 |  |  |
| `b03.out` | 2^22 | no | all seven provers, outside the sandbox | 9 | 18.5 | 23.9 | 23.9 |
| `c01.out` | 2^22 | yes | the command of the cell under `/usr/bin/time -l`, with the driver's environment | 9 | 19.7 | 26.0 | 31.9 |
| `c02.out` | 2^22 | yes | the same after `sleep 45` | 9 | 19.4 | 25.9 | 31.7 |
| `c03.out` | 2^22 | yes | the same after `sleep 45`, again | 9 | 19.7 | 25.4 | 32.1 |
| `d01.out` | 2^22 | yes | from Python with start_new_session=True (as the gate does) | 9 | 19.8 | 26.0 | 32.1 |
| `d02.out` | 2^22 | yes | directly, right after d01 | 9 | 20.3 | 25.9 | 31.3 |
| `d03.out` | 2^22 | yes | from Python with start_new_session=True, again | 9 | 20.0 | 26.2 | 31.9 |
| `d04.out` | 2^22 | no | from Python with start_new_session=True | 9 | 18.5 | 23.9 | 23.9 |
| `e01.out` | 2^22 | yes | as a background task of the session, no gate | 9 | 20.2 | 26.0 | 31.6 |
| `e02.out` | 2^22 | no | as a background task of the session, no gate | 9 | 18.3 | 24.4 | 24.2 |
| `f01.out` | 2^22 | yes | scripts/run_cells.zsh on a one-cell file, no gate, cool-down 3 s | 9 | 19.9 | 25.8 | 31.4 |
| `f02.out` | 2^22 | yes | directly, with a file on standard input (as in the driver's loop) | 9 | 19.9 | 26.1 | 31.5 |
| `f03.out` | 2^22 | yes | directly, with standard error to a file | 9 | 19.7 | 25.8 | 31.1 |
| `f04.out` | 2^22 | yes | bench_gate.py (--min-idle 50 --hold-seconds 5) + the driver on a one-cell file, cool-down 3 s | 9 | 20.1 | 26.0 | 31.6 |
| `f05.out` | 2^22 | yes | the same with the cool-down of 45 s | 9 | 21.7 | 27.8 | 33.4 |
| `f06.out` | 2^22 | yes | bench_gate.py with the settings of the run (--min-idle 80 --hold-seconds 60) + the driver on a one-cell file, cool-down 45 s, as a background task | 9 | 19.9 | 26.0 | 31.6 |
| `g01.out` | 2^20 | yes | the cell fast20, directly | 9 | 7.8 | 10.1 | 11.0 |
| `g02.out` | 2^20 | no | the cell fast20, directly | 9 | 6.3 | 8.5 | 7.9 |
| `g03.out` | 2^20 | yes | the driver on a two-cell file (fast20, fast22), no gate, cool-down 45 s: first cell | 9 | 7.5 | 9.8 | 11.0 |
| `g04.out` | 2^22 | yes | the same: second cell | 9 | 19.7 | 25.9 | 31.0 |
| `h01.out` | 2^24 | yes | the cell fast24 with reps=5, directly (7.2 GB of memory unused before) | 5 | 53.2 | 71.9 | 88.2 |
| `h02.out` | 2^24 | yes | the same while another process holds 4 GiB (3.6 GB unused before) | 5 | 54.4 | 73.6 | 88.9 |
| `h03.out` | 2^24 | yes | the same with one busy core elsewhere | 5 | 56.5 | 75.9 | 96.0 |
| `h04.out` | 2^24 | yes | the same with three busy cores elsewhere | 5 | 70.7 | 90.8 | 124.5 |
| `h05.out` | 2^24 | no | the cell fast24 with reps=5, directly | 5 | 51.5 | 69.5 | 73.9 |
| `h06.out` | 2^24 | yes | the cell fast24 with reps=5 while `dd if=/dev/zero of=/dev/null bs=64m` runs | 5 | 52.7 | 72.9 | 87.9 |
| `h07.out` | 2^24 | yes | the cell fast24 with reps=5 while another process maps, touches and unmaps 256 MiB in a loop | 5 | 60.1 | 80.8 | 97.6 |
