#!/usr/bin/env python3
"""A/B: the bench binary of the original folder (random-domain-ligerito/7-beep-ligerito, built 2026-11-14, the
binary of the run 100bits-3) against the one of BEEP/beep-ligerito (today), on the same cells, alternating.
Without proofs of work (FLOCK_NO_GRIND=1), so that the times are those of the provers' arithmetic.

    python3 ab_compare.py
"""
import json, os, statistics, subprocess, sys

OLD = "/Users/albertgarretafontelles/random-domain-ligerito/7-beep-ligerito/target/release/deps/ligerito_three_way-e93fe6fa1d98f987"
NEW = "/Users/albertgarretafontelles/BEEP/beep-ligerito/target/release/deps/ligerito_three_way-e93fe6fa1d98f987"
CELLS = [
    ("2^20, 128 bits", "log_n=20 profile=fast bits=128 rates=1,3,5 eta=0.02,0.001 variants=split,beep,control"),
    ("2^22, 128 bits", "log_n=22 profile=fast bits=128 rates=1,3,5,7 eta=0.02,0.001 variants=split,beep,control"),
    ("2^23, 128 bits", "log_n=23 profile=fast bits=128 rates=1,3,5,7 eta=0.02,0.001 variants=split,beep,control"),
    ("2^22, 100 bits", "log_n=22 profile=fast100 bits=100 rates=1,3,5,7 eta=0.02,0.001 variants=split,beep,control"),
    ("2^23, 100 bits", "log_n=23 profile=fast100 bits=100 rates=1,3,5,7 eta=0.02,0.001 variants=split,beep,control"),
]
ROUNDS, REPS = 3, 9
env = dict(os.environ, FLOCK_NO_GRIND="1")

def run(binary, args):
    out = subprocess.run([binary] + args.split() + [f"reps={REPS}"], capture_output=True, text=True, env=env)
    if out.returncode:
        sys.exit(out.stderr[-2000:])
    res = {}
    for line in out.stdout.splitlines():
        if line.startswith("RESULT "):
            r = json.loads(line[7:])
            res[r["variant"]] = (r["prove_ms_reps"], r["proof_bytes"])
    return res

for label, args in CELLS:
    acc = {"old": {}, "new": {}}
    for _ in range(ROUNDS):
        for tag, binary in (("old", OLD), ("new", NEW)):
            for v, (reps, size) in run(binary, args).items():
                acc[tag].setdefault(v, ([], size))[0].extend(reps)
    print(label)
    for v in sorted(acc["old"]):
        o, n = acc["old"][v], acc["new"][v]
        mo, mn = statistics.median(o[0]), statistics.median(n[0])
        print(f"  {v:12} proof {int(o[1]):7d} / {int(n[1]):7d} bytes   old {mo:7.2f} ms   new {mn:7.2f} ms   new/old {mn / mo:5.3f}   "
              f"(min old {min(o[0]):.2f}, new {min(n[0]):.2f}; {len(o[0])} runs each)")
