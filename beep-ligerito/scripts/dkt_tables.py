#!/usr/bin/env python3
# Tables of the comparison "BEEP-Ligerito against Ligerito under the MCA bound of DKT26" (research, unaudited).
# [AI-drafted (claude-fable-5-2), 2026-11-17, at the author's request ("Can you run a comparison for 100 and 128 bits
# at this error bound?"); please review]
#
#   python3 scripts/dkt_tables.py bench_results/three-way-dkt-20261117 [bench_results/three-way-dkt-20261117-m16 ...]
#
# Reads results.json of the run (scripts/collect.py) and, for the baseline "dkt" at 128 bits, the cells
# "<shape>.dkt-nopow" directly: collect.py makes a row only where a cell ran with its proofs of work. A later folder is a
# rerun of some cells: its rows replace those of the same processes. "prove" is the paper's convention: the median
# time without proofs of work plus the expected time of the searches (prove_expected_ms of collect.py). Where the
# baseline at 128 bits did not run its proofs of work, their time is the expected number of hashes over the hash
# rate of the run (the median over its cells of the rate measured on searches of 2^20 hashes).
import json, sys, math, pathlib, re, statistics

run = pathlib.Path(sys.argv[1])
# Optional later folders (reruns of some cells): a row of a later folder replaces the row of the same process
# name in an earlier one, and a `.dkt-nopow` cell is read from the last folder that has it.
reruns = [pathlib.Path(a) for a in sys.argv[2:]]
res = json.loads((run / "results.json").read_text())
rows, source = {}, {}
for folder in [run, *reruns]:
    for r in json.loads((folder / "results.json").read_text())["rows"]:
        m = re.match(r"m(\d+)-(\d+)$", r["cell"])
        key = (int(m.group(2)), int(m.group(1)), r["variant"])
        rows[key] = r; source[key] = folder.name
SIZES = sorted({k[1] for k in rows})
for folder in reruns:
    extra = json.loads((folder / "results.json").read_text())
    res["cells"].update(extra["cells"])
    res["warnings"] += [f"({folder.name}) {w}" for w in extra["warnings"]]
    print(f"rows of {folder.name} replace those of {run.name} for: " + ", ".join(sorted({r['process'] for r in extra['rows']})))

# hash rates of the campaign (parallel searches: above 2^13 expected hashes)
par = [c["context"]["pow_hashes_per_ms_parallel"] for c in res["cells"].values()
       if c.get("context") and c["context"].get("pow_hashes_per_ms_parallel")]
seq = [c["context"]["pow_hashes_per_ms_sequential"] for c in res["cells"].values()
       if c.get("context") and c["context"].get("pow_hashes_per_ms_sequential")]
PAR, SEQ = statistics.median(par), statistics.median(seq)

def nopow_cell(name):
    out = {}
    found = [f / "cells" / f"{name}.out" for f in [run, *reruns] if (f / "cells" / f"{name}.out").exists()]
    if not found:
        return out
    p = found[-1]
    for l in p.read_text().splitlines():
        if l.startswith("RESULT "):
            r = json.loads(l[7:]); out[r["variant"]] = r
    return out

def work_ms(r):
    ms = 0.0
    for kind in ("fold", "claim", "consistency", "queries"):
        for g in r["pow_grinds"][kind]:
            if g["work"] > 0:
                ms += g["work"] / (PAR if g["work"] > 8192 else SEQ)
    return ms

def fold_work(r):
    return sum(g["work"] for g in r["pow_grinds"]["fold"])

def lg(x):
    return f"2^{math.log2(x):.1f}" if x > 0 else "-"

print(f"run {run.name}: {len(res['rows'])} rows, {len(res['warnings'])} warnings of collect.py; "
      f"hash rate {PAR:.0f}/ms on every thread, {SEQ:.0f}/ms on one (medians over the cells)")
for w in res["warnings"]:
    print("  warning:", w)

def val(bits, n, v, key):
    r = rows.get((bits, n, v))
    return None if r is None else r.get(key)

print("\n=== 100 bits, everything over GF(2^128) except Ligerito (Flock), whose fold challenges are in GF(2^256)")
V100 = ["split", "mcanf-0.02", "dkt-0.02", "dkt-0.005", "dkt-0.002", "dkt-0.001", "beep-0.02", "beep-0.001"]
for title, key, fmt in (("proof size (KiB)", "proof_bytes", lambda x: f"{x/1024:9.1f}"),
                        ("prove (ms): no proofs of work + their expected time", "prove_expected_ms", lambda x: f"{x:9.2f}"),
                        ("prove without proofs of work (ms)", "prove_nopow_ms", lambda x: f"{x:9.2f}"),
                        ("prove as measured with proofs of work (ms, median)", "prove_ms", lambda x: f"{x:9.2f}"),
                        ("expected time of the proofs of work (ms)", "pow_expected_ms", lambda x: f"{x:9.3f}"),
                        ("verify (ms)", "verify_ms", lambda x: f"{x:9.3f}")):
    print(f"--- {title}")
    print("n   " + "".join(f"{v:>12}" for v in V100))
    for n in SIZES:
        print(f"{n:<4}" + "".join(f"{fmt(val(100, n, v, key)):>12}" if val(100, n, v, key) is not None else f"{'-':>12}" for v in V100))
print("--- commit (ms), shared by every variant")
print("    " + "  ".join(f"2^{n}: {rows[(100, n, 'beep-0.001')]['commit_ms']:.1f}" for n in SIZES))
print("--- BEEP-Ligerito (slack 0.001) relative to each baseline: proof size, prove, prove without proofs of work, prove + commit, verify")
for base in ("mcanf-0.02", "dkt-0.02", "dkt-0.005", "dkt-0.002", "dkt-0.001"):
    print(f"  against {base}")
    for n in SIZES:
        b, a = rows[(100, n, "beep-0.001")], rows[(100, n, base)]
        c = b["commit_ms"]
        print(f"    2^{n}: size {100*(b['proof_bytes']/a['proof_bytes']-1):+6.2f}%  prove x{b['prove_expected_ms']/a['prove_expected_ms']:.3f}"
              f"  no-PoW x{b['prove_nopow_ms']/a['prove_nopow_ms']:.3f}  with commit x{(b['prove_expected_ms']+c)/(a['prove_expected_ms']+c):.3f}"
              f"  verify x{b['verify_ms']/a['verify_ms']:.3f}  fold PoW of the baseline {lg(fold_work(a))} hashes = {a['pow_expected_ms_by_kind']['fold'] if a.get('pow_expected_ms_by_kind') else float('nan'):.3f} ms")

print("\n=== 128 bits")
print("--- BEEP-Ligerito (slack 0.001, GF(2^128)) against Ligerito (Flock, fold challenges in GF(2^256), slack 0.02)")
for n in SIZES:
    b, a = rows[(128, n, "beep-0.001")], rows[(128, n, "split")]
    print(f"    2^{n}: size {b['proof_bytes']/1024:7.1f} against {a['proof_bytes']/1024:7.1f} KiB ({100*(b['proof_bytes']/a['proof_bytes']-1):+6.2f}%)"
          f"  prove {b['prove_expected_ms']:8.2f} against {a['prove_expected_ms']:8.2f} ms (x{b['prove_expected_ms']/a['prove_expected_ms']:.3f})"
          f"  verify x{b['verify_ms']/a['verify_ms']:.3f}  BEEP's fold PoW {lg(fold_work(b))} = {b['pow_expected_ms_by_kind']['fold']:.2f} ms")
print("--- the MCA baseline with the bound of DKT26 over GF(2^128) at 128 bits, per slack: proof size against BEEP-0.001,")
print("    its prover without proofs of work (same process as BEEP), the expected hashes of its fold proofs of work,")
print("    their time (expected hashes over the measured rate), and the measured prover where the cell ran with them")
for n in SIZES:
    cell = nopow_cell(f"m{n}-128.dkt-nopow")
    beep = cell.get("beep-0.001")
    for eta in ("0.1", "0.05", "0.02"):
        d = cell.get(f"dkt-{eta}")
        if d is None or beep is None:
            print(f"    2^{n} dkt-{eta}: no cell"); continue
        measured = rows.get((128, n, f"dkt-{eta}"))
        m = (f"measured prove {measured['prove_ms']:.1f} ms (expected {measured['prove_expected_ms']:.1f})" if measured else "not run with proofs of work")
        pw = work_ms(d)
        print(f"    2^{n} dkt-{eta:<5}: size {d['proof_bytes']/1024:7.1f} KiB (BEEP {100*(beep['proof_bytes']/d['proof_bytes']-1):+6.2f}%)"
              f"  no-PoW prove {d['prove_ms']:8.2f} ms (BEEP {beep['prove_ms']:8.2f}, x{beep['prove_ms']/d['prove_ms']:.3f})"
              f"  fold PoW {lg(fold_work(d))} hashes -> {pw/1000:9.2f} s; {m}")
    b = rows[(128, n, "beep-0.001")]
    print(f"    2^{n} beep-0.001: prove {b['prove_expected_ms']:.2f} ms with its proofs of work ({lg(fold_work(b))} hashes on the fold challenges, {b['pow_expected_ms']:.2f} ms in all)")

print("\n=== memory and disturbances")
for name, c in sorted(res["cells"].items()):
    t = c.get("time") or {}
    rss, foot = t.get("max_rss_bytes", 0) / 2**30, t.get("peak_footprint_bytes", 0) / 2**30
    if foot > 1.02 * rss + 0.05 or c.get("status") != "ok":
        print(f"  {name}: status {c.get('status')}, rss {rss:.2f} GB, footprint {foot:.2f} GB (part of the memory was compressed)")
