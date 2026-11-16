#!/usr/bin/env python3
"""Parameters of a BEEP fold, checked exactly, and the fold errors of the other analyses.

[AI-drafted (claude-fable-5-2), 2026-11-13, at the author's request; research, unaudited; please review]
[AI-revised (claude-fable-5-2), 2026-11-13, after an independent review: a wider search for the parameters of
the affine bound (Flock's script stops too early for a small slack) and the bound as the published paper
states it; affine ladders at the least certified slack; the recheck of a run also covers the batching of the
queries, the binding samples and the queries, in exact arithmetic]
[AI-revised (claude-fable-5-2), 2026-11-13: the recheck accepts a ladder with no binding sample on the first
commitment, and then checks that the points of the first fold round bind it]
[AI-revised (claude-fable-5-2), 2026-11-13: the recheck of the proofs of work against a threshold: the
numerators of the ground squeezes, and that every threshold is the largest one that keeps its squeeze below
2^-128]
[AI-revised (claude-fable-5-2), 2026-11-13, at the author's request: `--beep-affine-charge`, the fold grinding
of a BEEP ladder if a fold challenge were charged the error of the affine fold (an accounting experiment, the
variant `beepaff-<eta>` of the bench), its recheck in `--check`, and a cache of the searches on disk]
[AI-revised (claude-fable-5-2), 2026-11-14, at the author's request ("experiments for 100 bits of security"):
the target of a ladder is read from its configuration (`target_bits`; 128 if absent), and `lam=100` on the
command line gives the fold grinding of an affine ladder for 100 bits]

    python3 scripts/beep_params.py --check bench_results/three-way-<label>/results.json
    python3 scripts/beep_params.py --print
    python3 scripts/beep_params.py --affine-ladder log_n=24 k0=6 ks=4,4,4 rates=1,3,5,7 [slacks=0.02] [lam=100]
    python3 scripts/beep_params.py --beep-affine-charge log_n=24 k0=6 ks=4,4,4 rates=1,3,5,7 etas=0.02,0.001 [lam=100]

`--check` rechecks, in exact integer and rational arithmetic, every level of every BEEP ladder that a run
of the bench built (the `levels` that flock/crates/flock-core/src/pcs/ligerito/beep.rs prints): the
agreement, the list size against the Johnson bound, the error of the points at the threshold, that the
threshold is the least one, the fold grinding, the queries, the grinding of the coefficients that batch
claims and queries, and the binding samples. `--print` prints the comparison of one fold under each analysis.
`--affine-ladder` prints, for an affine ladder, the least slack per level at which every fold round has a
certificate, with the certificates and the fold grinding (the arguments of the bench).
`--beep-affine-charge` prints, for a BEEP ladder, the fold grinding of every level if its fold squeeze were
charged the error of the affine fold in place of the bad fold challenges of BEEP, i.e. (E_aff + 3 L + 1)/q in
place of (t + 3 L)/q, at the levels where the affine fold has a certificate at the slack of the level and this
needs less grinding (the argument `beepaff=` of the bench). This is an accounting experiment: the fold of
BEEP-Ligerito is not the affine fold, so its bound does not apply to it.
`typst/scripts/make_tables.py` imports this module for the tables of the paper.

Setting. A fold of two words of an interleaved Reed-Solomon code with block length n and rate rho, over a
challenge field of size q = 2^qbits, analyzed at agreement s = ceil((sqrt(rho) + eta) n). With N = n - s + 1
(at least 2), a list bound L at agreement s, m points, an evader of error mu/q per point, and an integer
threshold t >= N + 1:

    points   kappa_1(t) = (q L)^3 (mu/q)^m / (t (t - 1) (t - N))
    fold     kappa_2(t) = (t - 1 + 2 L) / q          (bad fold challenges and the sumcheck round)
    batching kappa_3    = L / q

(Theorem "t:beep_soundness" of the paper for a general threshold; Corollary cor:rbr of Note 2, which is
checked in Lean.) The implementation draws the fold challenge and the batching coefficients in one squeeze,
followed by the points of the next round, and grinds this squeeze for (t + 3 L) / q. At a code switch it
draws the p binding points of the new commitment in one squeeze (two list codewords agree on all of them
with probability at most C(L', 2) (mu/q)^p), and it grinds the coefficients that batch the Q queries of the
level for L' ceil(log2 Q) / q, with the list bound L' of the next level.

The other analyses (bits = -log2 of the error of the fold challenge over the same field):
  UDR      Flock App. C.3 Thm ca-udr = BCHKS25 Cor. 1.4: (gamma n + 1)/q at gamma = delta/2 - 3/(delta n)
  BCHKS    BCHKS25 Thm 4.6 in the line form of Flock's Thm ca-johnson (2025/2055), no row-union factor
  DKT      Dao-Kominers-Thaler (2026/2056) Thm 5.12, as in Note 2 (tab:johnson)
  DEEP-FRI BGKS19 Thm 4.1: max{2 L (k/q + eps)^(1/3), 4/(eps^2 q)}, jointly over the point and the fold
           challenge, with one point and a loss eps in the radius; minimized over eps
  affine   Chiesa-Weissenberg-Yogev-Zheng (version of November 11, 2026): Thm 1.1 (when n eta^2 >= 4/rho),
           and the finite bound of Thm 4.10 for parameters (m, D) found by search, as the paper states it
           and in the form of Flock's script (flock/scripts/affine_fold_params.py), which follows an
           earlier draft (its "Lemma 3.1") and also searches a third parameter B; one coordinate of
           agreement loss

Standard library only; runs on Python 3.9.
"""
import importlib.util
import json
import math
import sys
from fractions import Fraction
from math import ceil, comb, isqrt, log2, sqrt
from pathlib import Path

HERE = Path(__file__).resolve().parent
MAX_SAMPLES = 8
MAX_FOLD_GRINDING = 40


# ------------------------------------------------------------------ exact helpers
def frac(x):
    """A decimal such as 0.02 or 5e-4, read exactly."""
    return x if isinstance(x, Fraction) else Fraction(str(x))


def agreement(n, log_inv_rate, eta):
    """ceil((sqrt(rho) + eta) n) for rho = 2^-log_inv_rate, exactly: the least integer s with
    (s - eta n)^2 >= rho n^2 and s >= eta n."""
    eta = frac(eta)
    s = int((2.0 ** (-log_inv_rate / 2) + float(eta)) * n)
    ok = lambda v: v >= eta * n and (v - eta * n) ** 2 * 2 ** log_inv_rate >= n * n
    while ok(s - 1):
        s -= 1
    while not ok(s):
        s += 1
    return s


def johnson_list_exact(n, k, s):
    """The integer Johnson bound at agreement s for a code of distance n - k + 1 (any alphabet):
    floor(n (n - k + 1) / (s^2 - n (k - 1))), or None at or below the Johnson agreement."""
    den = s * s - n * (k - 1)
    return (n * (n - k + 1)) // den if den > 0 else None


def johnson_list_simple(log_inv_rate, eta):
    """floor(1 / (2 eta sqrt(rho))), exactly: the largest L with (2 eta L)^2 <= 2^log_inv_rate."""
    eta = frac(eta)
    L = int(1 / (2 * float(eta) * 2.0 ** (-log_inv_rate / 2)))
    ok = lambda v: (2 * eta * v) ** 2 <= 2 ** log_inv_rate
    while not ok(L):
        L -= 1
    while ok(L + 1):
        L += 1
    return max(L, 1)


def points_reach(t, N, L, mu, m, lam, qbits):
    """(q L)^3 (mu/q)^m / (t (t - 1) (t - N)) <= 2^-lam, exactly."""
    return L ** 3 * mu ** m * 2 ** (3 * qbits + lam) <= t * (t - 1) * (t - N) * 2 ** (m * qbits)


def points_bits(t, N, L, mu, m, qbits):
    return m * (qbits - log2(mu)) - 3 * (qbits + log2(L)) + log2(t) + log2(t - 1) + log2(t - N)


def least_threshold(N, L, mu, m, lam, qbits):
    lo, hi = N + 1, 2 ** 100
    if not points_reach(hi, N, L, mu, m, lam, qbits):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if points_reach(mid, N, L, mu, m, lam, qbits):
            hi = mid
        else:
            lo = mid + 1
    return lo


def strict_bits(numerator, lam, qbits):
    """The least g >= 0 with numerator / 2^qbits * 2^-g < 2^-lam."""
    g = 0
    while numerator >= 2 ** (qbits - lam + g):
        g += 1
    return g


def select_fold(N, L, mu, lam=128, qbits=128):
    """The rule of beep.rs: per m the least threshold whose points reach lam bits and its fold grinding
    for (t + 3 L)/q; the least grinding, then the fewest points. Returns (m, t, g) or None."""
    best = None
    for m in range(1, MAX_SAMPLES + 1):
        t = least_threshold(N, L, mu, m, lam, qbits)
        if t is None:
            continue
        g = strict_bits(t + 3 * L, lam, qbits)
        if g <= MAX_FOLD_GRINDING and (best is None or g < best[2]):
            best = (m, t, g)
    return best


def queries(log_inv_rate, eta, grinding, lam=128):
    """The least Q with Q log2(1/theta) + grinding > lam (strictly), theta = sqrt(rho) + eta."""
    theta = 2.0 ** (-log_inv_rate / 2) + float(frac(eta))
    return int(max(lam - grinding, 0) / -log2(theta)) + 1


def sqrt_rho_bounds(log_inv_rate, prec=256):
    """Rationals lo <= sqrt(2^-log_inv_rate) <= hi, at most 2^-prec apart."""
    if log_inv_rate % 2 == 0:
        v = Fraction(1, 1 << (log_inv_rate // 2))
        return v, v
    root = isqrt(2 << (2 * prec))  # floor(sqrt(2) 2^prec)
    den = (1 << prec) << ((log_inv_rate + 1) // 2)
    return Fraction(root, den), Fraction(root + 1, den)


def queries_are_least(Q, log_inv_rate, eta, grinding, lam=128):
    """Whether Q is the least number of queries with theta^Q 2^-grinding < 2^-lam for theta = sqrt(rho) + eta,
    decided with rational bounds on theta (True, False, or None if the bounds do not decide)."""
    lo, hi = sqrt_rho_bounds(log_inv_rate)
    eta, need = frac(eta), max(lam - grinding, 0)
    below = lambda count, theta: theta ** count * 2 ** need < 1
    if below(Q, hi + eta) and (Q == 1 or not below(Q - 1, lo + eta)):
        return True
    if not below(Q, lo + eta) or (Q > 1 and below(Q - 1, hi + eta)):
        return False
    return None


LOG_PACKING = 7  # flock-core, pcs::LOG_PACKING: the ring-switched opening has 7 more variables


def binding_reaches(level_index, log_inv_rate, eta, variables, samples, lam=128, qbits=128):
    """Flock's bound for the binding samples of a commitment, exactly: two of the at most 1/(2 eta sqrt(rho))
    codewords of the list agree on every sample with probability at most (L^2 / 2) prod_j (deg_j / q), where
    the samples have degree `variables`, and level 0 has one more of degree variables + 7 (its opening)."""
    degrees = [variables] * samples + ([variables + LOG_PACKING] if level_index == 0 else [])
    prod = 1
    for d in degrees:
        prod *= d
    eta = frac(eta)
    # L^2 / 2 = 2^rate / (8 eta^2)
    return prod * 2 ** log_inv_rate * 2 ** lam <= 8 * eta * eta * 2 ** (qbits * len(degrees))


def beep_level(log_n_block, log_inv_rate, mu, eta, lam=128, qbits=128):
    """One level under BEEP: the shape, the list, and what the rule selects."""
    n = 1 << log_n_block
    k = n >> log_inv_rate
    s = agreement(n, log_inv_rate, eta)
    N = max(n - s + 1, 2)
    L = johnson_list_simple(log_inv_rate, eta)
    sel = select_fold(N, L, mu, lam, qbits)
    out = {"n": n, "k": k, "log_inv_rate": log_inv_rate, "eta": float(frac(eta)), "mu": mu,
           "agreement": s, "line_bound": N, "list_size": L, "list_exact": johnson_list_exact(n, k, s),
           "theta": s / n, "selected": None}
    if sel:
        m, t, g = sel
        out["selected"] = {"samples": m, "threshold": t, "fold_grinding_bits": g,
                           "sample_bits": points_bits(t, N, L, mu, m, qbits),
                           "fold_bits": qbits - log2(t - 1 + 2 * L),
                           "batch_bits": qbits - log2(L),
                           "squeeze_bits": qbits - log2(t + 3 * L)}
    return out


# ------------------------------------------------------------------ the other analyses
def udr(n, log_inv_rate, qbits=128):
    """(agreement fraction, -log2 fold error) of the unique-decoding analysis at its maximal radius."""
    rho = 2.0 ** -log_inv_rate
    delta = 1 - rho
    gamma = delta / 2 - 3 / (delta * n)
    return 1 - gamma, qbits - log2(gamma * n + 1)


def bchks_bits(n, log_inv_rate, eta, qbits=128):
    rho, eta = 2.0 ** -log_inv_rate, float(frac(eta))
    r = max(ceil(sqrt(rho) / (2 * eta)), 3) + 0.5
    gamma = 1 - sqrt(rho) - eta
    return qbits - log2((2 * r ** 5 + 3 * r * gamma * rho) / (3 * rho ** 1.5) * n + r / sqrt(rho))


def dkt_bits(n, log_inv_rate, eta, qbits=128):
    rho, eta = 2.0 ** -log_inv_rate, float(frac(eta))
    k = round(rho * n)
    rho_m = (k - 1) / n
    r = max(ceil(sqrt(rho_m) / (2 * eta)), 3) + 0.5
    return qbits - log2(8 / 3 * n * r ** 3 / rho_m)


def deepfri_bits(k, L, qbits=128):
    """-log2 of min over eps in (0, 1/3) of max{2 L (k/q + eps)^(1/3), 4/(eps^2 q)}, and the eps."""
    f = lambda le: max(1 + log2(L) + log2(k * 2.0 ** -qbits + 2.0 ** le) / 3, 2 - 2 * le - qbits)
    lo, hi = -qbits / 2.0, log2(1 / 3)
    for _ in range(200):  # the first term increases with eps and the second decreases
        a, b = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if f(a) < f(b):
            hi = b
        else:
            lo = a
    le = (lo + hi) / 2
    return -f(le), 2.0 ** le


def affine_theorem_bits(n, log_inv_rate, eta, qbits=128):
    """Thm 1.1 of the affine-combiners paper: 4/(eta q) + 2^14 n^2/(rho^3 eta^10 q^2), if n eta^2 >= 4/rho."""
    rho, eta = 2.0 ** -log_inv_rate, float(frac(eta))
    if n * eta * eta < 4 / rho:
        return None
    a = log2(4 / eta) - qbits
    b = 14 + 2 * log2(n) - 3 * log2(rho) - 10 * log2(eta) - 2 * qbits
    top = max(a, b)
    return -(top + log2(2.0 ** (a - top) + 2.0 ** (b - top)))


_FLOCK = None


def flock_affine():
    """Flock's script, as a module (the vendored copy)."""
    global _FLOCK
    if _FLOCK is None:
        path = HERE.parent / "flock" / "scripts" / "affine_fold_params.py"
        spec = importlib.util.spec_from_file_location("affine_fold_params", path)
        _FLOCK = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(_FLOCK)
    return _FLOCK


def affine_lemma_bits(n, log_msg_cols, log_inv_rate, eta, qbits=128, max_m=40):
    """Flock's script as it ships (multiplicity m <= 40, degree D < 20000), first round of a level:
    (-log2 eps_aff, list) or None. Kept for reference: `affine_search` looks further."""
    s = agreement(n, log_inv_rate, eta)
    d = (1 << log_msg_cols) - 1 + 1
    r = flock_affine().best_bound(n, d, s, qbits, max_m)
    return None if r is None else (-r[0], r[1])


# ------------------------------------------------------------------ the affine fold, with a wider search
# The finite bound of the affine-combiners paper (Chiesa, Weissenberg, Yogev, Zheng; version of November 11,
# 2026) is its Theorem 4.10: for positive integers m, D with M = min{D, floor((m A - D - 1)/d)} >= 1 and
#
#     (4.5)   sum_{j <= M} (m A - D - d j)(D - j + 1)  >  n sum_{s <= min(m - 1, M)} (m - s)(D - s + 1),
#
# and for B = ceil((sqrt(rho) + eta/2) n) - 1 with B^2 > n (d + 1),
#
#     eps_aff <= floor(n (B - d - 1)/(B^2 - n (d + 1))) max{q, C(n, 2)}/q^2 + (D^2 + 4 d^2 M^2 D^3 (n/(A - B))^2)/q^2.
#
# Here d is the degree bound of the folded word (2^c in the first round of a level, one more per round), rho =
# d/n and A = ceil((sqrt(rho) + eta) n). Flock's script (flock/scripts/affine_fold_params.py) follows an earlier
# draft, where the same counts are stated for any B with (B - 1)^2 > n (d + 1): it bounds the bad pairs by
# (4 d^2 M^2 + 1) D^3 (n/(A - B + 1))^2 + L_{d+1}(B - 1) max{q, C(n, 2)} and also searches B. It stops at m = 40
# and D < 20000, which is too early for a small slack: the search below goes further. Every (m, D) that it
# returns is checked against (4.5) with the function of Flock's script, in exact integers.
AFFINE_MULTIPLICITIES = sorted(set(list(range(1, 65)) + [int(64 * 1.06 ** i) for i in range(1, 84)]))  # up to 8055
AFFINE_MAX_DEGREE = 1 << 26


def affine_interpolation(n, d, A, m, D):
    """M if (4.5) holds for (m, D), else None. Closed forms of the two sums, exact."""
    M = min(D, (m * A - D - 1) // d)
    if M < 1:
        return None
    T = m * A - D
    s1, s2 = M * (M + 1) // 2, M * (M + 1) * (2 * M + 1) // 6
    unknowns = T * (D + 1) * (M + 1) - (T + d * (D + 1)) * s1 + d * s2
    K = min(m - 1, M)
    r1, r2 = K * (K + 1) // 2, K * (K + 1) * (2 * K + 1) // 6
    equations = n * (m * (D + 1) * (K + 1) - (m + D + 1) * r1 + r2)
    return M if unknowns > equations else None


def affine_least_degree(n, d, A, m):
    """A degree D >= m at which (4.5) holds and fails at D - 1, found by a scan in steps of 0.2 % and a
    bisection; None if the scan finds none. (4.5) is not monotone in D, so a smaller D may exist: any D
    that is returned is a valid choice."""
    top = min(m * A - d - 1, AFFINE_MAX_DEGREE)
    D, prev = m, m - 1
    while D <= top:
        if affine_interpolation(n, d, A, m, D) is not None:
            lo, hi = prev, D
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if affine_interpolation(n, d, A, m, mid) is not None:
                    hi = mid
                else:
                    lo = mid
            return hi
        prev, D = D, max(D + 1, D + D // 500)
    return None


def log2_fraction(x):
    x = Fraction(x)
    return log2(x.numerator) - log2(x.denominator)


def affine_paper_bound(n, d, A, B, m, D, M, qbits=128):
    """-log2 of the bound of Theorem 4.10 for (m, D, M) and the list floor(n (B - d - 1)/(B^2 - n (d + 1))),
    or None if its conditions on B fail. Exact up to the final logarithm."""
    if not (0 < B < A and B * B > n * (d + 1)):
        return None
    q = 1 << qbits
    ell = (n * (B - d - 1)) // (B * B - n * (d + 1))
    bad = ell * max(q, comb(n, 2)) + D * D + Fraction(4 * d * d * M * M * D ** 3 * n * n, (A - B) ** 2)
    return 2 * qbits - log2_fraction(bad), ell


def affine_paper_B(n, d, A):
    """B = ceil((sqrt(rho) + eta/2) n) - 1 of the paper, for rho = d/n and the slack eta = A/n - sqrt(rho)
    at which the agreement is exactly A: ceil((sqrt(d n) + A)/2) - 1, exactly."""
    v = (isqrt(d * n) + A) // 2
    ok = lambda u: 2 * u >= A and (2 * u - A) ** 2 >= d * n
    while ok(v - 1):
        v -= 1
    while not ok(v):
        v += 1
    return v - 1


def affine_script_bound(n, d, A, m, D, M, qbits=128):
    """-log2 of the bound in the form of Flock's script for (m, D, M), minimized over its grid of B:
    (bits, list, B), or None."""
    fl = flock_affine()
    q = 1 << qbits
    b_min = isqrt(n * (d + 1)) + 2
    if b_min > A:
        return None
    step = max(1, (A - b_min) // 200)
    best = None
    for B in range(A, b_min - 1, -step):
        ell = fl.johnson_list(n, B - 1, d + 1)
        if ell is None:
            break
        bad = Fraction((4 * d * d * M * M + 1) * D ** 3 * n * n, (A - B + 1) ** 2) + ell * max(q, comb(n, 2))
        bits = 2 * qbits - log2_fraction(bad)
        if best is None or bits > best[0]:
            best = (bits, ell, B)
    return best


_AFFINE_CACHE = {}
# The searches are slow (seconds each), so their results are also kept on disk. A cached certificate is never
# trusted: it is used only after `affine_recheck` passes (the interpolation inequality with the function of
# Flock's script, and the bound recomputed from the certificate). A cached "no certificate" is trusted; it can
# only make a ladder more conservative.
AFFINE_CACHE_FILE = HERE.parent / "affine_certificates" / "search_cache.json"
_DISK_CACHE = None


def _disk_key(key):
    n, d, A, qbits, mult = key
    return f"{n},{d},{A},{qbits}," + ("all" if mult is None else "m" + "-".join(str(m) for m in mult))


def _disk_cache():
    global _DISK_CACHE
    if _DISK_CACHE is None:
        try:
            _DISK_CACHE = json.loads(AFFINE_CACHE_FILE.read_text())
        except (OSError, ValueError):
            _DISK_CACHE = {}
    return _DISK_CACHE


def _disk_store(key, value):
    """Merge one entry into the file (other processes may be writing it too) and replace it atomically."""
    import os
    import tempfile
    cache = _disk_cache()
    cache[_disk_key(key)] = value
    try:
        on_disk = json.loads(AFFINE_CACHE_FILE.read_text())
    except (OSError, ValueError):
        on_disk = {}
    on_disk.update(cache)
    cache.update(on_disk)
    AFFINE_CACHE_FILE.parent.mkdir(exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=str(AFFINE_CACHE_FILE.parent), suffix=".tmp")
    with os.fdopen(fd, "w") as f:
        json.dump(on_disk, f, sort_keys=True)
    os.replace(tmp, AFFINE_CACHE_FILE)


def affine_script_bad(n, d, A, cert, qbits=128):
    """The bad pairs (alpha, beta) of the bound in the form of Flock's script for a certificate (m, D, M, B),
    as an exact fraction: eps_aff = bad / q^2."""
    ell = flock_affine().johnson_list(n, cert["B"] - 1, d + 1)
    assert ell is not None and ell == cert["list"], "the list of the certificate"
    q = 1 << qbits
    D, M, B = cert["D"], cert["M"], cert["B"]
    return Fraction((4 * d * d * M * M + 1) * D ** 3 * n * n, (A - B + 1) ** 2) + ell * max(q, comb(n, 2))


def affine_recheck(n, d, A, found, qbits=128):
    """Whether the certificates of a search result hold: (4.5) for (m, D) by Flock's function, and the bits."""
    fl = flock_affine()
    for form in ("script", "paper"):
        cert = found.get(form)
        if cert is None:
            continue
        if fl.lemma31_feasible(n, d, A, cert["m"], cert["D"]) != cert["M"]:
            return False
        if form == "script":
            bits = 2 * qbits - log2_fraction(affine_script_bad(n, d, A, cert, qbits))
        else:
            again = affine_paper_bound(n, d, A, cert["B"], cert["m"], cert["D"], cert["M"], qbits)
            if again is None or again[1] != cert["list"]:
                return False
            bits = again[0]
        if abs(bits - cert["bits"]) > 1e-9:
            return False
    return True


def affine_search(n, d, A, qbits=128, multiplicities=None):
    """The best bounds that the search finds for one fold (degree bound d, agreement A, block length n):
    {"paper": {...} or None, "script": {...} or None}, each with its bits and its certificate."""
    key = (n, d, A, qbits, tuple(multiplicities) if multiplicities else None)
    if key in _AFFINE_CACHE:
        return _AFFINE_CACHE[key]
    cached = _disk_cache().get(_disk_key(key))
    if cached is not None and affine_recheck(n, d, A, cached, qbits):
        _AFFINE_CACHE[key] = cached
        return cached
    fl = flock_affine()
    B_paper = affine_paper_B(n, d, A)
    out = {"paper": None, "script": None}
    for m in (multiplicities or AFFINE_MULTIPLICITIES):
        D = affine_least_degree(n, d, A, m)
        if D is None:
            continue
        M = affine_interpolation(n, d, A, m, D)
        assert fl.lemma31_feasible(n, d, A, m, D) == M, "the certificate fails the check of Flock's script"
        paper = affine_paper_bound(n, d, A, B_paper, m, D, M, qbits)
        if paper and (out["paper"] is None or paper[0] > out["paper"]["bits"]):
            out["paper"] = {"bits": paper[0], "list": paper[1], "m": m, "D": D, "M": M, "B": B_paper}
        script = affine_script_bound(n, d, A, m, D, M, qbits)
        if script and (out["script"] is None or script[0] > out["script"]["bits"]):
            out["script"] = {"bits": script[0], "list": script[1], "m": m, "D": D, "M": M, "B": script[2]}
    _AFFINE_CACHE[key] = out
    _disk_store(key, out)
    return out


def affine_round_grinding(bits, lam=128, qbits=128, candidates=1):
    """The grinding of a fold round of the affine ladder, by the rule of Flock's script: the round has error
    eps_aff + 2/q (the transport of the claim, for the one codeword that the out-of-domain samples leave), and
    the grinding is ceil(lam + log2 of that). With `candidates` codewords the transport costs 2/q for each
    (a level with no out-of-domain sample on its commitment: see `affine_no_first_sample`)."""
    round_bits = -log2(2.0 ** -bits + candidates * 2.0 ** (1 - qbits))
    return round_bits, max(0, ceil(lam - round_bits - 1e-9))


def affine_no_first_sample(level0, lam=128, qbits=128):
    """The fold grinding of the first level of an affine ladder with NO out-of-domain sample on the first
    commitment (the variants `anf*` of the bench; our change to Flock's protocol, at the author's request, to
    match BEEP-Ligerito, which has none).

    Flock's ladders draw one out-of-domain point on the first commitment. Its value binds the prover to one of
    the at most L codewords within the agreement of the level, and the note of the affine fold then charges
    every fold round eps_aff + 2/q: the bound of the fold, plus the transport of the claim of that one codeword
    (a wrong grid is a nonzero polynomial of degree 2 in the challenges). Without the sample the L codewords
    stay candidates during the fold rounds of the first level, and a claim that is false for all of them must be
    transported for each: eps_aff + 2 L/q per round, by a union bound, as in the analyses that carry the list
    through the sumcheck (WHIR, and t:beep_soundness of the BEEP paper, whose kappa_2 has the same 2 L). The
    next commitments keep their samples, so the later levels do not change. This is our accounting, not
    Flock's, and nobody has reviewed it.

    L is the larger of floor(1/(2 eta sqrt(rho))), which the rest of the accounting uses, and the exact Johnson
    bound for the code of the last round (dimension 2^c + k) at the agreement of the level.
    `level0`: the first level of `affine_ladder`. Returns {list, grinding, rounds}."""
    n, c, k = 1 << level0["log_n_block"], level0["log_msg_cols"], level0["folds"]
    simple = johnson_list_simple(level0["log_inv_rate"], level0["eta"])
    exact = johnson_list_exact(n, (1 << c) + k, level0["agreement"])
    if exact is None:
        raise SystemExit("the agreement of the first level is not above the Johnson agreement of its last round")
    L = max(simple, exact)
    rounds = [affine_round_grinding(r["bits"], lam, qbits, candidates=L) for r in level0["rounds"]]
    return {"list": L, "list_simple": simple, "list_exact": exact, "grinding": max(g for _, g in rounds),
            "round_bits": [b for b, _ in rounds]}


def affine_level(log_n_block, log_inv_rate, log_msg_cols, folds, eta, lam=128, qbits=128):
    """Every fold round of a level of the affine ladder at slack eta, in the form of Flock's script (round j
    folds into degree 2^c - 1 + j, at the agreement of the nominal rate): the certificates, and the grinding
    of the level, which is the largest of its rounds; None if some round has no certificate."""
    n = 1 << log_n_block
    A = agreement(n, log_inv_rate, eta)
    rounds = []
    for j in range(1, folds + 1):
        r = affine_search(n, (1 << log_msg_cols) - 1 + j, A, qbits)["script"]
        if r is None:
            return None
        round_bits, grind = affine_round_grinding(r["bits"], lam, qbits)
        rounds.append(dict(r, round=j, round_bits=round_bits, grinding=grind))
    return {"agreement": A, "rounds": rounds, "grinding": max(r["grinding"] for r in rounds)}


AFFINE_SLACKS = ["0.001", "0.0015", "0.002", "0.003", "0.005", "0.01", "0.02"]


def affine_ladder(log_n, initial_k, recursive_ks, rates, slacks=AFFINE_SLACKS, lam=128, qbits=128):
    """An affine ladder with, at each level, the smallest slack of `slacks` at which the search certifies
    every fold round of the level. Returns one dict per level: its shape, slack, grinding and rounds.
    Levels: (k_0, c_0) = (initial_k, log_n - initial_k), then c_i = c_{i-1} - k_i."""
    ks = [initial_k] + list(recursive_ks)
    out, c = [], log_n
    for li, (k, rate) in enumerate(zip(ks, rates)):
        c -= k
        ln = c + rate
        found = None
        for eta in sorted(slacks, key=frac):
            # the first round decides whether the slack is worth the search of the other rounds
            n, A = 1 << ln, agreement(1 << ln, rate, eta)
            first = affine_search(n, 1 << c, A, qbits)["script"]
            if first is None:
                continue
            near = [m for m in AFFINE_MULTIPLICITIES if first["m"] * 0.7 <= m <= first["m"] * 1.4]
            rounds = []
            for j in range(1, k + 1):
                r = first if j == 1 else affine_search(n, (1 << c) - 1 + j, A, qbits, near)["script"]
                if r is None:  # the multiplicities near the one of the first round fail: try all of them
                    r = affine_search(n, (1 << c) - 1 + j, A, qbits)["script"]
                if r is None:
                    rounds = None
                    break
                round_bits, grind = affine_round_grinding(r["bits"], lam, qbits)
                rounds.append(dict(r, round=j, round_bits=round_bits, grinding=grind))
            if rounds:
                found = {"level": li, "folds": k, "log_msg_cols": c, "log_inv_rate": rate, "log_n_block": ln,
                         "eta": eta, "agreement": A, "rounds": rounds,
                         "grinding": max(r["grinding"] for r in rounds)}
                break
        if found is None:
            raise SystemExit(f"level {li}: no slack of {slacks} has a certificate for every round")
        out.append(found)
    return out


def print_affine_ladder(levels, lam=128):
    print("level round   rho  log n  degree  slack  agreement     m        D      M  list        B  "
          "log2 eps_aff  log2 eps_round  grinding")
    for lv in levels:
        for r in lv["rounds"]:
            print(f"{lv['level']:5d} {r['round']:5d}  2^-{lv['log_inv_rate']} {lv['log_n_block']:5d} "
                  f"{(1 << lv['log_msg_cols']) - 1 + r['round']:7d} {lv['eta']:>6} {lv['agreement']:10d} "
                  f"{r['m']:5d} {r['D']:8d} {r['M']:6d} {r['list']:5d} {r['B']:8d}  {-r['bits']:12.2f}  "
                  f"{-r['round_bits']:14.2f}  {r['grinding']:8d}")
    print("affine_eta=" + ",".join(lv["eta"] for lv in levels)
          + " affine_fold=" + ",".join(str(lv["grinding"]) for lv in levels))
    # The same ladder with no out-of-domain sample on the first commitment (`affine_no_first_sample`): the
    # fold rounds of the first level carry its list.
    nf = affine_no_first_sample(levels[0], lam=lam)
    print(f"# no sample on the first commitment: the fold rounds of level 0 are charged eps_aff + 2 L/q with "
          f"L = {nf['list']} (floor(1/(2 eta sqrt(rho))) = {nf['list_simple']}, exact Johnson bound of the last "
          f"round {nf['list_exact']}): log2 eps_round = "
          + ", ".join(f"{-b:.2f}" for b in nf["round_bits"]) + f", grinding {nf['grinding']}")
    print("affine_fold_nf=" + ",".join(str(g) for g in [nf["grinding"]] + [lv["grinding"] for lv in levels[1:]]))


# ------------------------------------------------------------------ BEEP with the charge of the affine fold
# An accounting experiment (the variant `beepaff-<eta>` of the bench), at the author's request: "if we use the
# affine folding error (+2L) for BEEP-Ligerito instead of delta n + 1 (+2L), what results do we get?". In the
# proof of t:beep_soundness the fold challenge is bad if it is DEEP-MCA-bad (at most t - 1 challenges) or if it
# hits a root of one of at most L sumcheck differences (2 L). Here the first count is replaced by the bad pairs
# of the affine fold over q, E_aff = eps_aff q: the squeeze of beep.rs, which also carries the batching (L) and
# the points of the next round (1), is charged (E_aff + 3 L + 1)/q in place of (t + 3 L)/q. This is done at the
# levels where every fold round has a certificate of the affine bound at the slack of the level and where it
# needs less grinding. NOT a sound configuration of BEEP-Ligerito: the bound is that of the fold
# f_0 + (alpha + beta x) f_1 with two challenges, and BEEP-Ligerito folds f_0 + r (f_0 + f_1). With the affine
# fold the samples would not be needed at all (the bound is an MCA bound), and the protocol would be the affine
# ladder.
def beep_affine_charge_level(log_n_block, log_inv_rate, log_msg_cols, folds, eta, lam=128, qbits=128):
    """One BEEP level: its own fold grinding, and the grinding under the charge of the affine fold."""
    n, c, k = 1 << log_n_block, log_msg_cols, folds
    lv = beep_level(log_n_block, log_inv_rate, k + c - 1, eta, lam, qbits)
    L, A = lv["list_size"], lv["agreement"]
    own = lv["selected"]["fold_grinding_bits"]
    out = {"log_n_block": log_n_block, "log_inv_rate": log_inv_rate, "log_msg_cols": c, "folds": k,
           "eta": str(eta), "agreement": A, "list_size": L, "beep_fold_grinding": own,
           "beep_threshold": lv["selected"]["threshold"], "rounds": None, "affine_fold_grinding": None,
           "kappa2_bits": None, "squeeze_bits": None, "charge": "beep", "fold_grinding": own}
    first = affine_search(n, 1 << c, A, qbits)["script"]
    if first is None:
        return out
    near = [m for m in AFFINE_MULTIPLICITIES if first["m"] * 0.7 <= m <= first["m"] * 1.4]
    rounds = []
    for j in range(1, k + 1):
        d = (1 << c) - 1 + j
        r = first if j == 1 else affine_search(n, d, A, qbits, near)["script"]
        if r is None:
            r = affine_search(n, d, A, qbits)["script"]
        if r is None:
            return out
        rounds.append(dict(r, round=j, degree=d))
    q = 1 << qbits
    # E_aff of the worst round, exactly, and the two charges in units of 1/q
    e_aff = max(affine_script_bad(n, r["degree"], A, r, qbits) for r in rounds) / q
    squeeze = e_aff + 3 * L + 1
    g = 0
    while not squeeze < 2 ** (qbits - lam + g):
        g += 1
    out.update(rounds=rounds, affine_fold_grinding=g, e_aff_log2=log2_fraction(e_aff),
               kappa2_bits=qbits - log2_fraction(e_aff + 2 * L), squeeze_bits=qbits - log2_fraction(squeeze))
    if g < own:
        out.update(charge="affine", fold_grinding=g)
    return out


def beep_affine_charge(log_n, initial_k, recursive_ks, rates, eta, lam=128, qbits=128):
    """Every level of a BEEP ladder at slack eta (the shapes of `affine_ladder`)."""
    out, c = [], log_n
    for li, (k, rate) in enumerate(zip([initial_k] + list(recursive_ks), rates)):
        c -= k
        out.append(dict(beep_affine_charge_level(c + rate, rate, c, k, eta, lam, qbits), level=li))
    return out


def print_beep_affine_charge(etas, ladders):
    print("  slack level   rho  log n     L  BEEP: log2 t  grinding | affine: log2 E_aff  kappa_2 bits  "
          "squeeze bits  grinding | charge  fold grinding")
    for eta, levels in zip(etas, ladders):
        for lv in levels:
            aff = ("                 -             -             -         -" if lv["rounds"] is None else
                   f"{lv['e_aff_log2']:18.2f}  {lv['kappa2_bits']:12.2f}  {lv['squeeze_bits']:12.2f}  "
                   f"{lv['affine_fold_grinding']:8d}")
            print(f"{eta:>7} {lv['level']:5d}  2^-{lv['log_inv_rate']} {lv['log_n_block']:5d} {lv['list_size']:5d}  "
                  f"{log2(lv['beep_threshold']):12.2f}  {lv['beep_fold_grinding']:8d} | {aff} | "
                  f"{lv['charge']:>6}  {lv['fold_grinding']:13d}")
            for r in lv["rounds"] or []:
                print(f"#   certificate, level {lv['level']} round {r['round']}: degree {r['degree']}, m = {r['m']}, "
                      f"D = {r['D']}, M = {r['M']}, B = {r['B']}, list {r['list']}, log2 eps_aff = {-r['bits']:.2f}")
    print("beepaff=" + "/".join(f"{eta}:" + ",".join(str(lv["fold_grinding"]) for lv in levels)
                               for eta, levels in zip(etas, ladders)))


# ------------------------------------------------------------------ the exact recheck of a run
def check_level(lv, lam=128, qbits=128, level_index=None, next_level=None, last=None):
    """Exact recheck of one `BeepLevel` printed by the bench. Returns a list of failures. With `level_index`
    (and `next_level`, or `last=True` at the last level) it also rechecks the binding samples of the level's
    commitment and the grinding of the coefficients that batch its queries."""
    bad = []
    rate, c, k_folds = lv["log_inv_rate"], lv["log_msg_cols"], lv["folds"]
    n = 1 << (c + rate)
    dim = 1 << c
    eta = frac(repr(lv["eta"]))
    s = agreement(n, rate, eta)
    if lv["agreement"] != s:
        bad.append(f"agreement {lv['agreement']}, exact {s}")
    s = lv["agreement"]
    N, L, m, t = lv["line_bound"], lv["list_size"], lv["samples"], lv["threshold"]
    if N != max(n - s + 1, 2):
        bad.append(f"line bound {N}")
    exact = johnson_list_exact(n, dim, s)
    if exact is None or L < exact:
        bad.append(f"list size {L} below the Johnson bound {exact}")
    if L != johnson_list_simple(rate, eta):
        bad.append(f"list size {L}, floor(1/(2 eta sqrt(rho))) = {johnson_list_simple(rate, eta)}")
    mu = lv["max_variables"]
    if mu != k_folds + c - 1:
        bad.append(f"variables {mu}")
    if not (t >= N + 1 and points_reach(t, N, L, mu, m, lam, qbits)):
        bad.append("the points do not reach the target at the threshold")
    if t > N + 1 and points_reach(t - 1, N, L, mu, m, lam, qbits):
        # the Rust selection has a float margin of 1e-9 bits: report how far above the least it is
        least = least_threshold(N, L, mu, m, lam, qbits)
        if t - least > max(1, t >> 30):
            bad.append(f"threshold {t} is not the least one ({least})")
    g = lv["fold_grinding_bits"]
    if not (t + 3 * L < 2 ** (qbits - lam + g)):
        bad.append(f"fold grinding {g} does not cover (t + 3L)/q")
    if g > 0 and t + 3 * L < 2 ** (qbits - lam + g - 1):
        bad.append(f"fold grinding {g} is not the least")
    sel = select_fold(N, L, mu, lam, qbits)
    if sel is None or (sel[0], sel[2]) != (m, g) or abs(sel[1] - t) > max(1, t >> 30):
        bad.append(f"the rule selects {sel}, the bench has (m, t, g) = ({m}, {t}, {g})")
    # queries: the least Q with Q log2(1/theta) + grinding > lam, strictly, with theta = sqrt(rho) + eta
    Q, qg = lv["queries"], lv["query_grinding_bits"]
    least = queries_are_least(Q, rate, eta, qg, lam)
    if least is not True:
        bad.append(f"queries {Q}: " + ("not the least count that reaches the target" if least is False
                                         else "undecided at this precision"))
    # claim batching: (L_real + 1)/q, strictly below 2^-lam after grinding; L_real < L + 1
    cg = lv["claim_batch_grinding_bits"]
    if not (L + 2 <= 2 ** (qbits - lam + cg)):
        bad.append(f"claim-batching grinding {cg} does not cover (L + 1)/q")
    if level_index is not None:
        if level_index == 0 and lv["ood_samples"] == 0:
            # no binding sample on the first commitment (BeepConfig::without_first_binding): the m points
            # of the first fold round bind it. Two codewords of the list differ on one half of the table,
            # so they give the same answers with probability at most C(L, 2) (mu/q)^m, exactly:
            if not (L * (L - 1) // 2) * mu ** m * 2 ** lam <= 2 ** (qbits * m):
                bad.append(f"the {m} points of the first fold round do not bind the first commitment")
        # the binding samples of the level's commitment, drawn together: Flock's bound, exactly
        elif not binding_reaches(level_index, rate, eta, k_folds + c, lv["ood_samples"], lam, qbits):
            bad.append(f"the {lv['ood_samples']} binding samples do not reach the target")
        # the coefficients that batch the queries: L' ceil(log2 Q) / q with the list of the next level
        g = lv["consistency_batch_grinding_bits"]
        if next_level is not None:
            num = next_level["list_size"] * max((Q - 1).bit_length(), 1)
            if not num < 2 ** (qbits - lam + g):
                bad.append(f"consistency grinding {g} does not cover L' ceil(log2 Q) = {num}")
            if g > 0 and num < 2 ** (qbits - lam + g - 1):
                bad.append(f"consistency grinding {g} is not the least")
        elif last and g != 0:
            bad.append(f"consistency grinding {g} at the last level, which batches nothing")
    return bad


def check_grinds(cfg, lam=128, qbits=128):
    """Exact recheck of how a BEEP ladder grinds (`grinds` of its configuration, printed by the bench since
    the run 20261113e): the numerators of its ground squeezes, and every search against them. A search with
    `bits` needs numerator < 2^(qbits - lam + bits); a search with a 64-bit `target` passes with probability
    target/2^64, so it needs numerator * target < 2^(64 + qbits - lam), and the bench must have taken the
    largest such target. A ladder whose squeezes are ground against thresholds has no proof of work at all
    on a squeeze with numerator < 2^(qbits - lam) (at lam = 100 over a field of 2^128 elements: 2^28), and a
    threshold on every other one. Returns a list of failures."""
    bad = []
    levels, grinds = cfg["levels"], cfg.get("grinds")
    if grinds is None:
        return bad
    shift = 64 + qbits - lam
    for li, lv in enumerate(levels):
        t, L = lv["threshold"], lv["list_size"]
        nxt = levels[li + 1] if li + 1 < len(levels) else None
        want = {"fold": t + 3 * L, "claim": L + 2,
                "consistency": (nxt["list_size"] * max((lv["queries"] - 1).bit_length(), 1)) if nxt else 0}
        for kind, numerator in want.items():
            if lv[kind + "_numerator"] != numerator:
                bad.append(f"level {li}: {kind} numerator {lv[kind + '_numerator']}, exact {numerator}")
            g = grinds[kind][li]
            if kind == "consistency" and nxt is None:
                if g.get("bits") != 0:
                    bad.append(f"level {li}: the last level batches no queries, and grinds {g}")
                continue
            if g.get("target") is not None:
                T = g["target"]
                if not numerator * T < 2 ** shift:
                    bad.append(f"level {li}: {kind} target {T} does not cover the numerator {numerator}")
                if numerator * (T + 1) < 2 ** shift:
                    bad.append(f"level {li}: {kind} target {T} is not the largest one")
                if numerator < 2 ** (qbits - lam):
                    bad.append(f"level {li}: a {kind} search for the numerator {numerator}, which needs none")
            elif kind != "fold" or cfg["fold_grinding_bits"][li] == g["bits"]:
                # bits: they must cover the numerator (the fold bits of the accounting variant `beepaff`
                # are not those of the ladder and are rechecked apart)
                if not numerator < 2 ** (qbits - lam + g["bits"]) and kind != "fold":
                    bad.append(f"level {li}: {g['bits']} {kind} bits do not cover the numerator {numerator}")
    return bad


def target_of(row):
    """The round-by-round target of the ladder of a row, in bits: `target_bits` of its configuration (printed
    by the bench since the runs at 100 bits), else 128."""
    t = row["config"].get("target_bits", 128)
    if t != int(t):
        raise SystemExit(f"{row['cell']} {row['variant']}: a target of {t} bits")
    return int(t)


def check_results(path):
    data = json.loads(Path(path).read_text())
    seen, failures = set(), 0
    for row in data["rows"]:
        # the BEEP ladder of the comparison, and the same ladder with the binding sample of the first
        # commitment (`beepb`, `beepold`); `beepref` has the configuration of `beep`
        if not row["variant"].startswith(("beep-", "beepb-", "beepold-", "beepbits-")):
            continue
        levels = row["config"]["levels"]
        for li, lv in enumerate(levels):
            nxt = levels[li + 1] if li + 1 < len(levels) else None
            key = json.dumps([li, lv, nxt and nxt["list_size"], row["config"].get("grinds") if li == 0 else None],
                             sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            lam = target_of(row)
            bad = check_level(lv, lam=lam, level_index=li, next_level=nxt, last=nxt is None)
            if li == 0:
                bad += check_grinds(row["config"], lam=lam)
            tag = f"{row['cell']} {row['variant']} level {li}"
            if bad:
                failures += 1
                print(f"FAIL {tag}: " + "; ".join(bad))
            else:
                print(f"ok   {tag}: n = 2^{lv['log_msg_cols'] + lv['log_inv_rate']}, eta = {lv['eta']}, "
                      f"s = {lv['agreement']}, N = {lv['line_bound']}, L = {lv['list_size']}, "
                      f"m = {lv['samples']}, t = N + {lv['threshold'] - lv['line_bound']}, "
                      f"fold grinding {lv['fold_grinding_bits']}" + ("" if lam == 128 else f", {lam} bits"))
    print(f"{len(seen)} distinct levels checked, {failures} failures")
    # The accounting variant `beepaff-<eta>`: its fold grinding per level is the one that
    # `beep_affine_charge_level` gives for the level, recomputed here (certificates rechecked).
    hybrid, seen_h = 0, set()
    for row in data["rows"]:
        if not row["variant"].startswith("beepaff-"):
            continue
        cfg = row["config"]
        beep = next((r for r in data["rows"] if r["cell"] == row["cell"]
                     and r["variant"] == "beep-" + row["variant"][len("beepaff-"):]), None)
        for li, lv in enumerate(cfg["levels"]):
            got = cfg["fold_grinding_bits"][li]
            key = json.dumps([lv["log_msg_cols"], lv["log_inv_rate"], lv["folds"], lv["eta"], got])
            if key in seen_h:
                continue
            seen_h.add(key)
            want = beep_affine_charge_level(lv["log_msg_cols"] + lv["log_inv_rate"], lv["log_inv_rate"],
                                            lv["log_msg_cols"], lv["folds"], frac(repr(lv["eta"])),
                                            lam=target_of(row))
            bad = []
            if want["beep_fold_grinding"] != lv["fold_grinding_bits"]:
                bad.append(f"BEEP's own fold grinding {lv['fold_grinding_bits']}, recomputed {want['beep_fold_grinding']}")
            if want["fold_grinding"] != got:
                bad.append(f"fold grinding {got}, recomputed {want['fold_grinding']} ({want['charge']})")
            if beep is not None and beep["config"]["samples"] != cfg["samples"]:
                bad.append("the samples differ from those of the BEEP ladder")
            tag = f"{row['cell']} {row['variant']} level {li}"
            if bad:
                hybrid += 1
                print(f"FAIL {tag}: " + "; ".join(bad))
            else:
                print(f"ok   {tag}: fold grinding {got} ({want['charge']} charge; BEEP's own "
                      f"{want['beep_fold_grinding']})")
    if seen_h:
        print(f"{len(seen_h)} distinct levels of the affine-charge variant checked, {hybrid} failures")
    return failures + hybrid + check_affine_rows(data)


AFFINE_FAMILY = ("affine", "afast", "anf", "anfref")


def check_affine_rows(data):
    """Recheck the fold grinding of every affine ladder of a run (the variants `affine`, `afast`, `anf`,
    `anfref` and their `-small` twins): at each level, the grinding of the certificates of its fold rounds at
    the slack of the level (`affine_level`: eps_aff + 2/q); at the first level of a ladder with no
    out-of-domain sample on the first commitment, the grinding with the list (`affine_no_first_sample`:
    eps_aff + 2 L/q). Also: `anf` and `anfref` have no sample on the first commitment and the others have
    one, and the ladders with the prover of affine_fast.rs have the configuration and the proof size of the
    same ladder with Flock's prover. Returns the number of failures."""
    seen, failures = set(), 0
    rows = {(r["cell"], r["variant"]): r for r in data["rows"]}
    for (cell, variant), row in rows.items():
        family = variant[:-len("-small")] if variant.endswith("-small") else variant
        if family not in AFFINE_FAMILY:
            continue
        cfg = row["config"]
        bad = []
        no_first = family in ("anf", "anfref")
        if (cfg["ood_samples"][0] == 0) != no_first:
            bad.append(f"{cfg['ood_samples'][0]} samples on the first commitment")
        twin = rows.get((cell, {"afast": "affine", "anf": "anfref"}.get(family, family) + variant[len(family):]))
        if twin is not None and twin is not row:
            if twin["config"] != cfg:
                bad.append("another configuration than the same ladder with Flock's prover")
            if twin["proof_bytes"] != row["proof_bytes"]:
                bad.append("another proof size than the same ladder with Flock's prover")
        ks = [cfg["initial_k"]] + list(cfg["recursive_ks"])
        c = row["log_n"]
        lam = target_of(row)
        for li, (k, rate, eta) in enumerate(zip(ks, cfg["log_inv_rates"], cfg["etas"])):
            c -= k
            key = (c, rate, k, repr(float(eta)), cfg["fold_grinding_bits"][li], no_first and li == 0, lam)
            if key in seen:
                continue
            seen.add(key)
            lv = affine_level(c + rate, rate, c, k, repr(float(eta)), lam=lam)
            if lv is None:
                bad.append(f"level {li}: no certificate at slack {eta}")
                continue
            want = lv["grinding"]
            if no_first and li == 0:
                lv.update(folds=k, log_msg_cols=c, log_inv_rate=rate, log_n_block=c + rate, eta=repr(float(eta)))
                want = affine_no_first_sample(lv, lam=lam)["grinding"]
            if cfg["fold_grinding_bits"][li] != want:
                bad.append(f"level {li}: fold grinding {cfg['fold_grinding_bits'][li]}, recomputed {want}")
        if bad:
            failures += 1
            print(f"FAIL {cell} {variant}: " + "; ".join(bad))
    print(f"{len(seen)} distinct levels of the affine ladders checked, {failures} failures")
    return failures


# ------------------------------------------------------------------ the comparison of one fold
# (label, log2 n, log inverse rate, log2 of the row length, variables of the largest message of the level)
SHAPES = [
    ("level 0 of 2^20 words, rate 1/2", 15, 1, 14, 19),
    ("level 0 of 2^24 words, rate 1/2", 19, 1, 18, 23),
    ("level 0 of 2^22 words, rate 1/4", 19, 2, 17, 21),
    ("level 1 of 2^24 words, rate 1/8", 17, 3, 14, 17),
    ("level 2 of 2^24 words, rate 1/32", 15, 5, 10, 13),
    ("level 3 of 2^24 words, rate 1/128", 13, 7, 6, 9),
]
ETAS = ["0.02", "0.005", "0.001"]


def comparison(shapes=SHAPES, etas=ETAS, qbits=128, lam=128, with_lemma=True):
    """One row per shape and slack: the fold under each analysis."""
    rows = []
    for label, ln, rate, c, mu in shapes:
        n = 1 << ln
        theta_u, udr_fold = udr(n, rate, qbits)
        for eta in etas:
            lv = beep_level(ln, rate, mu, eta, lam, qbits)
            N, L = lv["line_bound"], lv["list_size"]
            fixed = {}
            for m in (3, 4, 5):
                fixed[m] = points_bits(N + 1, N, L, mu, m, qbits)
            # The first round of a level folds into degree 2^c, at the agreement of the level.
            shipped = affine_lemma_bits(n, c, rate, eta, qbits) if with_lemma else None
            found = affine_search(n, 1 << c, lv["agreement"], qbits) if with_lemma else {"paper": None, "script": None}
            script, paper = found["script"], found["paper"]
            affine_round = affine_grind = None
            if script:
                # Flock's rule: the round has error eps_aff + 2/q (the transport of the claim), and its
                # grinding is ceil(lam + log2 of that), as in affine_fold_params.py
                affine_round, affine_grind = affine_round_grinding(script["bits"], lam, qbits)
            rows.append({
                "label": label, "log_n": ln, "log_inv_rate": rate, "eta": eta, "mu": mu,
                "theta": lv["theta"], "list_size": L, "line_bound": N,
                "queries": queries(rate, eta, 16, lam),
                "udr_theta": theta_u, "udr_fold_bits": udr_fold,
                "udr_queries": int(max(lam - 16, 0) / -log2(theta_u)) + 1,
                "bchks_bits": bchks_bits(n, rate, eta, qbits),
                "dkt_bits": dkt_bits(n, rate, eta, qbits),
                "deepfri_bits": deepfri_bits(lv["k"], L, qbits)[0],
                "affine_theorem_bits": affine_theorem_bits(n, rate, eta, qbits),
                "affine_shipped_bits": shipped[0] if shipped else None,
                "affine_script_bits": script["bits"] if script else None,
                "affine_script_certificate": script,
                "affine_paper_bits": paper["bits"] if paper else None,
                "affine_paper_certificate": paper,
                "affine_round_bits": affine_round,
                "affine_grinding_bits": affine_grind,
                "affine_list": script["list"] if script else None,
                "beep_points_bits_at_least_threshold": fixed,
                "beep_fold_bits_at_least_threshold": qbits - log2(N + 2 * L),
                "beep": lv["selected"],
            })
    return rows


def main():
    args = sys.argv[1:]
    if args[:1] == ["--check"] and len(args) == 2:
        sys.exit(1 if check_results(args[1]) else 0)
    if args[:1] == ["--affine-ladder"]:
        # e.g. --affine-ladder log_n=24 k0=6 ks=4,4,4 rates=1,3,5,7 [slacks=0.02]
        kv = dict(a.split("=", 1) for a in args[1:])
        ints = lambda key: [int(x) for x in kv[key].split(",")]
        slacks = kv["slacks"].split(",") if "slacks" in kv else AFFINE_SLACKS
        lam = int(kv.get("lam", 128))
        print(f"# affine ladder, {' '.join(args[1:])}: per level the smallest slack of {slacks} with a certificate")
        print("# for every fold round, in the form of Flock's script (flock/scripts/affine_fold_params.py) with the")
        print("# wider search of scripts/beep_params.py; every (m, D) passes lemma31_feasible of Flock's script")
        if lam != 128:
            print(f"# the grinding is for a round-by-round target of {lam} bits (lam={lam}), over a field of 2^128 elements")
        print_affine_ladder(affine_ladder(int(kv["log_n"]), int(kv["k0"]), ints("ks"), ints("rates"), slacks, lam=lam),
                            lam=lam)
        return
    if args[:1] == ["--beep-affine-charge"]:
        # e.g. --beep-affine-charge log_n=24 k0=6 ks=4,4,4 rates=1,3,5,7 etas=0.02,0.001
        kv = dict(a.split("=", 1) for a in args[1:])
        ints = lambda key: [int(x) for x in kv[key].split(",")]
        etas = kv["etas"].split(",")
        print(f"# BEEP ladder with the charge of the affine fold, {' '.join(args[1:])}: an accounting experiment,")
        print("# not a sound configuration (see scripts/beep_params.py). Per level: the fold grinding of BEEP, for")
        print("# (t + 3 L)/q; the grinding if the squeeze is charged (E_aff + 3 L + 1)/q, where E_aff = eps_aff q is")
        print("# the bound of the affine fold in the form of Flock's script, at the worst round of the level (\"-\" if")
        print("# some round has no certificate at this slack); and the smaller of the two. kappa_2 bits is")
        print("# -log2((E_aff + 2 L)/q), the second round of the paper's construction alone.")
        lam = int(kv.get("lam", 128))
        if lam != 128:
            print(f"# for a round-by-round target of {lam} bits (lam={lam})")
        ladders = [beep_affine_charge(int(kv["log_n"]), int(kv["k0"]), ints("ks"), ints("rates"), eta, lam=lam)
                   for eta in etas]
        print_beep_affine_charge(etas, ladders)
        return
    if args == ["--print"]:
        fmt = lambda v, w=6: (f"{v:{w}.1f}" if v is not None else " " * (w - 1) + "-")
        print("shape, eta | theta   L      N | UDR fold  BCHKS    DKT  DEEP-FRI  affine: Thm 1.1, Thm 4.10, script form |"
              " BEEP: points at t = N+1 for m = 3, 4, 5; fold at t = N+1 | selected m, t - N, points, fold, grinding")
        for r in comparison():
            b = r["beep"]
            p = r["beep_points_bits_at_least_threshold"]
            print(f"{r['label']:34} {r['eta']:>6} | {r['theta']:.4f} {r['list_size']:5d} {r['line_bound']:7d} |"
                  f" {fmt(r['udr_fold_bits'])} {fmt(r['bchks_bits'])} {fmt(r['dkt_bits'])} {fmt(r['deepfri_bits'])}"
                  f"   {fmt(r['affine_theorem_bits'])} {fmt(r['affine_paper_bits'])} {fmt(r['affine_script_bits'])} |"
                  f" {fmt(p[3])} {fmt(p[4])} {fmt(p[5])}; {fmt(r['beep_fold_bits_at_least_threshold'])} |"
                  f" {b['samples']} {b['threshold'] - r['line_bound']:6d} {fmt(b['sample_bits'])}"
                  f" {fmt(b['fold_bits'])} {b['fold_grinding_bits']:3d}")
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
