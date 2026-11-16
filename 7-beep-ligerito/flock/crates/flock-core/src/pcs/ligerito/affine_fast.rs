// [AI-drafted (claude-fable-5-2), 2026-11-14, at the author's request ("try to bring the affine version to a
// similar level of optimization as BEEP"): a prover for Flock's affine ladder on a dense L0 that makes one pass
// over the table per fold round. Not part of upstream Flock, whose prover is `affine::prove_affine`. This one
// writes the same proof, byte for byte (`tests::fast_matches_flock`), so Flock's verifier checks it unchanged.
// Research, unaudited. Please review]
// [AI-revised (claude-fable-5-2), 2026-11-14: the last table and the last weight of a proof no longer go back to
// the buffer pool (the pool grew by two buffers per proof, up to 48 of the size of the message)]

//! One pass per fold round for the affine ladder of [`super::affine`].
//!
//! The protocol, the transcript and the proof are those of
//! [`super::affine::prove_affine`] on a dense L0, and the verifier is
//! [`super::affine::verify_affine`]. Only the work of the fold rounds
//! differs. A round of the affine fold on a table `f` with rows `(f_0, f_1)`
//! per row pair and a weight `W` sends the grid `G[u][b] = <u, W_b>` for
//! `u ∈ {f_0, f_1, T f_1}` (`T` is multiplication by `X` in the novel basis),
//! and then folds `f' = f_0 + α f_1 + β T f_1`, `W' = W_0 + r (W_0 + W_1)`.
//! Flock's dense prover makes three passes per round (`T f_1`, the grid, the
//! fold), with one reduced multiplication per product and two new tables per
//! round. Here:
//!
//! * **One pass per round.** The pass that folds the table and the weight at
//!   the challenges of a round also computes the grid of the next round,
//!   block by block on the folded table while the block is in cache
//!   ([`fold_pass`]). The first round of a level has a pass of its own, which
//!   only reads ([`first_grid`]).
//! * **`T` on the fly.** `(T g)_c` is `g_{c-1} + g_c` at an odd column `c`
//!   and `P_z (g_{c-1} + g_{c + 2^z - 1})` at an even one, with `z` the
//!   trailing zeros of `c`. Inside a block of `2^b` columns that starts at a
//!   multiple of `2^b`, every such index is in the block, except at the first
//!   column of the block, which needs two columns from outside. So `T f_1`
//!   is never stored: the fold reads its two operands, and the grid sums
//!   `g_{c-1} + g_{c + 2^z - 1}` against the weight per value of `z` and
//!   multiplies the sums by `P_z` at the end of the pass.
//! * **The claim gives `G[f_1][1]`.** The grid has six entries, five go on
//!   the wire and the claim fixes the sixth, so the pass computes five.
//! * **Deferred reduction.** The sums of the grid are accumulated as
//!   unreduced carry-less products, and an entry of the folded table is one
//!   reduction of two products. With PMULL the inner loops keep their
//!   accumulators in vector registers ([`kernels`]).
//! * **No new tables.** The outputs of a pass come from Flock's buffer pool
//!   and its inputs go back to it. The pool keeps up to 48 buffers, so a
//!   prover must not give it more than it takes: the message and the basis
//!   of a proof are given in the first round, the last table goes into the
//!   proof and the last weight is dropped, as in [`super::beep`]. (A first
//!   version gave these two back as well, and the pool grew to 48 buffers of
//!   the size of the message, 12 GiB at `2^24` words.)
//!
//! Every value that reaches the transcript is the same field element as in
//! Flock's prover, so the proofs are identical. `tests::fast_matches_flock`
//! checks this on small ladders, with and without out-of-domain samples.

use std::time::{Duration, Instant};

use rayon::prelude::{
    IndexedParallelIterator, ParallelIterator, ParallelSlice, ParallelSliceMut,
};

use crate::{
    merkle::cap_layer,
    pcs::ligerito::{
        AdditiveNttF128, Challenger, F128, F256Unreduced, Hash, LigeroWitness, ProverConfig,
        RecursiveProof, VerifierConfig,
        affine::{
            AffineProof, Commitment, EqFactors, LABEL, Level, batched_consistency, carry_products,
            fold_claim, level_shapes, view,
        },
        beep::ProveTimings,
        ceil_log2, eval_sk_at_vks, fold_pairs, grind_and_sample_queries,
        induce_sumcheck_poly_auto, ligero_commit, merkle_paths_for,
    },
    scratch::{give_f128, take_f128},
};

/// An affine ladder with no out-of-domain sample on the first commitment.
///
/// Flock's ladders draw one out-of-domain point on the first commitment
/// (`ood_samples[0] = 1`): the prover answers the multilinear extension of
/// the committed message at the point, and this claim is batched with the
/// opening claim. The answer is consistent with at most one of the codewords
/// within the agreement of the level (up to the binding error), and the note
/// of the affine fold then charges each fold round the bound of the fold plus
/// `2 / |F|`, the transport of the claim of that one codeword.
///
/// Without the sample (`ood_samples[0] = 0`) the at most `L` codewords of the
/// list stay candidates during the fold rounds of the first level, and each
/// round must be charged `2 L / |F|` in place of `2 / |F|` (a union bound
/// over the candidates, as in the analyses that carry the list through the
/// sumcheck). `level0_fold_grinding` must be the fold grinding of the first
/// level under that charge
/// (`7-beep-ligerito/scripts/beep_params.py --affine-ladder` prints it as
/// `affine_fold_nf=`). The later commitments keep their samples, so the
/// other levels do not change. Flock's prover and verifier run on this
/// configuration unchanged: they loop over `ood_samples[0]`.
///
/// This is not Flock's protocol nor its accounting: it is the change that
/// BEEP-Ligerito makes (`BeepConfig::without_first_binding`), applied to the
/// affine ladder so that the two are compared like for like.
pub fn without_first_sample(
    ladder: &(ProverConfig, VerifierConfig),
    level0_fold_grinding: usize,
) -> (ProverConfig, VerifierConfig) {
    let (mut prover, mut verifier) = ladder.clone();
    prover.ood_samples[0] = 0;
    verifier.ood_samples[0] = 0;
    prover.fold_grinding_bits[0] = level0_fold_grinding;
    verifier.fold_grinding_bits[0] = level0_fold_grinding;
    (prover, verifier)
}

/// Entries of the table per block of a pass: `2^12` (64 KiB of the table and
/// as much of the weight), so that a block that the fold has just written is
/// still in the first cache levels when the grid of the next round reads it.
const BLOCK_LOG: usize = 12;

/// Columns per block of a pass over a table with `rows` rows whose weight has
/// `live` columns: a power of two that divides `live`.
fn block_columns(rows: usize, live: usize) -> usize {
    ((1usize << BLOCK_LOG) / rows).max(1).min(live)
}

/// Column `col` of a table with `rows` rows, stored `f[row + rows * col]`.
#[inline(always)]
fn column(f: &[F128], rows: usize, col: usize) -> &[F128] {
    &f[rows * col..rows * (col + 1)]
}

/// `(T g)_col` for a row `g` of `width` coefficients, as `P_z` times a sum
/// of at most two coefficients: `Some((z, col - 1, second))`, with `second`
/// the column of the second coefficient if it is in range, or `None` at
/// `col = 0`, where `(T g)_0 = 0`. This is `affine::t_at`: `P_0 = 1`, and at
/// an odd column the second coefficient is `g_col`.
#[inline(always)]
fn shift_operands(col: usize, width: usize) -> Option<(usize, usize, Option<usize>)> {
    if col == 0 {
        return None;
    }
    let z = col.trailing_zeros() as usize;
    let second = col + (1usize << z) - 1;
    Some((z, col - 1, (second < width).then_some(second)))
}

/// Column `col <= width` of `f_0 + α f_1 + β T f_1`, for a table `f` with
/// `rows` rows and `width` columns: `out[m]` for the row pair `m`.
///
/// At an odd column this is `f_0 + (α + β) f_1[col] + β f_1[col - 1]`, and at
/// an even one `f_0 + α f_1[col] + β P_z (f_1[col - 1] + f_1[col + 2^z - 1])`:
/// two multiplications per entry. At `col = width` there is no `f_0` and no
/// `f_1[col]`.
///
/// `beta_p[z] = β P_z` (so `beta_p[0] = β`), computed once per pass.
fn fold_column_of(
    f: &[F128],
    rows: usize,
    width: usize,
    col: usize,
    alpha: F128,
    beta_p: &[F128],
    out: &mut [F128],
) {
    debug_assert!(col <= width && out.len() == rows / 2);
    let (a, b, ca, cb) = match shift_operands(col, width) {
        None => (None, None, alpha, F128::ZERO),
        Some((0, prev, _)) => (Some(column(f, rows, prev)), None, alpha + beta_p[0], beta_p[0]),
        Some((z, prev, second)) => (
            Some(column(f, rows, prev)),
            second.map(|c| column(f, rows, c)),
            alpha,
            beta_p[z],
        ),
    };
    if col < width {
        kernels::fold_column(column(f, rows, col), a, b, ca, cb, out);
    } else {
        // The overflow column: `β (T f_1)[width]`. `width >= 1`, so `a` is
        // there, and the second coefficient is out of range.
        let a = a.expect("the overflow column is not the first");
        for (m, dst) in out.iter_mut().enumerate() {
            let s = b.map_or(a[2 * m + 1], |b| a[2 * m + 1] + b[2 * m + 1]);
            *dst = cb * s;
        }
    }
}

/// The accumulators of the grid of a table, for one thread: the three sums
/// `<f_0, W_0>`, `<f_0, W_1>`, `<f_1, W_0>` and, per value `z` of the
/// trailing zeros of the column, the two sums of `(T f_1) / P_z` against
/// `W_0` and `W_1`. All unreduced.
struct GridAcc {
    g: [F256Unreduced; 3],
    u: Vec<[F256Unreduced; 2]>,
    /// Columns from outside the block, for its first column.
    left: Vec<F128>,
    far: Vec<F128>,
}

impl GridAcc {
    fn new(rows: usize) -> Self {
        Self {
            g: [F256Unreduced::ZERO; 3],
            u: vec![[F256Unreduced::ZERO; 2]; usize::BITS as usize],
            left: vec![F128::ZERO; rows],
            far: vec![F128::ZERO; rows],
        }
    }

    /// Add the columns `col0..col0 + n` of a table with `rows` rows and
    /// `width` columns, given as the block `fb` (and `wb` of the weight).
    /// `col0` is a multiple of `n`, a power of two, so `T` only leaves the
    /// block at its first column; `outside(col, out)` writes a column of the
    /// table that is not in the block.
    fn add_block(
        &mut self,
        fb: &[F128],
        wb: &[F128],
        rows: usize,
        col0: usize,
        width: usize,
        outside: impl Fn(usize, &mut [F128]),
    ) {
        let n = fb.len() / rows;
        debug_assert!(fb.len() == rows * n && wb.len() == fb.len() && col0.is_multiple_of(n));
        let inside = |c: usize| c >= col0 && c < col0 + n;
        if let Some((_, prev, second)) = shift_operands(col0, width) {
            outside(prev, &mut self.left);
            if let Some(c) = second.filter(|&c| !inside(c)) {
                outside(c, &mut self.far);
            }
        }
        for i in 0..n {
            let fc = column(fb, rows, i);
            let wc = column(wb, rows, i);
            let g = match shift_operands(col0 + i, width) {
                None => kernels::grid_column(fc, wc, None, None).0,
                Some((z, prev, second)) => {
                    let a = if inside(prev) { column(fb, rows, prev - col0) } else { &self.left[..] };
                    let b = second
                        .map(|c| if inside(c) { column(fb, rows, c - col0) } else { &self.far[..] });
                    let (g, u) = kernels::grid_column(fc, wc, Some(a), b);
                    self.u[z][0] ^= u[0];
                    self.u[z][1] ^= u[1];
                    g
                }
            };
            for (x, y) in self.g.iter_mut().zip(g) {
                *x ^= y;
            }
        }
    }

    fn merge(mut self, other: Self) -> Self {
        for (x, y) in self.g.iter_mut().zip(other.g) {
            *x ^= y;
        }
        for (x, y) in self.u.iter_mut().zip(other.u) {
            x[0] ^= y[0];
            x[1] ^= y[1];
        }
        self
    }

    /// `[G00, G01, G10, G20, G21]`: the entries of the grid that go on the
    /// wire (`G11` follows from the claim).
    fn finish(&self, p: &[F128]) -> [F128; 5] {
        let (mut g20, mut g21) = (F128::ZERO, F128::ZERO);
        for (z, u) in self.u.iter().enumerate() {
            if *u != [F256Unreduced::ZERO; 2] {
                g20 += p[z] * u[0].reduce();
                g21 += p[z] * u[1].reduce();
            }
        }
        [self.g[0].reduce(), self.g[1].reduce(), self.g[2].reduce(), g20, g21]
    }
}

/// Whether `DC ZVA` may be used from user space and zeroes 64 bytes
/// (`DCZID_EL0`: the prohibition bit clear, and a block of 2^4 words).
#[cfg(target_arch = "aarch64")]
fn zva_64() -> bool {
    use std::sync::OnceLock;
    static OK: OnceLock<bool> = OnceLock::new();
    *OK.get_or_init(|| {
        if std::env::var_os("FLOCK_NO_ZVA").is_some() {
            return false;
        }
        let id: u64;
        // SAFETY: reading DCZID_EL0 is allowed at EL0 and has no side effect.
        unsafe {
            core::arch::asm!("mrs {id}, dczid_el0", id = out(reg) id, options(nomem, nostack, preserves_flags));
        }
        id & 0x1f == 4
    })
}

/// Tell the cache that the block `dst` is about to be written in full: zero
/// every 64-byte line that lies inside it with `DC ZVA`, which allocates
/// the line without reading it from memory. The pass then overwrites every
/// entry, so the zeros are never read. Without this each line of an output
/// is first read from memory (a read for ownership), which is a third of
/// the memory traffic of a fold pass. A no-op where `DC ZVA` is not
/// available.
#[inline(always)]
pub(super) fn will_overwrite(dst: &mut [F128]) {
    #[cfg(target_arch = "aarch64")]
    if zva_64() {
        let start = dst.as_mut_ptr() as usize;
        let end = start + size_of_val(dst);
        let mut line = (start + 63) & !63;
        while line + 64 <= end {
            // SAFETY: the 64 bytes at `line` are inside `dst`, which this
            // function borrows mutably, and DC ZVA zeroes exactly them.
            unsafe {
                core::arch::asm!("dc zva, {line}", line = in(reg) line, options(nostack, preserves_flags));
            }
            line += 64;
        }
    }
    #[cfg(not(target_arch = "aarch64"))]
    let _ = dst;
}

/// The grid of `(f, w)`, a table with `rows` rows and `width` columns whose
/// weight has `w.len() / rows` columns, in one pass that only reads.
fn first_grid(f: &[F128], w: &[F128], rows: usize, width: usize, p: &[F128]) -> [F128; 5] {
    let live = w.len() / rows;
    assert!(f.len() == rows * width && w.len() == rows * live && live <= width && rows >= 2);
    let n = block_columns(rows, live);
    let block = rows * n;
    f[..rows * live]
        .par_chunks(block)
        .zip(w.par_chunks(block))
        .enumerate()
        .fold(
            || GridAcc::new(rows),
            |mut acc, (bi, (fb, wb))| {
                acc.add_block(fb, wb, rows, bi * n, width, |col, out| {
                    out.copy_from_slice(column(f, rows, col));
                });
                acc
            },
        )
        .reduce(|| GridAcc::new(rows), GridAcc::merge)
        .finish(p)
}

/// Fold `(f, w)`, a table with `rows` rows and `width` columns, at the
/// challenges `(α, β, r)` of a round and, if a round follows (`look`),
/// compute its grid from the folded table, block by block in the same pass.
/// Returns the folded table (`rows / 2` rows, `width + 1` columns), the
/// folded weight and that grid.
fn fold_pass(
    f: &[F128],
    w: &[F128],
    rows: usize,
    width: usize,
    (alpha, beta, r): (F128, F128, F128),
    p: &[F128],
    look: bool,
) -> (Vec<F128>, Vec<F128>, Option<[F128; 5]>) {
    let h = rows / 2;
    let live = w.len() / rows;
    assert!(f.len() == rows * width && w.len() == rows * live && live <= width && rows >= 2);
    assert!(!look || h >= 2, "a round follows only if two rows are left");
    // `β P_z` for the trailing zeros `z` of a column of the folded table.
    let beta_p: Vec<F128> = (0..=width.ilog2() as usize + 1).map(|z| beta * p[z]).collect();
    let beta_p = &beta_p[..];
    // The outputs come from the buffer pool; every entry is written below.
    let mut dst_f = take_f128(h * (width + 1));
    let mut dst_w = take_f128(h * live);
    let n = block_columns(h, live);
    let block = h * n;
    let (head, tail) = dst_f.split_at_mut(h * live);
    let acc = head
        .par_chunks_mut(block)
        .zip(dst_w.par_chunks_mut(block))
        .enumerate()
        .fold(
            || GridAcc::new(h),
            |mut acc, (bi, (fb, wb))| {
                let col0 = bi * n;
                will_overwrite(fb);
                will_overwrite(wb);
                for (i, fo) in fb.chunks_exact_mut(h).enumerate() {
                    fold_column_of(f, rows, width, col0 + i, alpha, beta_p, fo);
                }
                fold_pairs(w, h * col0, wb, r);
                if look {
                    acc.add_block(fb, wb, h, col0, width + 1, |col, out| {
                        fold_column_of(f, rows, width, col, alpha, beta_p, out);
                    });
                }
                acc
            },
        )
        .reduce(|| GridAcc::new(h), GridAcc::merge);
    // The columns past the weight (the overflow of the level so far).
    for (i, fo) in tail.chunks_exact_mut(h).enumerate() {
        fold_column_of(f, rows, width, live + i, alpha, beta_p, fo);
    }
    let grid = look.then(|| acc.finish(p));
    (dst_f, dst_w, grid)
}

/// The inner loops of the passes, over one column of a table (`rows` entries,
/// the row pairs `(2m, 2m + 1)`). With PMULL they use three carry-less
/// products per multiplication and keep their sums in vector registers; the
/// portable versions define them.
mod kernels {
    use super::{F128, F256Unreduced};

    /// For a column `fc` of the table and `wc` of the weight, and the columns
    /// `a` and `b` whose odd rows add up to `(T f_1) / P_z` at this column:
    /// `([Σ f_0 w_0, Σ f_0 w_1, Σ f_1 w_0], [Σ s w_0, Σ s w_1])` over the row
    /// pairs, with `s = a_1 + b_1`. Without `a` the second part is zero.
    pub(super) fn grid_column(
        fc: &[F128],
        wc: &[F128],
        a: Option<&[F128]>,
        b: Option<&[F128]>,
    ) -> ([F256Unreduced; 3], [F256Unreduced; 2]) {
        assert!(fc.len().is_multiple_of(2) && wc.len() == fc.len());
        assert!(a.is_none_or(|a| a.len() == fc.len()) && b.is_none_or(|b| b.len() == fc.len()));
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        if let Some(a) = a {
            // SAFETY: the cfg gate guarantees PMULL; the lengths are checked above.
            return unsafe { neon::grid_column(fc, wc, a, b) };
        }
        grid_column_portable(fc, wc, a, b)
    }

    pub(super) fn grid_column_portable(
        fc: &[F128],
        wc: &[F128],
        a: Option<&[F128]>,
        b: Option<&[F128]>,
    ) -> ([F256Unreduced; 3], [F256Unreduced; 2]) {
        let mut g = [F256Unreduced::ZERO; 3];
        let mut u = [F256Unreduced::ZERO; 2];
        for m in 0..fc.len() / 2 {
            let (f0, f1) = (fc[2 * m], fc[2 * m + 1]);
            let (w0, w1) = (wc[2 * m], wc[2 * m + 1]);
            g[0] ^= f0.mul_unreduced(w0);
            g[1] ^= f0.mul_unreduced(w1);
            g[2] ^= f1.mul_unreduced(w0);
            if let Some(a) = a {
                let s = b.map_or(a[2 * m + 1], |b| a[2 * m + 1] + b[2 * m + 1]);
                u[0] ^= s.mul_unreduced(w0);
                u[1] ^= s.mul_unreduced(w1);
            }
        }
        (g, u)
    }

    /// `out[m] = f_0 + ca · f_1 + cb · (a_1 + b_1)` over the row pairs of the
    /// column `fc`, with `a_1`, `b_1` the odd rows of the columns `a`, `b`.
    pub(super) fn fold_column(
        fc: &[F128],
        a: Option<&[F128]>,
        b: Option<&[F128]>,
        ca: F128,
        cb: F128,
        out: &mut [F128],
    ) {
        assert!(fc.len() == 2 * out.len());
        assert!(a.is_none_or(|a| a.len() == fc.len()) && b.is_none_or(|b| b.len() == fc.len()));
        #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
        if let Some(a) = a {
            // SAFETY: the cfg gate guarantees PMULL; the lengths are checked above.
            unsafe { neon::fold_column(fc, a, b, ca, cb, out) };
            return;
        }
        fold_column_portable(fc, a, b, ca, cb, out);
    }

    pub(super) fn fold_column_portable(
        fc: &[F128],
        a: Option<&[F128]>,
        b: Option<&[F128]>,
        ca: F128,
        cb: F128,
        out: &mut [F128],
    ) {
        for (m, dst) in out.iter_mut().enumerate() {
            let mut acc = fc[2 * m + 1].mul_unreduced(ca);
            if let Some(a) = a {
                let s = b.map_or(a[2 * m + 1], |b| a[2 * m + 1] + b[2 * m + 1]);
                acc ^= s.mul_unreduced(cb);
            }
            *dst = fc[2 * m] + acc.reduce();
        }
    }

    #[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
    mod neon {
        use core::arch::aarch64::{
            uint64x2_t, vdupq_n_u64, veorq_u64, vextq_u64, vgetq_lane_u64, vld1q_u64,
            vmull_high_p64, vmull_p64, vreinterpretq_p64_u64, vreinterpretq_u64_p128, vst1q_u64,
        };

        use super::{F128, F256Unreduced};

        #[inline(always)]
        unsafe fn load(x: *const F128) -> uint64x2_t {
            // SAFETY: `F128` is `repr(C)` with two `u64` fields, `lo` first;
            // the caller gives a valid pointer.
            unsafe { vld1q_u64(x.cast::<u64>()) }
        }

        /// The xor of the two lanes, in the low lane (the Karatsuba operand).
        #[inline(always)]
        unsafe fn kar(x: uint64x2_t) -> uint64x2_t {
            // SAFETY: plain vector arithmetic.
            unsafe { veorq_u64(x, vextq_u64::<1>(x, x)) }
        }

        /// `lo · lo'`, `hi · hi'` and `(lo ^ hi)(lo' ^ hi')` of two elements.
        #[inline(always)]
        unsafe fn products(
            a: uint64x2_t,
            ak: uint64x2_t,
            b: uint64x2_t,
            bk: uint64x2_t,
        ) -> [uint64x2_t; 3] {
            // SAFETY: PMULL is available (the callers carry the feature).
            unsafe {
                [
                    vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b))),
                    vreinterpretq_u64_p128(vmull_high_p64(
                        vreinterpretq_p64_u64(a),
                        vreinterpretq_p64_u64(b),
                    )),
                    vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(ak), vgetq_lane_u64::<0>(bk))),
                ]
            }
        }

        #[inline(always)]
        unsafe fn add(acc: &mut [uint64x2_t; 3], x: [uint64x2_t; 3]) {
            // SAFETY: plain vector arithmetic.
            unsafe {
                acc[0] = veorq_u64(acc[0], x[0]);
                acc[1] = veorq_u64(acc[1], x[1]);
                acc[2] = veorq_u64(acc[2], x[2]);
            }
        }

        /// The 256-bit product from the three Karatsuba sums.
        #[inline(always)]
        unsafe fn combine(x: [uint64x2_t; 3]) -> F256Unreduced {
            // SAFETY: plain vector arithmetic.
            unsafe {
                let mid = veorq_u64(x[2], veorq_u64(x[0], x[1]));
                F256Unreduced {
                    r0: vgetq_lane_u64::<0>(x[0]),
                    r1: vgetq_lane_u64::<1>(x[0]) ^ vgetq_lane_u64::<0>(mid),
                    r2: vgetq_lane_u64::<0>(x[1]) ^ vgetq_lane_u64::<1>(mid),
                    r3: vgetq_lane_u64::<1>(x[1]),
                }
            }
        }

        /// The three Karatsuba sums reduced modulo `x^128 + x^7 + x^2 + x + 1`,
        /// in a register: the two folds of `flock_field`'s `mul_q`.
        #[inline(always)]
        unsafe fn reduce(x: [uint64x2_t; 3]) -> uint64x2_t {
            // SAFETY: PMULL is available (the callers carry the feature).
            unsafe {
                let zero = vdupq_n_u64(0);
                let cross = veorq_u64(x[2], veorq_u64(x[0], x[1]));
                let fold = |t: uint64x2_t| {
                    veorq_u64(
                        vextq_u64::<1>(zero, t),
                        vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<1>(t), 0x87)),
                    )
                };
                let t1 = veorq_u64(cross, fold(x[1]));
                veorq_u64(x[0], fold(t1))
            }
        }

        #[target_feature(enable = "aes")]
        pub(super) unsafe fn grid_column(
            fc: &[F128],
            wc: &[F128],
            a: &[F128],
            b: Option<&[F128]>,
        ) -> ([F256Unreduced; 3], [F256Unreduced; 2]) {
            let pairs = fc.len() / 2;
            assert!(wc.len() == fc.len() && a.len() == fc.len());
            assert!(b.is_none_or(|b| b.len() == fc.len()));
            // SAFETY: PMULL is enabled; every index below is in range by the
            // assertions above.
            unsafe {
                let zero = vdupq_n_u64(0);
                let mut acc = [[zero; 3]; 5];
                let (fp, wp, ap) = (fc.as_ptr(), wc.as_ptr(), a.as_ptr());
                let bp = b.map(<[F128]>::as_ptr);
                for m in 0..pairs {
                    let f0 = load(fp.add(2 * m));
                    let f1 = load(fp.add(2 * m + 1));
                    let w0 = load(wp.add(2 * m));
                    let w1 = load(wp.add(2 * m + 1));
                    let mut s = load(ap.add(2 * m + 1));
                    if let Some(bp) = bp {
                        s = veorq_u64(s, load(bp.add(2 * m + 1)));
                    }
                    let (f0k, f1k, sk) = (kar(f0), kar(f1), kar(s));
                    let (w0k, w1k) = (kar(w0), kar(w1));
                    add(&mut acc[0], products(f0, f0k, w0, w0k));
                    add(&mut acc[1], products(f0, f0k, w1, w1k));
                    add(&mut acc[2], products(f1, f1k, w0, w0k));
                    add(&mut acc[3], products(s, sk, w0, w0k));
                    add(&mut acc[4], products(s, sk, w1, w1k));
                }
                (
                    [combine(acc[0]), combine(acc[1]), combine(acc[2])],
                    [combine(acc[3]), combine(acc[4])],
                )
            }
        }

        #[target_feature(enable = "aes")]
        pub(super) unsafe fn fold_column(
            fc: &[F128],
            a: &[F128],
            b: Option<&[F128]>,
            ca: F128,
            cb: F128,
            out: &mut [F128],
        ) {
            let h = out.len();
            assert!(fc.len() == 2 * h && a.len() == 2 * h);
            assert!(b.is_none_or(|b| b.len() == 2 * h));
            // SAFETY: PMULL is enabled; every index below is in range by the
            // assertions above.
            unsafe {
                let cav = load(&raw const ca);
                let cbv = load(&raw const cb);
                let (cak, cbk) = (kar(cav), kar(cbv));
                let (fp, ap, op) = (fc.as_ptr(), a.as_ptr(), out.as_mut_ptr());
                let bp = b.map(<[F128]>::as_ptr);
                for m in 0..h {
                    let f0 = load(fp.add(2 * m));
                    let f1 = load(fp.add(2 * m + 1));
                    let mut s = load(ap.add(2 * m + 1));
                    if let Some(bp) = bp {
                        s = veorq_u64(s, load(bp.add(2 * m + 1)));
                    }
                    let mut acc = products(f1, kar(f1), cav, cak);
                    add(&mut acc, products(s, kar(s), cbv, cbk));
                    vst1q_u64(op.add(m).cast::<u64>(), veorq_u64(f0, reduce(acc)));
                }
            }
        }
    }
}

// Indices of the timers of [`prove_affine_fast_timed`].
const T_FOLDS: usize = 0;
const T_FOLD_POW: usize = 1;
const T_OTHER_POW: usize = 2;
const T_OOD: usize = 3;
const T_COMMITS: usize = 4;
const T_OPENS: usize = 5;
const T_INDUCE: usize = 6;

/// The fold rounds of one level, with one pass over the table per round.
/// Returns the `(α, β)` of every round.
fn rounds_fast<Ch: Challenger>(
    level: &mut Level,
    k: usize,
    fold_bits: u32,
    p: &[F128],
    proof: &mut AffineProof,
    challenger: &mut Ch,
    t: &mut [Duration; 7],
) -> Vec<(F128, F128)> {
    let mut gammas = Vec::with_capacity(k);
    let ti = Instant::now();
    let mut grid = first_grid(&level.f, &level.w, level.rows, level.width, p);
    t[T_FOLDS] += ti.elapsed();
    for j in 0..k {
        // `G11 = v − G00`: the claim is `<f_0, W_0> + <f_1, W_1>`.
        let g = [grid[0], grid[1], grid[2], level.claim + grid[0], grid[3], grid[4]];
        let sent = [g[0], g[1], g[2], g[4], g[5]];
        challenger.observe_f128_slice(&sent);
        proof.grids.push(sent);
        let ti = Instant::now();
        let (nonce, ch) = challenger.grind_pow_and_sample_f128_vec(fold_bits, 3);
        proof.fold_grinding_nonces.push(nonce);
        t[T_FOLD_POW] += ti.elapsed();
        let (alpha, beta, rr) = (ch[0], ch[1], ch[2]);

        let ti = Instant::now();
        let (f, w, next) = fold_pass(
            &level.f,
            &level.w,
            level.rows,
            level.width,
            (alpha, beta, rr),
            p,
            j + 1 < k,
        );
        give_f128(std::mem::replace(&mut level.f, f));
        give_f128(std::mem::replace(&mut level.w, w));
        level.rows /= 2;
        level.width += 1;
        level.claim = fold_claim(&g, alpha, beta, rr);
        if let Some(next) = next {
            grid = next;
        }
        t[T_FOLDS] += ti.elapsed();
        gammas.push((alpha, beta));
    }
    gammas
}

/// [`super::affine::prove_affine`] with one pass per fold round: the same
/// arguments, and the same proof.
pub fn prove_affine_fast<Ch: Challenger>(
    config: &ProverConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
) -> AffineProof {
    prove_affine_fast_timed(config, witness, basis, target, l0_codeword, l0_tree, challenger).0
}

/// [`prove_affine_fast`], also returning where the time went (the phases of
/// [`ProveTimings`]; the affine fold has no answers).
pub fn prove_affine_fast_timed<Ch: Challenger>(
    config: &ProverConfig,
    witness: Vec<F128>,
    basis: Vec<F128>,
    target: F128,
    l0_codeword: &[F128],
    l0_tree: &[Hash],
    challenger: &mut Ch,
) -> (AffineProof, ProveTimings) {
    let t_total = Instant::now();
    let mut t = [Duration::ZERO; 7];
    let log_n = witness.len().trailing_zeros() as usize;
    let r = config.recursive_steps;
    let shapes = level_shapes(log_n, config.initial_k, &config.recursive_ks);
    assert_eq!(
        config.recursive_log_msg_cols,
        shapes[1..].iter().map(|s| s.1).collect::<Vec<_>>()
    );
    config
        .validate_stratified()
        .expect("stratified schedules invalid (affine prover)");
    let strat = |level: usize| &config.stratified[level];
    let claim_bits = |level: usize| config.claim_batch_grinding_bits[level] as u32;
    let consistency_bits = |level: usize| config.consistency_batch_grinding_bits[level] as u32;

    challenger.observe_label(LABEL);
    challenger.observe_f128(target);
    let block_len_0 = 1usize << (shapes[0].1 + config.log_inv_rates[0]);
    let lanes_0 = 1usize << shapes[0].0;
    assert_eq!(l0_codeword.len(), block_len_0 * lanes_0);
    let initial_cap = cap_layer(l0_tree, block_len_0, strat(0).cap_depth()).to_vec();
    challenger.observe_bytes(initial_cap.as_flattened());

    let p = carry_products(log_n + 1);
    let mut proof = AffineProof {
        initial_cap,
        recursive_caps: Vec::new(),
        openings: Vec::new(),
        grids: Vec::new(),
        overflows: Vec::new(),
        yr: Vec::new(),
        ood_values: Vec::new(),
        fold_grinding_nonces: Vec::new(),
        claim_batch_grinding_nonces: Vec::new(),
        consistency_batch_grinding_nonces: Vec::new(),
        grinding_nonces: Vec::new(),
    };

    let ti = Instant::now();
    let mut level = Level::new(witness, basis, shapes[0].0, target);
    for _ in 0..config.ood_samples[0] {
        let z = challenger.sample_f128_vec(log_n);
        let eq_z = EqFactors::new(&z);
        let y = level.dot_eq(&eq_z);
        challenger.observe_f128(y);
        proof.ood_values.push(y);
        let (nonce, beta) = challenger.grind_pow_and_sample_f128(claim_bits(0));
        proof.claim_batch_grinding_nonces.push(nonce);
        level.add_eq_weight(&eq_z, beta, y);
    }
    t[T_OOD] += ti.elapsed();

    let mut committed: Vec<LigeroWitness> = Vec::with_capacity(r);
    for li in 0..=r {
        let (k, c) = shapes[li];
        assert_eq!(level.rows, 1usize << k);
        assert_eq!(level.width, 1usize << c);
        let gammas = rounds_fast(
            &mut level,
            k,
            config.fold_grinding_bits[li] as u32,
            &p,
            &mut proof,
            challenger,
            &mut t,
        );
        let prev = if li == 0 {
            Commitment {
                mat: l0_codeword,
                tree: l0_tree,
                block_len: block_len_0,
                lanes: lanes_0,
            }
        } else {
            view(&committed[li - 1])
        };

        if li == r {
            // The last table goes into the proof and the last weight is dropped at the end, as in
            // `beep::prove_beep`: a proof takes two buffers that are not from the pool (the message and the
            // basis) and gives them to it in its first round, so it must also take two out.
            proof.yr = std::mem::take(&mut level.f);
            challenger.observe_f128_slice(&proof.yr);
            let ti = Instant::now();
            let (nonce, queries) = grind_and_sample_queries(
                challenger,
                config.grinding_bits[li] as u32,
                prev.block_len,
                config.queries[li],
                strat(li),
            );
            proof.grinding_nonces.push(nonce);
            t[T_OTHER_POW] += ti.elapsed();
            let ti = Instant::now();
            proof.openings.push(RecursiveProof {
                opened_rows: queries.iter().map(|&q| prev.row(q).to_vec()).collect(),
                merkle_proof: merkle_paths_for(prev.tree, prev.block_len, &queries, strat(li)),
            });
            t[T_OPENS] += ti.elapsed();
            break;
        }

        // Code switch: commit the low 2^c coefficients, send the overflow.
        let mut f = std::mem::take(&mut level.f);
        let overflow = f.split_off(1usize << c);
        challenger.observe_f128_slice(&overflow);
        let (k_next, c_next) = shapes[li + 1];
        let rate = config.log_inv_rates[li + 1];
        let ti = Instant::now();
        let ntt = AdditiveNttF128::standard(c_next + rate);
        let next = ligero_commit(&f, c_next, k_next, rate, &ntt, config.merkle_hash);
        t[T_COMMITS] += ti.elapsed();
        let cap = next.cap(strat(li + 1).cap_depth()).to_vec();
        challenger.observe_bytes(cap.as_flattened());
        proof.recursive_caps.push(cap);
        let w = std::mem::take(&mut level.w);
        level = Level::new(f, w, k_next, level.claim);

        let ti = Instant::now();
        for _ in 0..config.ood_samples[li + 1] {
            let z = challenger.sample_f128_vec(c);
            let eq_z = EqFactors::new(&z);
            let y = level.dot_eq(&eq_z);
            challenger.observe_f128(y);
            proof.ood_values.push(y);
            let (nonce, beta) = challenger.grind_pow_and_sample_f128(claim_bits(li + 1));
            proof.claim_batch_grinding_nonces.push(nonce);
            level.add_eq_weight(&eq_z, beta, y);
        }
        t[T_OOD] += ti.elapsed();

        let ti = Instant::now();
        let (nonce, queries) = grind_and_sample_queries(
            challenger,
            config.grinding_bits[li] as u32,
            prev.block_len,
            config.queries[li],
            strat(li),
        );
        proof.grinding_nonces.push(nonce);
        let (nonce, alpha) = challenger
            .grind_pow_and_sample_f128_vec(consistency_bits(li), ceil_log2(config.queries[li]));
        proof.consistency_batch_grinding_nonces.push(nonce);
        t[T_OTHER_POW] += ti.elapsed();
        let ti = Instant::now();
        let opened_rows: Vec<Vec<F128>> = queries.iter().map(|&q| prev.row(q).to_vec()).collect();
        proof.openings.push(RecursiveProof {
            merkle_proof: merkle_paths_for(prev.tree, prev.block_len, &queries, strat(li)),
            opened_rows,
        });
        t[T_OPENS] += ti.elapsed();
        let ti = Instant::now();
        let rows = &proof.openings.last().expect("just pushed").opened_rows;
        let enforced = batched_consistency(rows, &queries, &gammas, &overflow, c, &alpha);
        let basis = induce_sumcheck_poly_auto(
            c,
            config.log_inv_rates[li],
            &eval_sk_at_vks(c),
            &vec![Vec::new(); queries.len()],
            &[],
            &queries,
            &alpha,
        )
        .0;
        debug_assert_eq!(level.dot(&basis), enforced, "consistency claim must hold");
        let (nonce, beta) = challenger.grind_pow_and_sample_f128(claim_bits(li + 1));
        proof.claim_batch_grinding_nonces.push(nonce);
        level.add_weight(&basis, beta, enforced);
        t[T_INDUCE] += ti.elapsed();
        proof.overflows.push(overflow);
        committed.push(next);
    }

    let ms = |d: Duration| d.as_secs_f64() * 1e3;
    let timings = ProveTimings {
        fold_answers_ms: 0.0,
        folds_ms: ms(t[T_FOLDS]),
        fold_grinding_ms: ms(t[T_FOLD_POW]),
        other_grinding_ms: ms(t[T_OTHER_POW]),
        ood_ms: ms(t[T_OOD]),
        commits_ms: ms(t[T_COMMITS]),
        opens_ms: ms(t[T_OPENS]),
        induce_ms: ms(t[T_INDUCE]),
        total_ms: ms(t_total.elapsed()),
    };
    (proof, timings)
}

#[cfg(test)]
mod tests {
    use super::{F128, first_grid, fold_pass, kernels, prove_affine_fast};
    use crate::{
        challenger::{Challenger, FsChallenger, RandomChallenger},
        lincheck::build_eq_table,
        merkle::HashKind,
        ntt::additive_ntt_f128::AdditiveNttF128,
        pcs::ligerito::{
            ProverConfig, VerifierConfig,
            affine::{
                AffineProof, affine_configs, carry_products, prove_affine, t_at, verify_affine,
            },
            ligero_commit, partial_eval_lsb,
        },
    };

    fn random_vec(rng: &mut RandomChallenger, len: usize) -> Vec<F128> {
        (0..len).map(|_| rng.sample_f128()).collect()
    }

    /// The selected kernels against their portable definitions.
    #[test]
    fn kernels_match_definitions() {
        let mut rng = RandomChallenger::new(0xAFF1_F001);
        for rows in [2usize, 4, 8, 64] {
            let fc = random_vec(&mut rng, rows);
            let wc = random_vec(&mut rng, rows);
            let a = random_vec(&mut rng, rows);
            let b = random_vec(&mut rng, rows);
            let (ca, cb) = (rng.sample_f128(), rng.sample_f128());
            for (a, b) in [(None, None), (Some(&a[..]), None), (Some(&a[..]), Some(&b[..]))] {
                assert_eq!(
                    kernels::grid_column(&fc, &wc, a, b),
                    kernels::grid_column_portable(&fc, &wc, a, b),
                    "grid, rows = {rows}"
                );
                let mut got = vec![F128::ZERO; rows / 2];
                let mut want = vec![F128::ZERO; rows / 2];
                kernels::fold_column(&fc, a, b, ca, cb, &mut got);
                kernels::fold_column_portable(&fc, a, b, ca, cb, &mut want);
                assert_eq!(got, want, "fold, rows = {rows}");
            }
            // The definition of the grid sums, with reduced products.
            let (g, u) = kernels::grid_column(&fc, &wc, Some(&a), Some(&b));
            let sum = |f: &dyn Fn(usize) -> F128| {
                (0..rows / 2).fold(F128::ZERO, |acc, m| acc + f(m))
            };
            assert_eq!(g[0].reduce(), sum(&|m| fc[2 * m] * wc[2 * m]));
            assert_eq!(g[1].reduce(), sum(&|m| fc[2 * m] * wc[2 * m + 1]));
            assert_eq!(g[2].reduce(), sum(&|m| fc[2 * m + 1] * wc[2 * m]));
            assert_eq!(u[0].reduce(), sum(&|m| (a[2 * m + 1] + b[2 * m + 1]) * wc[2 * m]));
            assert_eq!(u[1].reduce(), sum(&|m| (a[2 * m + 1] + b[2 * m + 1]) * wc[2 * m + 1]));
        }
    }

    /// One round of the passes against the three passes of Flock's `Level`
    /// (`T f_1`, the grid, the fold), on tables with an overflow and with
    /// blocks of several sizes.
    #[test]
    fn passes_match_the_definition() {
        let mut rng = RandomChallenger::new(0xAFF1_F002);
        for (log_rows, log_live, extra) in [(1usize, 3usize, 0usize), (2, 5, 0), (3, 4, 2), (6, 9, 0), (4, 12, 3), (2, 13, 1)] {
            let (rows, live) = (1usize << log_rows, 1usize << log_live);
            let width = live + extra;
            let f = random_vec(&mut rng, rows * width);
            let w = random_vec(&mut rng, rows * live);
            let p = carry_products(log_live + log_rows + 2);
            let (alpha, beta, r) = (rng.sample_f128(), rng.sample_f128(), rng.sample_f128());
            // The definition, entry by entry.
            let half = rows / 2;
            let t = |m: usize, col: usize| t_at(|j| f[2 * (m + half * j) + 1], width, col, &p);
            let grid_of = |f: &[F128], w: &[F128], rows: usize, width: usize| -> [F128; 5] {
                let half = rows / 2;
                let live = w.len() / rows;
                let mut g = [F128::ZERO; 5];
                for q in 0..half * live {
                    let (m, col) = (q % half, q / half);
                    let (f0, f1) = (f[2 * q], f[2 * q + 1]);
                    let (w0, w1) = (w[2 * q], w[2 * q + 1]);
                    let t = t_at(|j| f[2 * (m + half * j) + 1], width, col, &p);
                    g[0] += f0 * w0;
                    g[1] += f0 * w1;
                    g[2] += f1 * w0;
                    g[3] += t * w0;
                    g[4] += t * w1;
                }
                g
            };
            assert_eq!(first_grid(&f, &w, rows, width, &p), grid_of(&f, &w, rows, width), "first grid");
            let want_f: Vec<F128> = (0..half * (width + 1))
                .map(|q| {
                    let (m, col) = (q % half, q / half);
                    let base = if col < width { f[2 * q] + alpha * f[2 * q + 1] } else { F128::ZERO };
                    base + beta * t(m, col)
                })
                .collect();
            let want_w: Vec<F128> =
                (0..half * live).map(|q| w[2 * q] + r * (w[2 * q] + w[2 * q + 1])).collect();
            let look = half >= 2;
            let (got_f, got_w, next) = fold_pass(&f, &w, rows, width, (alpha, beta, r), &p, look);
            assert_eq!(got_f, want_f, "folded table, rows = {rows}, width = {width}");
            assert_eq!(got_w, want_w, "folded weight");
            if look {
                assert_eq!(next.expect("looked ahead"), grid_of(&want_f, &want_w, half, width + 1), "next grid");
            }
        }
    }

    struct Shape {
        log_n: usize,
        initial_k: usize,
        ks: Vec<usize>,
        rates: Vec<usize>,
        ood: Vec<usize>,
    }

    fn ladder(s: &Shape) -> (ProverConfig, VerifierConfig) {
        let levels = s.ks.len() + 1;
        let split = ProverConfig {
            log_inv_rates: s.rates.clone(),
            recursive_steps: s.ks.len(),
            initial_log_msg_cols: s.log_n - s.initial_k,
            initial_log_num_interleaved: s.initial_k,
            initial_k: s.initial_k,
            recursive_log_msg_cols: vec![0; s.ks.len()],
            recursive_ks: s.ks.clone(),
            queries: vec![23, 17, 13, 11][..levels].to_vec(),
            grinding_bits: vec![2; levels],
            fold_grinding_bits: vec![0; levels],
            claim_batch_grinding_bits: vec![1; levels],
            consistency_batch_grinding_bits: vec![1; levels],
            ood_samples: s.ood.clone(),
            merkle_hash: HashKind::Blake3,
            stratified: vec![],
        };
        affine_configs(&split, s.log_n, &[2, 3, 3, 3][..levels])
    }

    /// The fast prover writes the proof of Flock's prover, and Flock's
    /// verifier accepts it: several shapes, with and without out-of-domain
    /// samples (also with none on the first commitment only).
    #[test]
    fn fast_matches_flock() {
        let shapes = [
            Shape { log_n: 14, initial_k: 3, ks: vec![2, 2, 2], rates: vec![1, 2, 2, 3], ood: vec![1, 2, 2, 2] },
            Shape { log_n: 14, initial_k: 3, ks: vec![2, 2, 2], rates: vec![1, 2, 2, 3], ood: vec![0, 2, 2, 2] },
            Shape { log_n: 14, initial_k: 3, ks: vec![2, 2, 2], rates: vec![1, 2, 2, 3], ood: vec![0, 0, 0, 0] },
            Shape { log_n: 16, initial_k: 6, ks: vec![4], rates: vec![1, 3], ood: vec![1, 2] },
            Shape { log_n: 16, initial_k: 6, ks: vec![4], rates: vec![1, 3], ood: vec![0, 2] },
            Shape { log_n: 15, initial_k: 5, ks: vec![3, 2], rates: vec![2, 3, 4], ood: vec![2, 1, 2] },
            Shape { log_n: 12, initial_k: 1, ks: vec![1, 1, 1], rates: vec![1, 1, 2, 2], ood: vec![1, 1, 1, 1] },
            Shape { log_n: 17, initial_k: 4, ks: vec![4, 4], rates: vec![1, 3, 5], ood: vec![0, 2, 2] },
        ];
        for (i, s) in shapes.iter().enumerate() {
            let (prover, verifier) = ladder(s);
            let mut rng = RandomChallenger::new(0xAFF1_F003 + i as u64);
            let witness = random_vec(&mut rng, 1 << s.log_n);
            let z1 = random_vec(&mut rng, s.log_n);
            let z2 = random_vec(&mut rng, s.log_n);
            let gamma = rng.sample_f128();
            let basis: Vec<F128> = build_eq_table(&z1)
                .into_iter()
                .zip(build_eq_table(&z2))
                .map(|(a, b)| a + gamma * b)
                .collect();
            let target = witness
                .iter()
                .zip(&basis)
                .fold(F128::ZERO, |acc, (&a, &b)| acc + a * b);
            let rate = prover.log_inv_rates[0];
            let ntt = AdditiveNttF128::standard(s.log_n - s.initial_k + rate);
            let l0 = ligero_commit(
                &witness,
                s.log_n - s.initial_k,
                s.initial_k,
                rate,
                &ntt,
                HashKind::Blake3,
            );
            let cap = l0.cap(prover.level_zero_cap_depth()).to_vec();
            let prove = |fast: bool| -> AffineProof {
                let mut ch = FsChallenger::new(b"affine-fast-test");
                if fast {
                    prove_affine_fast(&prover, witness.clone(), basis.clone(), target, &l0.mat, &l0.tree, &mut ch)
                } else {
                    prove_affine(&prover, witness.clone(), basis.clone(), target, &l0.mat, &l0.tree, &mut ch)
                }
            };
            let (fast, flock) = (prove(true), prove(false));
            assert_eq!(fast, flock, "shape {i}: the two provers must write the same proof");
            assert_eq!(fast.ood_values.len(), s.ood.iter().sum::<usize>());
            let mut ch = FsChallenger::new(b"affine-fast-test");
            let ok = verify_affine(
                &verifier,
                &fast,
                s.log_n,
                target,
                &cap,
                |rs, residual_log| {
                    let out = partial_eval_lsb(&basis, rs);
                    assert_eq!(out.len(), 1usize << residual_log);
                    out
                },
                &mut ch,
            );
            assert!(ok, "shape {i}: Flock's verifier must accept");
        }
    }
}
