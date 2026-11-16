#!/bin/sh
# [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request; please review]
# [AI-revised (claude-opus-5-5), 2026-11-16: copied into the repository BEEP; the paper's numbers in the comments
# are those of its current numbering within sections (Theorem 5.3, Lemma 5.5); please review]
# Checks BEEP/AffineMain.lean (Theorem 5.3 and Lemma 5.5 of the BEEP paper, typst/deep+.typ) with the
# Mathlib build of ~/math in lean (Mathlib v4.30.0), in about a minute on an idle machine. Every
# `lean` call passes the options of lakefile.toml, `-DautoImplicit=false -DrelaxedAutoImplicit=false`,
# so that an undeclared name in a statement is an error instead of an automatically bound implicit
# variable.
#   1. the file type-checks (no output from Lean means success);
#   2. a scratch file made of the file plus a few examples applies the theorems to concrete data,
#      with every hypothesis proved: a `Setup` over ZMod 5 with the weights (1, α), another with
#      the weights (1 - α, α) of Section 4, `affine_main` for both, and `affine_main_delta` for
#      the second (with δ = 1/4), all with the trivial list size. So the hypotheses can be met; with
#      the trivial list size the bounds are above 1, so the examples show that the theorems apply,
#      not a useful bound. It also checks a form with an assumed list decodability (the general
#      case), and prints the axioms of the main theorems (each should depend only on propext,
#      Classical.choice and Quot.sound).
# The scratch file goes to $TMPDIR (or /tmp); nothing is written next to this script.
# Do not run it while a benchmark campaign holds /tmp/bitz-bench.lock.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
MIL="$HOME/math in lean"
SCRATCH="${TMPDIR:-/tmp}/beep-affine-check.lean"
# The options of lakefile.toml.
OPTS="-DautoImplicit=false -DrelaxedAutoImplicit=false"
if [ -e /tmp/bitz-bench.lock ]; then
  echo "a benchmark campaign holds /tmp/bitz-bench.lock; not checking now" >&2
  exit 1
fi
cd "$MIL"
echo "== type-checking BEEP/AffineMain.lean"
lake env lean $OPTS "$HERE/BEEP/AffineMain.lean"
echo "== examples and axioms (scratch file $SCRATCH)"
{
  cat "$HERE/BEEP/AffineMain.lean"
  cat <<'EOF'

namespace BEEP
open Finset Polynomial Classical

-- `ZMod 5` is a field, since 5 is prime.
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- A setup over `F = ZMod 5`, with the points `0, 1, 2, 3`, the code dimension `ℓ = 1` and the
-- weights `(1, α)` of CWYZ26 (`a₁ = 1`, `d₁ = 0`, `a₂ = 0`, `d₂ = 1`).
def setupOneAlpha : Setup (ZMod 5) (Fin 4) where
  x := fun i => ((i : ℕ) : ZMod 5)
  x_inj := by decide
  ℓ := 1
  a₁ := 1
  d₁ := 0
  a₂ := 0
  d₂ := 1
  det_ne := by decide

-- The weights `(1 - α, α)` of Section 4 (`a₁ = 1`, `d₁ = -1`, `a₂ = 0`, `d₂ = 1`).
def setupBEEP : Setup (ZMod 5) (Fin 4) where
  x := fun i => ((i : ℕ) : ZMod 5)
  x_inj := by decide
  ℓ := 1
  a₁ := 1
  d₁ := -1
  a₂ := 0
  d₂ := 1
  det_ne := by decide

-- The list decodability of Theorem 5.3 always holds with the trivial list size, the number of
-- polynomials of degree at most `ℓ`.
theorem listDecodable_trivial {F ι : Type*} [Field F] [Fintype F] [Fintype ι] (R : Setup F ι)
    (s : ℕ) : R.ListDecodable s (polysLT F (R.ℓ + 1)).card :=
  fun _ => card_filter_le _ _

-- Theorem 5.3 applies to both setups with every hypothesis proved: `m = 3` samples, the agreement
-- threshold `s = 3`, the trivial list size, and `t = 6`, since here
-- `N = max(5, (4 - 3 + 2)(4 - 3 + 1)/2) = 5`.
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupOneAlpha.affine_main u₁ u₂ 3 (m := 3) _ 6 (listDecodable_trivial setupOneAlpha 3) (by simp)
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.affine_main u₁ u₂ 3 (m := 3) _ 6 (listDecodable_trivial setupBEEP 3) (by simp)

-- The form with `δ`, with every hypothesis proved: `δ = 1/4` (so `δ n = 1` and the paper's `N` is
-- `max(5, 3 · 2/2) = 5`), `ℓ + 1 = 2 ≤ 4 = n`, `t = 6`, and the list size `#RS_2`, the number of
-- codewords (`card_filter_le`: a filter has at most as many elements as the set it filters).
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.affine_main_delta u₁ u₂ (m := 3) (δ := 1 / 4) (by norm_num) _ 6
    (by simp [setupBEEP]) (fun _ => card_filter_le _ _) (by norm_num [max_def])

-- The form with `δ` with an assumed list decodability. Over `ZMod 5` the filter in `hL` decides
-- `c i ≠ w i` with the equality test of `ZMod 5`, while the theorem, stated for every field, uses
-- classical logic; `convert` identifies the two (any two proofs of decidability are equal).
example (u₁ u₂ : Fin 4 → ZMod 5) (δ : ℝ) (hδ : 0 ≤ δ) (L t : ℕ)
    (hL : ∀ w : Fin 4 → ZMod 5, ((setupOneAlpha.rsWords (setupOneAlpha.ℓ + 1)).filter fun c =>
      ((univ.filter fun i => c i ≠ w i).card : ℝ) ≤ δ * Fintype.card (Fin 4)).card ≤ L)
    (ht : max (Fintype.card (ZMod 5) : ℝ)
      ((δ * Fintype.card (Fin 4) + 2) * (δ * Fintype.card (Fin 4) + 1) / 2) + 1 ≤ t) :=
  setupOneAlpha.affine_main_delta u₁ u₂ (m := 3) hδ L t (by simp [setupOneAlpha]) (by convert hL)
    ht

end BEEP
EOF
  for t in Setup.affine_line_pairs Setup.affine_line Setup.affine_main_gen_nat \
      Setup.affine_main_gen Setup.affine_main_nat Setup.affine_main Setup.fold_challenge_le \
      Setup.affine_main_delta Setup.isPretender_ceil_iff Setup.listDecodable_of_delta \
      Setup.card_close_rsWords defect_eq_zero_of_onLine pair_count_arith listDecodable_trivial; do
    echo "#print axioms BEEP.$t"
  done
} > "$SCRATCH"
lake env lean $OPTS "$SCRATCH"
echo "== done"
