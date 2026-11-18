#!/bin/sh
# [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request; please review]
# [AI-revised (claude-opus-5-5), 2026-11-16: copied into the repository BEEP; the paper's numbers in the comments
# are those of its current numbering within sections (Theorem 5.3, Lemma 5.5); please review]
# [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request: the script also checks the formalization of
# Theorem 3.4, with its own examples and axioms; the files are compiled once into a scratch folder, and the root
# file BEEP.lean and the examples import them from there; please review]
# [AI-revised (claude-fable-5-2), 2026-11-17, at the author's request: the two Lean files are now six, BEEP/Scalar
# (Theorem 3.4) and BEEP/Affine (Theorem 5.3), each with Defs.lean, Proof.lean and Theorem.lean. The script
# compiles them in the order of their imports. The examples are the same, in the namespaces BEEP.Scalar and
# BEEP.Affine. New: steps 1 and 5, and the script now stops with an error if a theorem depends on an axiom other
# than the three standard ones; please review]
# [AI-revised (claude-fable-5-2), 2026-11-17, later: in the examples, `hits` takes the pair `(b₁, b₂)`]
# Checks the Lean formalizations of the BEEP paper (paper/main.typ) with the Mathlib build of ~/math in lean
# (Mathlib v4.30.0), in about a minute on an idle machine. Every `lean` call passes the options of
# lakefile.toml, `-DautoImplicit=false -DrelaxedAutoImplicit=false`, so that an undeclared name in a statement is
# an error instead of an automatically bound implicit variable.
#   1. BEEP/Scalar/Defs.lean and BEEP/Affine/Defs.lean, the files of definitions, import Mathlib only, and
#      BEEP/Scalar/Proof.lean and BEEP/Affine/Proof.lean contain definitions and theorems only (no notation, no
#      instance, no attribute, no axiom), so they cannot change how a statement of Theorem.lean is read;
#   2. the six files type-check, in the order Defs.lean, Proof.lean, Theorem.lean (no output from Lean means
#      success), and so does the root file BEEP.lean, which imports both Theorem.lean (so the two formalizations
#      can be used together);
#   3. examples for BEEP/Affine apply its theorems to concrete data, with every hypothesis proved: a `Setup` over
#      ZMod 5 with the weights (1, α), another with the weights (1 - α, α) of Section 4, `affine_main` for both,
#      and `affine_main_delta` for the second (with δ = 1/4), all with the trivial list size. So the hypotheses
#      can be met; with the trivial list size the bounds are above 1, so the examples show that the theorems
#      apply, not a useful bound. They also check a form with an assumed list decodability (the general case);
#   4. examples for BEEP/Scalar do the same for Theorem 3.4: a Reed-Solomon code of dimension 2 on four points of
#      ZMod 5, the univariate zero evader with one sample and its error bound 1/5 (proved), the weights (1, α)
#      and (1 - α, α), `main_thm` for both, `main_thm_delta` and `main_thm_delta_real` for the second (with
#      δ = 1/4) and `main_thm_delta_floor` (with δ = 3/10, for which δ n is not an integer), all with the trivial
#      list size (so, again, the bounds are above 1). They also exhibit a pretender and a DEEP-MCA-bad element in
#      a concrete case, so the definitions are not vacuous;
#   5. the statement of every theorem of the two Theorem.lean mentions only declarations of the Defs.lean of
#      its folder and of Mathlib: to know what these theorems say, it is enough to read Defs.lean and
#      Theorem.lean;
#   6. the axioms of the theorems are printed, and each must depend only on propext, Classical.choice and
#      Quot.sound.
# The compiled files and the example files go to the folder $TMPDIR/beep-lean-check (or /tmp/beep-lean-check);
# nothing is written next to this script.
# Do not run it while a benchmark campaign holds /tmp/bitz-bench.lock.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
MIL="$HOME/math in lean"
OUT="${TMPDIR:-/tmp}/beep-lean-check"
if [ -e /tmp/bitz-bench.lock ]; then
  echo "a benchmark campaign holds /tmp/bitz-bench.lock; not checking now" >&2
  exit 1
fi
echo "== the files of definitions import Mathlib only; the files of proofs have definitions and theorems only"
for d in Scalar Affine; do
  if [ "$(grep '^import' "$HERE/BEEP/$d/Defs.lean")" != "import Mathlib" ]; then
    echo "BEEP/$d/Defs.lean must import Mathlib and nothing else" >&2
    exit 1
  fi
  if [ "$(grep '^import' "$HERE/BEEP/$d/Proof.lean")" != "import BEEP.$d.Defs" ]; then
    echo "BEEP/$d/Proof.lean must import BEEP.$d.Defs and nothing else" >&2
    exit 1
  fi
  # A command of Proof.lean that could change the meaning of a later file: none is allowed.
  if grep -n -E '^[[:space:]]*(@\[|((local|scoped|private|protected|unsafe|partial)[[:space:]]+)*(notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|instance|attribute|axiom|opaque|export|initialize|declare_syntax_cat|binder_predicate|unif_hint|deriving|abbrev|alias)([[:space:]]|$))' \
      "$HERE/BEEP/$d/Proof.lean"; then
    echo "BEEP/$d/Proof.lean must contain definitions and theorems only" >&2
    exit 1
  fi
done
# Start from an empty scratch folder, so that nothing compiled earlier is used.
rm -rf "$OUT"
mkdir -p "$OUT/BEEP/Scalar" "$OUT/BEEP/Affine"
cd "$MIL"
# `lean` with the options of lakefile.toml and with the compiled modules of $OUT on its search path, in front of
# those of Mathlib.
lean_with_beep() {
  lake env sh -c 'out="$1"; shift; LEAN_PATH="$out:$LEAN_PATH" exec lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$@"' sh "$OUT" "$@"
}
# `-R` gives the folder from which the module name of a file is computed (BEEP.Scalar.Defs, ...), and `-o` writes
# the compiled module, which the later steps import.
for m in Scalar/Defs Scalar/Proof Scalar/Theorem Affine/Defs Affine/Proof Affine/Theorem; do
  echo "== type-checking BEEP/$m.lean"
  lean_with_beep -R "$HERE" -o "$OUT/BEEP/$m.olean" "$HERE/BEEP/$m.lean"
done
echo "== the root file BEEP.lean, which imports both"
lean_with_beep "$HERE/BEEP.lean"
# Runs a file of examples that ends with `#print axioms` commands, shows its output, and stops if a line of the
# output is not "... depends on axioms: [propext, Classical.choice, Quot.sound]".
run_examples() {
  lean_with_beep "$1" > "$1.out" 2>&1 || { cat "$1.out"; exit 1; }
  cat "$1.out"
  if grep -v -F -e "depends on axioms: [propext, Classical.choice, Quot.sound]" "$1.out" | grep -q .; then
    echo "unexpected output above: an error, a warning, or an axiom other than the three standard ones" >&2
    exit 1
  fi
}
echo "== examples and axioms of BEEP/Affine (file $OUT/ExamplesAffine.lean)"
{
  cat <<'EOF'
import BEEP.Affine.Theorem

namespace BEEP.Affine
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

end BEEP.Affine
EOF
  for t in Setup.affine_line_pairs Setup.affine_line Setup.affine_main_gen_nat \
      Setup.affine_main_gen Setup.affine_main_nat Setup.affine_main Setup.fold_challenge_le \
      Setup.affine_main_delta Setup.isPretender_ceil_iff Setup.listDecodable_of_delta \
      Setup.card_close_rsWords defect_eq_zero_of_onLine pair_count_arith listDecodable_trivial; do
    echo "#print axioms BEEP.Affine.$t"
  done
} > "$OUT/ExamplesAffine.lean"
run_examples "$OUT/ExamplesAffine.lean"
echo "== examples and axioms of BEEP/Scalar (file $OUT/ExamplesScalar.lean)"
{
  cat <<'EOF'
import BEEP.Scalar.Theorem

namespace BEEP.Scalar
open Finset Classical

-- `ZMod 5` is a field, since 5 is prime.
instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

-- The Reed-Solomon code of dimension 2 on the points 0, 1, 2, 3 of `ZMod 5`: the message
-- `(w₀, w₁)` is encoded as the word with entries `w₀ + w₁ · i`.
def encRS : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5) where
  toFun w := fun i => w 0 + w 1 * ((i : ℕ) : ZMod 5)
  map_add' := by intro v w; funext i; simp only [Pi.add_apply]; ring
  map_smul' := by
    intro a w; funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

-- The encoding map is injective: the entries at the points 0 and 1 determine the message.
theorem encRS_injective : Function.Injective encRS := by
  intro v w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [encRS] at h0 h1
  funext j
  fin_cases j
  · exact h0
  · simpa [h0] using h1

-- The univariate zero evader with one sample (Definition 2.4 with `m = 1`): `Z = ZMod 5` and
-- `φ_z(w₀, w₁) = w₀ + w₁ z`.
def evUni (z : ZMod 5) : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 1 → ZMod 5) where
  toFun w := fun _ => w 0 + w 1 * z
  map_add' := by intro v w; funext _; simp only [Pi.add_apply]; ring
  map_smul' := by
    intro a w; funext _; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

-- A nonzero `(w₀, w₁)` has `w₀ + w₁ z = 0` for at most one `z` (Lemma 2.5 with `e = 2`, `m = 1`).
theorem evUni_card_le_one (v : Fin 2 → ZMod 5) (hv : v ≠ 0) :
    (univ.filter fun z : ZMod 5 => evUni z v = 0).card ≤ 1 := by
  rw [card_le_one]
  intro z hz z' hz'
  simp only [mem_filter, mem_univ, true_and] at hz hz'
  have e := congrFun hz 0
  have e' := congrFun hz' 0
  simp only [evUni, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at e e'
  by_contra hne
  apply hv
  have h1 : v 1 * (z - z') = 0 := by linear_combination e - e'
  have hv1 : v 1 = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)
  have hv0 : v 0 = 0 := by rw [hv1] at e; simpa using e
  funext j
  fin_cases j
  · exact hv0
  · exact hv1

-- A setup over `F = ZMod 5` with this code, this evader and the given weights.
def setupRS (a₁ d₁ a₂ d₂ : ZMod 5) (h : a₁ * d₂ ≠ a₂ * d₁) :
    Setup (ZMod 5) (Fin 4) (ZMod 5) where
  ℓ := 2
  m := 1
  enc := encRS
  enc_inj := encRS_injective
  a₁ := a₁
  d₁ := d₁
  a₂ := a₂
  d₂ := d₂
  det_ne := h
  φ := evUni

-- The weights `(1, α)` (`a₁ = 1`, `d₁ = 0`, `a₂ = 0`, `d₂ = 1`).
def setupOneAlpha : Setup (ZMod 5) (Fin 4) (ZMod 5) := setupRS 1 0 0 1 (by decide)

-- The weights `(1 - α, α)` of Section 4 (`a₁ = 1`, `d₁ = -1`, `a₂ = 0`, `d₂ = 1`).
def setupBEEP : Setup (ZMod 5) (Fin 4) (ZMod 5) := setupRS 1 (-1) 0 1 (by decide)

-- `1/5` is an error bound of the evader of these setups.
theorem setupRS_errorBound (a₁ d₁ a₂ d₂ : ZMod 5) (h : a₁ * d₂ ≠ a₂ * d₁) :
    (setupRS a₁ d₁ a₂ d₂ h).IsErrorBound (1 / 5) := by
  refine ⟨by norm_num, fun v hv => ?_⟩
  -- `|Z| = 5`, and the goal becomes `#{z | φ_z(v) = 0} / 5 ≤ 1 / 5`.
  have hZ : (Fintype.card (ZMod 5) : ℝ) = 5 := by simp [ZMod.card]
  rw [hZ]
  -- Divide both sides by `5` (`gcongr`) and go back to `ℕ` (`norm_cast`). Over `ZMod 5` the
  -- filter of `evUni_card_le_one` decides `φ_z(v) = 0` with the equality test of `ZMod 5`, while
  -- `IsErrorBound`, stated for every field, uses classical logic; `convert` identifies the two.
  gcongr
  norm_cast
  convert evUni_card_le_one v hv

-- The list decodability of Theorem 3.4 always holds with the trivial list size, the number of
-- messages.
theorem listDecodable_trivial {F ι Z : Type*} [Field F] [Fintype F] [Fintype ι]
    (R : Setup F ι Z) (s : ℕ) : R.ListDecodable s (Fintype.card (Fin R.ℓ → F)) :=
  fun _ => card_le_univ _

-- Theorem 3.4 applies to both setups with every hypothesis proved: the agreement threshold
-- `s = 3` (so `n - s + 2 = 3`), the trivial list size, the error bound `1/5`, and `t = 3`.
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupOneAlpha.main_thm u₁ u₂ 3 _ 3 (1 / 5) (listDecodable_trivial setupOneAlpha 3)
    (setupRS_errorBound _ _ _ _ _) (by simp)
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.main_thm u₁ u₂ 3 _ 3 (1 / 5) (listDecodable_trivial setupBEEP 3)
    (setupRS_errorBound _ _ _ _ _) (by simp)

-- The form with `δ`, with every hypothesis proved: `δ = 1/4` (so `δ n = 1`), `t = 3 ≥ δ n + 2`,
-- and the list size `#C`, the number of codewords.
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.main_thm_delta u₁ u₂ (δ := 1 / 4) (by norm_num) _ 3
    (fun _ => card_filter_le _ _) (setupRS_errorBound _ _ _ _ _) (by norm_num)

-- The same for the real threshold `t = 7/2`.
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.main_thm_delta_real u₁ u₂ (δ := 1 / 4) (by norm_num) _ (7 / 2)
    (fun _ => card_filter_le _ _) (setupRS_errorBound _ _ _ _ _) (by norm_num)

-- The form with `⌊δ n⌋`, for `δ = 3/10`. Here `δ n = 1.2` is not an integer and `⌊δ n⌋ + 2 = 3`:
-- the threshold `t = 3` is covered by this form and not by `main_thm_delta`, which asks for
-- `t ≥ δ n + 2 = 3.2`.
theorem floor_three_tenths : ⌊(3 / 10 : ℝ) * (Fintype.card (Fin 4) : ℝ)⌋₊ = 1 := by
  -- `Nat.floor_eq_iff : ⌊a⌋₊ = k ↔ k ≤ a ∧ a < k + 1`, for `a ≥ 0`.
  rw [Nat.floor_eq_iff (by positivity)]
  norm_num
example (u₁ u₂ : Fin 4 → ZMod 5) :=
  setupBEEP.main_thm_delta_floor u₁ u₂ (δ := 3 / 10) (by norm_num) _ 3
    (fun _ => card_filter_le _ _) (setupRS_errorBound _ _ _ _ _) (by rw [floor_three_tenths])

-- The definitions are not vacuous. Take the weights `(1, α)`, the words `u₁ = (0, 0, 1, 0)` and
-- `u₂ = (0, 0, -1, 0)`, and the agreement threshold `s = 3`. The fold at `α = 1` is `u₁ + u₂ = 0`,
-- a codeword, while `u₁` agrees with no codeword on `S = {0, 1, 2}` (its entries `0, 0, 1` there
-- are not those of a polynomial of degree at most one). So the zero codeword is a `1`-pretender.
def w₁ : Fin 4 → ZMod 5 := ![0, 0, 1, 0]
def w₂ : Fin 4 → ZMod 5 := ![0, 0, -1, 0]

theorem encRS_apply (w : Fin 2 → ZMod 5) (i : Fin 4) :
    encRS w i = w 0 + w 1 * ((i : ℕ) : ZMod 5) := rfl

theorem zero_isPretender : setupOneAlpha.IsPretender w₁ w₂ 3 1 0 := by
  refine ⟨{0, 1, 2}, by decide, ?_, ?_⟩
  · intro i hi
    rw [map_zero, Pi.zero_apply]
    fin_cases i <;>
      simp [setupOneAlpha, setupRS, Setup.fold, Setup.lam₁, Setup.lam₂, w₁, w₂] at hi ⊢
  · rintro ⟨c₁, c₂, h⟩
    have h0 := (h 0 (by decide)).1
    have h1 := (h 1 (by decide)).1
    have h2 := (h 2 (by decide)).1
    change w₁ 0 = encRS c₁ 0 at h0
    change w₁ 1 = encRS c₁ 1 at h1
    change w₁ 2 = encRS c₁ 2 at h2
    rw [encRS_apply] at h0 h1 h2
    simp [w₁] at h0 h1 h2
    -- Now `h0 : 0 = c₁ 0`, `h1 : 0 = c₁ 0 + c₁ 1` and `h2 : 1 = c₁ 0 + c₁ 1 * 2`, so `1 = 0`.
    have h10 : (1 : ZMod 5) = 0 := by linear_combination h2 - 2 * h1 + h0
    exact absurd h10 (by decide)

-- Hence `α = 1` is a DEEP-MCA-bad element with respect to every `z` and `b₁ = b₂ = 0`:
-- `φ_z(0) = 0 = λ₁(1) · 0 + λ₂(1) · 0`. In particular `|A_z| ≥ 1` for every `z`.
theorem one_mem_hits (z : ZMod 5) :
    (1 : ZMod 5) ∈ setupOneAlpha.hits w₁ w₂ 3 z (0, 0) := by
  simp only [Setup.hits, mem_filter, mem_univ, true_and]
  refine ⟨(setupOneAlpha.mcaBad_iff_exists_pretender w₁ w₂ 3 1).mpr ⟨0, zero_isPretender⟩,
    0, zero_isPretender, ?_⟩
  simp [Setup.Consistent]

example (z : ZMod 5) : 1 ≤ setupOneAlpha.maxHits w₁ w₂ 3 z :=
  (card_pos.mpr ⟨1, one_mem_hits z⟩).trans_le
    (setupOneAlpha.card_hits_le_maxHits w₁ w₂ 3 z (0, 0))

end BEEP.Scalar
EOF
  for t in Setup.mcaBad_iff_exists_pretender Setup.few_pretenders_on_line defect_eq_zero_iff \
      Setup.evader_defect_eq_zero Setup.third_moment_bound Setup.main_thm_gen_nat \
      Setup.main_thm_gen Setup.main_thm_nat Setup.main_thm Setup.fold_challenge_le \
      Setup.card_filter_codewords Setup.satisfiesMCA_ceil_iff Setup.isPretender_ceil_iff \
      Setup.listDecodable_of_delta Setup.main_thm_delta Setup.main_thm_delta_real \
      Setup.main_thm_delta_floor setupRS_errorBound listDecodable_trivial zero_isPretender \
      one_mem_hits; do
    echo "#print axioms BEEP.Scalar.$t"
  done
} > "$OUT/ExamplesScalar.lean"
run_examples "$OUT/ExamplesScalar.lean"
echo "== the statements of Theorem.lean mention only Defs.lean and Mathlib (file $OUT/Statements.lean)"
cat > "$OUT/Statements.lean" <<'EOF'
import BEEP.Scalar.Theorem
import BEEP.Affine.Theorem
open Lean

-- For every declaration of the module `thms`: it is a theorem, and each constant in its statement
-- is declared by the module `defs` or by a module outside `BEEP` (Mathlib, Lean). It is an error
-- otherwise.
def checkStatements (defs thms : Name) : CoreM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? thms | throwError "the module {thms} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  if names.isEmpty then throwError "{thms} declares nothing"
  for n in names do
    let some ci := env.find? n | throwError "unknown declaration {n}"
    unless ci matches .thmInfo _ do
      throwError "{thms} declares {n}, which is not a theorem"
    for c in ci.type.getUsedConstants do
      if let some i := env.getModuleIdxFor? c then
        let m := env.header.moduleNames[i.toNat]!
        if (`BEEP).isPrefixOf m && m != defs then
          throwError "the statement of {n} mentions {c}, which {m} declares"
  let sorted := names.qsort fun a b => a.toString < b.toString
  IO.println s!"{thms}: the statements of its {names.size} theorems mention only {defs} and Mathlib: {sorted.toList}"

#eval checkStatements `BEEP.Scalar.Defs `BEEP.Scalar.Theorem
#eval checkStatements `BEEP.Affine.Defs `BEEP.Affine.Theorem
EOF
lean_with_beep "$OUT/Statements.lean"
echo "== done"
