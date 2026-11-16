-- [AI-drafted (claude-opus-5-5), 2026-11-14, at the author's request; please review]
-- [AI-revised (claude-opus-5-5), 2026-11-16: the paper's current numbers and labels; please review]
-- [AI-revised (claude-fable-5-2), 2026-11-16, at the author's request ("Let's add a lean
-- formalization of theorem 3.4"): the import of `BEEP.MainTheorem`; please review]
-- The Lean formalizations of results of the BEEP paper (`paper/main.typ`).
-- `BEEP/MainTheorem.lean`: Theorem 3.4 (`t:main_thm`) and Lemmas 3.7 to 3.10 of its proof.
-- `BEEP/AffineMain.lean`: Theorem 5.3 (`t:affine_main_0`) and Lemma 5.5 (`l:few_bad_points_on_line_0`).
-- The two files do not depend on each other. The names of the first are in the namespace
-- `BEEP.Main`, and those of the second in the namespace `BEEP`.
import BEEP.MainTheorem
import BEEP.AffineMain
