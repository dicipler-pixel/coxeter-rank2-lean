# Audit report — statement 14: `tits_indefinite_above_four`

| statement | standard fact | verdict | evidence | correction needed |
|---|---|---|---|---|
| `tits_indefinite_above_four (a b : ℕ) (ha:1≤a) (hb:1≤b) (hab:4<a*b) : (∃ x y:ℝ, 0 < titsForm a b x y) ∧ (∃ x y:ℝ, titsForm a b x y < 0)` with `titsForm a b x y = 2*b*x^2 -2*(a*b)*x*y +2*a*y^2` | Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4, Thm 4.3 and discussion of symmetrised invariant form (Ch. 2–4): for symmetrizable GCM of indefinite type the invariant bilinear form is indefinite, i.e. takes both positive and negative values; in rank-two with `a,b ≥1, ab>4` this is signature `(1,1)`, `det = ab(4-ab) <0`, non-degenerate indefinite. Bourbaki Ch. VI §1 gives same trichotomy (finite/affine/indefinite) for Tits form. | **matches** (definitionally; equivalent to signature `(1,1)` in rank-two) | Computation: `titsForm a b 1 0 = 2*b >0` when `b≥1`; `titsForm a b a 2 = 2*b*a^2 -2*a*b*a*2 +2*a*4 = -2*a^2*b+8*a = -2*a*(a*b-4) = 2*a*(4-a*b)`. Under `ha,hab`, `a>0` and `ab-4>0` so `<0`. Hence (1,0) witnesses positivity, (a,2) negativity. Determinant of matrix `[[2b,-ab],[-ab,2a]]` is `4ab-a^2b^2 = ab(4-ab) <0` when `ab>4`, so form non-degenerate; in dim 2 existence of both signs ⇔ `det<0` ⇔ signature `(1,1)` (degenerate non-zero `2×2` form is semidefinite: `det=0 ⇒ Q=±(linear)^2` or `0`). Hypotheses `1≤a,1≤b` redundant given `ab>4` in `ℕ` but harmless and ensure symmetriser `diag(b,a)` positive. No vacuity. Verified by direct expansion (sympy and Lean definitional unfolding). | None required. Docstring correctly says “takes both signs, so it is indefinite” — it does not over-claim radical spanning or converse. If explicit signature wording desired, add lemma `det <0` / non-degeneracy, but not needed for correctness; the two formulations are equivalent in rank-two. |

## True-but-not-what-it-says paragraph

The statement is true and carries the content its name suggests, with one nuance flagged in the brief: the standard literature has two phrasings — (i) *indefinite* defined as “`∃v Q(v)>0 ∧ ∃w Q(w)<0`” and (ii) *signature `(1,1)`* (non-degenerate indefinite). In general dimension (ii) is strictly stronger than (i) (degenerate indefinite exists for `n≥3`, e.g. `x^2-y^2` on `ℝ^3`). In rank-two (i) ⇔ (ii) for non-zero forms: a `2×2` real symmetric `Q` with `det=0` and `Q≠0` is semidefinite, so taking both signs forces `det<0` and conversely. Here `det = ab(4-ab) <0` exactly when `ab>4`, and for `a,b≥1` the form is not identically zero, so (i) already entails (ii). The witnesses `(1,0)` and `(a,2)` therefore suffice for what the standard signature claim requires; proving `(i)` is proving `(1,1)` up to the elementary `2×2` lemma. The hypotheses `ha,hb` are formally redundant (`a*b>4` in `ℕ` implies `a,b≥1`) but match the rest of the file and make positivity of the symmetriser explicit. No missing faithful-action or carrier issue: the Tits form is defined on `ℝ^2` as intended.

## Blindness

Did **not** open any forbidden files: `$REPO/RankTwoClassification.lean`, `$REPO/swarm/Classification.lean`, `$REPO/swarm/selftest/`, `$REPO/swarm/submissions/`, `$REPO/swarm/RESULT.md`, `$REPO/swarm/AUDIT.md`, `$REPO/swarm/REVIEW-PACKET.md`, or anything under `$REPO/.ultramath/` (except this brief, as permitted). Only read `$REPO/swarm/Statements.lean`, `$REPO/swarm/Targets.lean`, `$REPO/RankTwoCertificate.lean`, `$REPO/README.md`, `$REPO/LIMITATIONS.md`, and this brief.

## Sources

Citations to Kac Ch. 4 / Bourbaki Ch. VI §1 are **from memory / secondary summary** (not re-verified against page scans in this VM); the reference structure (finite ⇔ positive definite, affine ⇔ semidefinite corank 1, indefinite ⇔ indefinite) is standard and recalled. The computational evidence (`titsForm (1,0)=2b`, `titsForm (a,2)=-2a(ab-4)`, `det=ab(4-ab)`) was **verified** by explicit expansion in `python3/sympy` and by unfolding the Lean definition `titsForm a b x y = 2*b*x^2 -2*(a*b)*x*y +2*a*y^2` (matrix `diag(b,a)*cartan`).

## Repository modification

Confirmed: **did not modify `$REPO`**; no files written outside `~/.ultramath/smwbhzsg5/m1/` (this directory).
