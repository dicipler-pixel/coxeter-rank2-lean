# Audit report — statement 12, `golden_product_eq_four_cos_sq`

Auditor: member m1 (swarm smwbdn3we). Audited statement, verbatim from `swarm/Statements.lean`
(T6 block, no docstring, no hypotheses):

```lean
theorem golden_product_eq_four_cos_sq :
    4 * Real.cos (Real.pi / 5) ^ 2 = (3 + Real.sqrt 5) / 2
```

Namespace `OperatorFirst.CoxeterRankTwo`; no `a`, `b`, `cartan`, `step`, `V` or `HasExactPeriod`
occurs in it — it is a closed equation between two real numbers.

## Table

| statement | standard fact | verdict | evidence | correction needed |
| :--- | :--- | :--- | :--- | :--- |
| `golden_product_eq_four_cos_sq : 4 * Real.cos (Real.pi/5)^2 = (3 + Real.sqrt 5)/2` | `cos(π/5) = (1+√5)/4 = φ/2` with `φ = (1+√5)/2` the golden ratio, so `4cos²(π/5) = (2cos(π/5))² = φ² = φ+1 = (3+√5)/2`. In the H₂ = I₂(5) context `(3+√5)/2 = 4cos²(π/5) = φ²` is the product of the two off-diagonal magnitudes of the H₂ Cartan matrix (`c₁₂ = −4cos²(π/m)`, or `−2cos(π/m)` each in the symmetric convention, at `m = 5`), i.e. the non-integral "golden" Cartan product that excludes `I₂(5)` from the crystallographic list. | **matches** | (i) Formally checked in the active Lean 4/Mathlib: `check12.lean` (this directory) proves the proposition verbatim; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. (ii) `sympy`: exact difference `0`; numerically both sides `2.618033988749894848204586834365638117720`. (iii) Literature: Wikipedia "Exact trigonometric values", table row `π/5 = 36°` (`cos = (√5+1)/4`) and §4.3 "18°, 36°, 54°, and 72°" ("`cos(36°) = (√5+1)/4 = φ/2`"); Wikipedia "Golden ratio" (`φ = 2cos(π/5) = 2cos 36°`, `φ² = φ+1`); Magma Handbook "Finite and Affine Coxeter Groups" (non-crystallographic finite types `I₂(m)`, `m = 5`; `CartanMatrix` convention `c_ij = −4cos²(π/m_ij)`, symmetric `−2cos(π/m_ij)`); Wikipedia "Coxeter group" (`H₂ ≅ I₂(5)`). All quoted in `evidence.md` with URLs. | None for truth: the equation is true, and it is exactly the arithmetic identity its name and the T6 comment in `Statements.lean` advertise. Optional (documentation, not correctness): name the standard fact in a docstring (`2cos(π/5) = (1+√5)/2`, `4cos²(π/5) = φ² = φ+1`) and, if the H₂ reading is wanted from the statement itself, state the model-level companion (`trace (step a b) = a*b − 2`, so order 5 forces `a*b = 2 + 2cos(2π/5) = 4cos²(π/5)`) — the repository currently leaves that link to prose. |

## True, but not what the rank-two framing suggests

The proposition is a bare real-number identity: no hypothesis, no `a b`, no `step`, no order 5, no
mention of a reflection or a Cartan matrix. This has consequences in both directions.

*It cannot be wrong about the classification* — there is nothing in it to be wrong about; the whole
of its content is the value of `cos(π/5)`. *It also cannot carry the classification content* that
the T6 comment and the README attach to it. The link runs through facts that are absent from the
statement: (a) in the standard Cartan-matrix convention for `I₂(m)` the two off-diagonal magnitudes
are `4cos²(π/m)` and `1` (Magma Handbook), or `2cos(π/m)` each in the symmetric convention, so for
`m = 5` the product is `4cos²(π/5) = (3+√5)/2`; (b) in this repository's own model, `step a b` is the
matrix `[[a*b−1, −a],[b, −1]]` with trace `a*b − 2` and determinant `1`, so an element of order 5
(rotation through `2π/5`) needs `a*b = 2 + 2cos(2π/5)`, which sympy confirms is the same number
`(√5−1)/2 + 2 = (3+√5)/2`. Since that number is irrational, no integer pair `(a, b)` realizes
`I₂(5)`, and `4 − a*b = (5−√5)/2 > 0`, so the associated form stays positive definite: H₂ is finite
but non-crystallographic. None of this is asserted or proved by statement 12. `LIMITATIONS.md` says
precisely this ("The golden product is proved to equal `4cos²(π/5)`. That this number is the Cartan
product of `I₂(5)`, and the full `H₂` geometry, are not formalized"), so the statement does not
over-claim *given its own documentation*; a reader who takes "golden product" to promise an equation
about the Cartan product `a*b` would find only its arithmetic half.

Second, minor: as an equation in `cos(π/5)` the statement fixes the cosine only up to sign
(`4cos²θ = X ⇔ |2cos θ| = √X`). Recovering the classical `2cos(π/5) = (1+√5)/2` uses
`0 < π/5 < π/2` and `√((3+√5)/2) = (1+√5)/2`. So the proposition is *equivalent* to the standard
value, not weaker, but the equivalence has that one-line sign step.

Nothing is vacuous here (no quantifier, no hypothesis; a concrete equation), nothing is stronger
than the standard fact, and there are no missing or superfluous hypotheses to add or drop — the
`1 ≤ a, 1 ≤ b` issues that matter for statements 2, 3, 5 and 9 simply do not arise. No coercions can
distort the meaning: `4`, `5`, `2` are `ℝ`-literals, and `/` is real division in both places.
`Real.pi` is Mathlib's usual π (twice the zero of `cos` in `[1,2]`, docstring "The number
π = 3.14159265..."), and `Real.cos` is the real part of `(e^{iz}+e^{−iz})/2`; `Real.sqrt` is the
nonnegative square root. Mathlib already contains the literature value it squares,
`Real.cos_pi_div_five : cos (π/5) = (1 + √5)/4`.

## Blindness

I opened **none** of the forbidden files: not `RankTwoClassification.lean`, not
`swarm/Classification.lean`, not `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`,
`swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, not anything else under `swarm/review/` besides
`AUDIT-BRIEF.md`, and nothing under `.ultramath/` except the files in my own directory
`.ultramath/smwbdn3we/m1/`. Files read: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`,
`swarm/Targets.lean`, `README.md`, `LIMITATIONS.md`, `RankTwoCertificate.lean` (grepped, to see the
`golden_product_between` / `golden_product_not_integer` context), and the installed Mathlib sources
under `/opt/mathlib`. I audited statement 12 only.

## Sources: verified vs from memory

* **Verified** (fetched and quoted, see `evidence.md` for URLs and raw-line references):
  Wikipedia "Exact trigonometric values" (π/5 row and §4.3); Wikipedia "Golden ratio"
  (`φ = 2cos(π/5)`, `φ² = φ+1`); Wikipedia "Coxeter group" (`H₂ ≅ I₂(5)`); Magma Handbook,
  "Finite and Affine Coxeter Groups" (non-crystallographic finite types; `c_ij = −4cos²(π/m_ij)`
  and symmetric `−2cos(π/m_ij)` conventions). Also verified locally: the Mathlib definitions of
  `Real.pi`, `Real.cos`, `Real.sqrt` and the lemma `Real.cos_pi_div_five`.
* **From memory, not verified**: Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 1 §1.1 and
  Ch. 2 §2.4 (for `I₂(m)` the product of the two simple reflections is a rotation through `2π/m`)
  and Ch. 6 (crystallographic `I₂(m)` forces `m ∈ {2,3,4,6}`). I did not open the book. The rotation
  statement is replaced, for the purposes of this report, by the explicit `2×2` trace computation in
  `evidence.md` §2; the crystallographic restriction is supported by the verified Magma quote.

## Repository integrity

I did not modify the repository. `git status --porcelain` and `git diff --stat` in `$REPO` are both
empty after this audit; my only writes are `audit-report.md`, `evidence.md`, `check12.lean` and
`.scratch/` inside `.ultramath/smwbdn3we/m1/`, which is (a) my own working directory and (b) matched
by `.gitignore` (`.ultramath/`).
