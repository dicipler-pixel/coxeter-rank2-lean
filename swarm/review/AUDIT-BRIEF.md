# Audit brief: one Lean statement, checked against the literature

You are auditing **one** statement of a Lean 4 library. You did not write it, and you are not
proving it. The question is whether the proposition says the standard mathematical fact its name
and docstring claim, under the hypotheses written.

Repository: `/workspace/nucleus/work/projects/p-870b05c7d9a34cc6a7491c6863177ba6/repo` (`$REPO`).

## What you may read

- `$REPO/swarm/Statements.lean` — the twelve statements, bodies `sorry`. Your statement is in here.
- `$REPO/swarm/Targets.lean` — `cartan` and `titsForm`.
- `$REPO/RankTwoCertificate.lean` — the model: `V`, `s1`, `s2`, `step`, `iter`, `HasExactPeriod`.
- `$REPO/README.md`, `$REPO/LIMITATIONS.md` — the prose the repository publishes about them.
- this brief.

## What you must not read

These contain proofs, prior auditors' verdicts, or framing that would bias your reading:

`$REPO/RankTwoClassification.lean`, `$REPO/swarm/Classification.lean`, `$REPO/swarm/selftest/`,
`$REPO/swarm/submissions/`, `$REPO/swarm/RESULT.md`, `$REPO/swarm/AUDIT.md`,
`$REPO/swarm/REVIEW-PACKET.md`, `$REPO/swarm/review/` (except this file), and **anything under
`$REPO/.ultramath/`** including other auditors' reports.

If you read one of them anyway, say so plainly in your report. An honest report that admits it is
worth more than a concealed one.

## The definitions

`V = ℤ × ℤ`, and for integers `a b : ℤ`, on a vector `(x, y) : V`:

```lean
s1 a (x, y) = (-x + a*y, y)          -- simple reflection 1
s2 b (x, y) = ( x,     b*x - y)      -- simple reflection 2
step a b    = s1 a (s2 b v)          -- the product of the two reflections
iter f n    = f applied n times
HasExactPeriod f n  ⇔  (∀ x, iter f n x = x) ∧ ∀ m, 0 < m → m < n → ∃ x, iter f m x ≠ x
cartan a b  : Matrix (Fin 2) (Fin 2) ℤ  = !![2, -a; -b, 2]
titsForm a b x y : ℝ = 2*b*x^2 - 2*(a*b)*x*y + 2*a*y^2
```

`HasExactPeriod f n` is "the map `f` has exact period `n`" (universal period `n`, and no smaller
positive universal period). `titsForm` is the quadratic form of `diag(b,a) * cartan a b`.

## What to determine

1. The standard mathematical fact the statement appears to name.
2. Whether it matches that fact under the standard hypotheses. Look specifically at:
   - **hypotheses** — missing, too strong, or too weak? (`1 ≤ a, 1 ≤ b` appears often; is it needed,
     and is it enough?)
   - **carrier and quantifier order** — these are statements about a map on `ℤ × ℤ`, not about
     Coxeter groups; a conjunction of implications `a*b = 1 → …`, `a*b = 2 → …`, `a*b = 3 → …` is
     not a statement about all products.
   - **meaning of the definitions used** — is `cartan` a generalised Cartan matrix (in whose
     sense?); is `titsForm` the symmetrised invariant form or the raw quadratic form; is
     `HasExactPeriod` the right notion for a *map*, and does the statement need the action to be
     faithful?
   - **vacuity** — is it true for a trivial reason, so that it does not carry the content its name
     suggests?
   - **name and docstring** — do they promise more than the proposition delivers?
3. A verdict: `matches` / `weaker than the standard fact` / `stronger` / `misleading as named or
   documented` / `false as stated`.
4. Evidence: a section-level citation (author, title, chapter/section/theorem or page) **or** an
   explicit computation. Write "not verified" whenever you are citing from memory.

## Sources, by statement number

| # | Statement | Read against |
|---|---|---|
| 1 | `cartan_det` | Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 (classification of generalised Cartan matrices); Bourbaki, *Lie Groups and Lie Algebras* Ch. VI §1 |
| 2 | `finite_exact_period` | Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 1 §1.1 (`I₂(m)`; the product of the two simple reflections is a rotation through `2π/m`) and Ch. 6 (finite and crystallographic groups, `m ∈ {2,3,4,6}`); Bourbaki Ch. IV §1 |
| 3 | `affine_unipotent` | Kac Ch. 4 (affine type: `det = 0`, proper principal minors `> 0`); Humphreys Ch. 6 §6.5 |
| 4 | `affine_iterate` | no independent source — check the implication from statement 3 |
| 5 | `affine_no_positive_period` | Bourbaki Ch. IV §1 no. 2 (`m = ∞`, infinite dihedral) |
| 6 | `zero_product_iterate` | no source: this pair is not a generalised Cartan matrix. Check the computation, and say whether including it is defensible |
| 7 | `zero_product_no_positive_period` | as 6, plus: is "`4 − ab > 0` alone does not give finiteness" the honest reading? |
| 8 | `zero_partner_no_positive_period` | mirror of 7 |
| 9 | `tits_positive_definite` | Kac Ch. 2 (invariant bilinear form) and Ch. 4 (finite type criterion) |
| 10 | `tits_vanishes_at_four` | Kac Ch. 4 (affine type) |
| 11 | `tits_negative_above_four` | Kac Ch. 4 (indefinite type) |
| 12 | `golden_product_eq_four_cos_sq` | trigonometry; the `H₂ = I₂(5)` context |
| 13 | `tits_semidefinite_at_four` | Kac Ch. 4 (affine type: positive semidefinite of corank 1); and what "degenerate" requires |
| 14 | `tits_indefinite_above_four` | Kac Ch. 4 (indefinite type: `∃v, (v|v) > 0` and `∃w, (w|w) < 0`) |

Mark clearly which citations you verified and which you recalled.

## Arithmetic

`python3` with `sympy` is available. Checking the arithmetic is expected and cheap: the `2×2`
matrix of `step a b` (columns are the images of `(1,0)` and `(0,1)`), its trace `a*b - 2` and
determinant `1`, its characteristic polynomial `λ² − (a*b − 2)λ + 1`, the value `titsForm a b a 2`,
powers of the matrix, orders of the map. A computation supports a verdict; it does not replace the
citation.

## Deliverable

One file `audit-report.md` in your own working directory, containing:

- a one-row table: statement | standard fact | verdict | evidence | correction needed;
- a short paragraph on anything true-but-not-what-it-says;
- an explicit line on blindness: which of the forbidden files you did or did not open;
- an explicit line on sources: verified vs from memory;
- confirmation that you did not modify the repository.

Do not modify `$REPO`. Do not audit any statement other than yours.
