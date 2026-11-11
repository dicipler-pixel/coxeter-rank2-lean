# Audit report — statement 10: `tits_vanishes_at_four`

Auditor: m1 (swarm `smwbdn3sj`). Scope: statement 10 only, as required by `swarm/review/AUDIT-BRIEF.md`.

## The statement audited

```lean
theorem tits_vanishes_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 = 0
```

with `titsForm a b x y = 2*b*x^2 - 2*(a*b)*x*y + 2*a*y^2` (`swarm/Targets.lean`). Writing
`A = cartan a b = [[2,-a],[-b,2]]` and `D = diag(b,a)`, one has `D*A = [[2b,-ab],[-ab,2a]]`, symmetric, so
`titsForm a b x y = (x,y)ᵀ (D A) (x,y)` is the quadratic form of the **symmetrised** (Kac invariant-form) Gram
matrix, with positive integer symmetriser `D` (`a,b ≥ 1`). It is not the raw form `xᵀAx`.

## Verdict table (one row)

| # | statement | standard fact it appears to name | verdict | evidence | correction needed |
|---|---|---|---|---|---|
| 10 | `tits_vanishes_at_four`: `a,b ≥ 1`, `a*b = 4` ⟹ `titsForm a b a 2 = 0` | Kac Ch. 4, **affine type**: the 2×2 GCM `[[2,-a],[-b,2]]` with `a,b ≥ 1` is affine exactly when `a*b = 4` (proper principal minors `2,2 > 0`, `det = 4-ab = 0`); then it has a positive null vector `θ = (a,2)` with `Aθ = 0`, `A` is positive semidefinite of rank 1, and the Tits form `q(x,y) = 2b x² - 2ab xy + 2a y²` is positive semidefinite with radical `ℝ·(a,2)` — the types being `A₁⁽¹⁾` at `(2,2)` and `A₂⁽²⁾` at `(4,1)`/`(1,4)` | **weaker than the standard fact** — true, non-vacuous, honestly named and documented, but it asserts a single point-evaluation of the affine sign/radical statement and nothing else | Kac, *Infinite-Dimensional Lie Algebras* (3rd ed., 1990), Ch. 4, **Thm 4.3, p. 48** (affine: `∃θ>0, Aθ=0`, `A` positive semidefinite, `rank = n-1`) — verified through two published restatements that quote it by theorem and page; Perrin, *Introduction to Kac–Moody groups and Lie algebras* (2015), §8.2, **Lemma 8.2.3, p. 66** (read in text): symmetric `A` is affine iff positive semidefinite of corank 1; own computation and Lean check: `q(a,2) = -2a(ab-4)` and, at `ab = 4`, `q(x,y) = (2/a)(2x-ay)²` | none for truth; to match the standard fact, strengthen the conclusion to PSD + radical (one line: `titsForm a b x y = 2/(a:ℝ) * (2*x - a*y)^2`, or the bilinear identity `B((a,2),(x,y)) = (a:ℝ)*y*(4-a*b)`); also soften the T5 summary bullet, `swarm/Statements.lean` line 22, "degenerate at `a*b = 4`", which the frozen statement does not establish (isotropic ≠ degenerate) |

## The statement is true: verified, not merely believed

* Identity, for all `a b : ℤ`: `titsForm a b a 2 = -2a(ab-4)`. At `ab = 4` this is `0`. With `a,b : ℕ`, `a*b = 4`
  leaves exactly `(1,4)`, `(2,2)`, `(4,1)`, and `(a:ℝ) = a ≠ 0` there, so `(a,2) ≠ 0`.
* Lean, in my own file [verify10.lean](verify10.lean) (definitions copied verbatim from `swarm/Targets.lean`;
  the repository is not imported and not modified), no `sorry`:
  `tits_vanishes_at_four` (verbatim), `titsForm_at_a_two` (`= -2a(ab-4)`), `hyps_redundant`
  (`a*b = 4` ⟹ `1 ≤ a ∧ 1 ≤ b`), `titsForm_square_at_four` (`ab = 4, a ≠ 0` ⟹ `q = (2/a)(2x-ay)²`),
  `polar_at_a_two` (`B((a,2),(x,y)) = a*y*(4-ab)`), `not_posDef_at_four` (the form is not positive definite
  at `ab = 4`). `#print axioms` on each: `propext, Classical.choice, Quot.sound` only.
* sympy: `q(a,2) = -2a(ab-4)`; `B((a,2),(x,y)) = a*y*(4-ab)`; at `ab=4`, `q = (2/a)(2x-ay)²` and the zero set is
  exactly the line `ℝ·(a,2)` — `2(2x-y)²` at `(1,4)`, `4(x-y)²` at `(2,2)`, `2(x-2y)²` at `(4,1)`.

## Hypotheses, carrier, quantifiers

* `ha : 1 ≤ a`, `hb : 1 ≤ b` are **redundant**: `a,b : ℕ` with `a*b = 4` already forces both (proved in Lean),
  the three pairs above being all the solutions. They are not too strong — no representative is lost — and they
  are exactly what one needs for `cartan a b` to be a generalised Cartan matrix in Kac's sense (C1–C3: diagonal
  `2`, off-diagonal `-a, -b ≤ 0`, zero off-diagonal only jointly) and for the symmetriser `D = diag(b,a)` to be
  positive, i.e. for `titsForm` to be a *positive* multiple of the invariant form. So: right hypotheses, no more
  than the framing needs.
* Quantifier shape is fine here: one universally quantified implication, so all three representatives at `ab = 4`
  are covered, with no case-split-conjunction defect (unlike the shape criticised in the brief for statement 2).
* The carrier is `ℝ²` and a quadratic form: this statement carries no group action, so questions of faithfulness
  or of `HasExactPeriod` do not arise. That is appropriate for a statement about a form, and it is the reason the
  statement needs none of the reflection model.
* `cartan a b` under `ab = 4, a,b ≥ 1` **is** an indecomposable GCM: `-a, -b ≤ 0`, both nonzero, symmetrisable by
  `diag(b,a)`. So the literature applies squarely to it.

## True, but not what it says — and what it does say

The name and both docstrings (`swarm/Statements.lean`, `swarm/Targets.lean`) are unusually honest: they say the
form vanishes at `(a,2)` at `a*b = 4`, record the exact identity `-2a(ab-4)`, and `Targets.lean` explicitly adds
that *"that `(a, 2)` spans the radical … and that the form is indefinite above are true but are **not**
formalized here"*; `LIMITATIONS.md` repeats the disclaimer. So the statement delivers exactly what it advertises
and is **not misleading as named or documented**, and it is **not vacuous** (three genuine instances). What is
thin is the mathematical content:

* What it establishes genuinely: the form is **isotropic** at `(a,2) ≠ 0` at `ab = 4`, hence **not positive
  definite** — i.e. the finite-type positive-definiteness (`A > 0 ⇔ a*b ≤ 3`, the finite side) *fails* at
  `ab = 4`. That is a true and relevant fragment of the finite/affine boundary.
* What it does **not** establish, though the affine-type theorem and the surrounding prose suggest it:
  * that the form is **positive semidefinite** (vanishing at one point is compatible with indefiniteness — e.g.
    `x² - y²` is isotropic at `(1,1)` and nondegenerate);
  * that `(a,2)` is in the **radical** of the bilinear form, or that the radical is one-dimensional;
  * that `det(cartan a b) = 4 - ab = 0`, or that `A·(a,2)ᵀ = 0` (i.e. that `(a,2)` is the null vector, Kac's
    `θ`), or that `rank A = 1`.
  Each of those is a one-line consequence of the same computation (proved in `verify10.lean`), yet none is stated.
* Two further signs of how little this evaluation tests: (i) because `a*b = 4` puts `(a,2)` in `ker A`, the **raw**
  form `xᵀAx = 2x² - (a+b)xy + 2y²` also vanishes at `(a,2)` there (`= -2(ab-4) = 0`) — so this particular value
  does not even pin down that `titsForm` is the symmetrised form rather than the raw one; (ii) `D = diag(b,a)` is
  only a positive integer multiple of the primitive symmetriser, so at `(2,2)` the form is `2×` the primitive
  normalisation — harmless for sign and zeros, but again invisible at a single point.
  Consequently the T5 summary in `Statements.lean` ("positive definite on the finite side, **degenerate** at
  `a*b = 4`, negative somewhere above it") describes the intended theorem, not this statement: from the frozen
  statement alone one gets isotropy, not degeneracy. `LIMITATIONS.md` already says so; the summary line does not.

## Suggested correction (if the library wants this to match Kac Ch. 4)

Replace the conclusion by the positive-semidefinite-plus-radical statement at `ab = 4`, e.g.

```lean
theorem tits_psd_radical_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) (x y : ℝ) :
    0 ≤ titsForm (a : ℤ) (b : ℤ) x y ∧
      (titsForm (a : ℤ) (b : ℤ) x y = 0 ↔ ∃ t : ℝ, x = t * (a : ℝ) ∧ y = 2 * t)
```

or the matrix form `(cartan a b) *ᵥ ![a, 2] = 0 ∧ (cartan a b).rank = 1`, equivalently
`titsForm a b x y = 2/(a:ℝ) * (2*x - (a:ℝ)*y)^2`. All ingredients are already proved in
[verify10.lean](verify10.lean); a submission would need them restated over the repository's own definitions.
If the statement is kept as is, it should be described in `Statements.lean` as an isotropic-vector lemma at
`a*b = 4` (the current per-statement docstring already says exactly that).

## Blindness

**Files I opened**: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`,
`RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. **Files I did not open**: `RankTwoClassification.lean`,
`swarm/Classification.lean`, `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`,
`swarm/REVIEW-PACKET.md`, everything under `swarm/review/` except the brief, and everything under
`.ultramath/` except my own directory `.ultramath/smwbdn3sj/m1/`. I ran `ls`/`fs_list` on the repository root,
which exposes file names only, and `git status --porcelain` (clean) to confirm I changed nothing.

## Sources: verified vs recalled

* **Verified by reading the text** (PDFs fetched and converted in this session):
  * N. Perrin, *Introduction to Kac–Moody groups and Lie algebras* (Bonn lecture notes, dated 9 Nov 2015), §8.2,
    **Lemma 8.2.3, p. 66**: "A symmetric matrix `A` is of finite (resp. affine) type if and only if `A` is
    positive definite (resp. positive semidefinite of corank 1)."
  * H. Nicolai, O. Schlotterer, *Infinite Dimensional Symmetries* (Saalburg lectures, 2009), §2.4, **Eq. (2.25)**:
    for the rank-two ansatz `[[2,-a],[-b,2]]`, `A > 0 ⇔ a·b ≤ 3`; and the rank-two affine examples with `a·b = 4`
    are `[[2,-2],[-2,2]]` and `[[2,-4],[-1,2]]`.
  * W. Cook, PhD thesis (Kent State), **Theorem 2.10**, labelled "Theorem 4.3 on page 48 of [16]" with
    `[16] = V. G. Kac, Infinite-dimensional Lie algebras, CUP, 3rd ed., 1990`: for an indecomposable GCM `C`,
    affine type means there is `θ ∈ ℤⁿ` with `θ > 0` and `Cθ = 0`, *and* `C` is positive semidefinite with
    `rank(C) = n-1`.
* **Quoted by a search excerpt only** (PDF itself not opened): Kac–Peterson, *Adv. Math.* 53 (1984) 125–264, §1.2
  ("affine iff all proper principal minors are positive and `det A = 0`") and §1.3 (the invariant form restricted
  to the real span of the simple roots is positive semidefinite with kernel `ℝδ`). Used only as corroboration.
* **From memory, not verified**: that Kac's Ch. 4 is entitled "A Classification of Generalized Cartan Matrices"
  and occupies pp. 47–58 (consistent with Thm 4.3 on p. 48 and with a publisher table-of-contents listing that
  Googling produced, but I did not open Kac's book); that the name `A₂⁽²⁾` attaches to `[[2,-4],[-1,2]]` and that
  `[[2,-1],[-4,2]]` is its dual in Kac's Table Aff 3 (only the matrices themselves, not their labels, are
  verified above). I did not have access to Kac's book and did not open it.
* **My own verification** (decisive for the mathematical content, independent of any citation): the algebraic
  identities and the Lean proofs listed above.

## Repository modification

**None.** All my writes — `audit-report.md`, `verify10.lean`, a temporary `.scratch/` with the fetched PDFs —
are inside `.ultramath/smwbdn3sj/m1/`, my assigned directory. `git status --porcelain` in the repository root is
empty (my directory is ignored by git), and I created, changed or deleted no other file in the repository.
