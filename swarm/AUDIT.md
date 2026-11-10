# Independent audit of the twelve statements

An audit of `swarm/Statements.lean` — and of the README/LIMITATIONS sentences that describe it —
against the standard mathematics, by readers who did not write the statements and who did not see
the proofs or the author's review.

## 1. What this audit is, and what it is not

- **Independent of the author.** The auditors ran `mistralai/mistral-large-4-0`, a different
  model family from the `moonshotai/kimi-k3.1-pro` that wrote the proofs, at max reasoning. They
  were given the statements, the definitions they use, and the prose, and were told not to open
  `RankTwoClassification.lean`, `swarm/submissions/`, `swarm/RESULT.md` or `.ultramath/`. Each
  report states whether it complied.
- **How many readers actually reported.** Two passes, **two** reports. First pass: six members on
  the whole set, five produced nothing (317 duplicate direction registrations — they spent the run
  contending over who covered which statements), and **m5** delivered a full twelve-statement
  audit. Second pass: four members on pre-assigned disjoint triples, three (m2, m3, m4) ended
  without writing anything and **m1** delivered an audit of statements 1–3. So statements 1–3 have
  two independent readings, statements 4–12 have one, and everything below was additionally
  checked by machine (§2, §3) or against a fetched source (§4). That is the extent of the
  independence, and this file does not claim more.
- **Not referees.** These are language models. Nothing below is recorded as *verified* because an
  auditor said it; it is verified because it was checked by machine here, or quoted from a source
  fetched here. Citations that could not be checked are labelled.

## 2. Machine-checked anchors

**The objects are Mathlib's objects.** `cartan` equals, at specific `(a,b)`, the Cartan matrices
Mathlib curates from Bourbaki's plates (`Mathlib/LinearAlgebra/Matrix/Cartan.lean`). These compile
by `decide`:

```
cartan 1 1 = CartanMatrix.A 2          -- A₂
cartan 1 2 = CartanMatrix.C 2          -- C₂
cartan 2 1 = CartanMatrix.B 2          -- B₂
cartan 3 1 = CartanMatrix.G₂           -- Bourbaki's orientation
cartan 1 3 = (CartanMatrix.G₂).transpose
```

So the two representatives at `ab = 2` are B₂ and C₂ — one Coxeter group, dual Cartan matrices —
which is why "one representative per product" was a real gap. Mathlib's
`LinearAlgebra/RootSystem/CartanMatrix.lean` also proves that a root-system Cartan matrix admits a
positive-diagonal symmetrization that is `Matrix.PosDef`, the general fact that
`tits_positive_definite` is the integral rank-two instance of.

**The model is the standard reflection action.** m5's observation, checked: `s1 a (0,1) = (a,1)`
is `α₂ + a α₁`, i.e. `α₂ - a₁₂ α₁` — exactly `s_i(α_j) = α_j - a_ij α_i` on the root lattice
`ℤα₁ ⊕ ℤα₂`. So `step = s₁ ∘ s₂` is the Coxeter element acting on the root lattice, not an
invented toy.

**The statements themselves are kernel-checked** and CI-green on the pinned toolchain
(`466c1c8`, run 5). This audit is about what they *say*; that is about whether they are proved.

## 3. One table behind all twelve

Two reflections whose product has order `N` have Cartan product `a*b = 4cos²(π/N)`:

| N | 2 | 3 | 4 | 5 | 6 | ∞ |
|---|---|---|---|---|---|---|
| 4cos²(π/N) | 0 | 1 | 2 | (3+√5)/2 | 3 | 4 |
| statement | degenerate | period 3 | period 4 | *not integral* | period 6 | affine |

For integers `a, b ≥ 1`: `ab ≤ 3` ⟺ `ab < 4` ⟺ `det(cartan a b) > 0` ⟺ finite type. The table
explains the hypotheses rather than decorating them — `ab = 0` is excluded because the *geometric*
`ab = 0` pair is the commuting one (`a = b = 0`, `N = 2`, and there `step 0 0` is the negation,
period 2), while `a = 0, b ≠ 0` is realised by no real angle. That is exactly what
`zero_product_no_positive_period` shows has infinite order.

## 4. The literature, quoted

- **Kac's criterion.** Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* (Oregon),
  Theorem 4.2.4, fetched and quoted: "Let A be an indecomposable GCM. Then: (i) A has finite type
  if and only if all its principal minors have positive determinant. (ii) A has affine type if and
  only if det A = 0 and all proper principal minors have positive determinant. (iii) A has
  indefinite type if and only if neither of the above conditions holds." This is Kac's
  classification (Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4); the theorem number differs
  between editions and between notes that restate it, so it is cited here at chapter level with
  the statement quoted.
- **The rank-two trichotomy and the affine case.** Andersen, Carbone, Penta, *Kac–Moody Fibonacci
  sequences, hyperbolic golden ratios, and real quadratic fields*, §1, fetched and quoted: for
  rank-two `A = (−a,−b)` with `a, b > 0`, `ab ≥ 4`, "When ab = 4, A is positive semi-definite but
  not positive definite, and we call A affine. When ab > 4, A is neither positive semi-definite
  nor positive definite, but every proper generalized Cartan submatrix is positive definite, and A
  is hyperbolic."
- **What that means for this library.** The literature asserts positive semidefiniteness at
  `ab = 4` and indefiniteness above. The library proves positive definiteness for `ab ≤ 3`,
  vanishing at `(a,2)` at `ab = 4`, and negativity at `(a,2)` above — not psd, not indefinite.
  `LIMITATIONS.md` says so. The gap is a gap, correctly labelled, not a misreading.

## 5. Verdicts

All twelve were judged **true as stated, non-vacuous, with the hypotheses as stated being the
right ones**, by the independent pass; the second pass is recorded below. The substantive
qualifications, each of which the text now reflects:

| # | Statement | Reading | Qualification |
|---|---|---|---|
| 1 | `cartan_det` | determinant of the rank-two GCM | true for all `a,b ∈ ℤ`; `det > 0` does not by itself decide finiteness (`ab = 0`, non-GCM) |
| 2 | `finite_exact_period` | in `I₂(m)` the product of the simple reflections has exact order `m`; crystallographic `ab = 4cos²(π/m)` | five pairs, not six; for each pair two of the three implications have false antecedents, so the conjunction is one live claim — worth saying in the docstring |
| 3 | `affine_unipotent` | `ab = 4` is affine type, charpoly `(λ−1)²`, the element acts unipotently | unipotence of the *map on ℤ×ℤ*, not of a group element |
| 4 | `affine_iterate` | `(T−1)² = 0 ⟹ Tⁿ = I + n(T−I)` | none |
| 5 | `affine_no_positive_period` | affine rank-two element has infinite order | a single witness suffices to rule out `Tⁿ = id`; it does **not** say every orbit is infinite (see §6) |
| 6 | `zero_product_iterate` | `a = 0`: the step is `(x,y) ↦ (−x, bx−y)`, square a shear | `[[2,0],[−b,2]]` with `b ≠ 0` is not a GCM; not claimed to be |
| 7 | `zero_product_no_positive_period` | so `4 − ab > 0` alone does not give finiteness | `b ≠ 0` is necessary: `step 0 0` is the negation, period 2 |
| 8 | `zero_partner_no_positive_period` | mirror of 7 | same |
| 9 | `tits_positive_definite` | symmetrisable GCM of finite type has a positive definite invariant form | hypotheses right: `2b > 0` is the leading minor, `ab ≤ 3` ⟺ `0 < ab < 4` |
| 10 | `tits_vanishes_at_four` | the form is degenerate at `ab = 4`; `(a,2)` is a radical vector | proves vanishing only — radical membership is true (`B((a,2),(x,y)) = a y (4−ab)`) but is not formalized |
| 11 | `tits_negative_above_four` | indefinite type above `ab = 4` | proves negativity at one vector, not indefiniteness |
| 12 | `golden_product_eq_four_cos_sq` | `4cos²(π/5) = (3+√5)/2`, hence `H₂` is not crystallographic | the arithmetic is proved; the `H₂` and Cartan-product identification is context, not formalized |

## 5a. What the second pass added

m1 audited statements 1–3 (`cartan_det`, `finite_exact_period`, `affine_unipotent`) and returned
**matches** on all three, independently of m5: it verified the charpoly and Cayley–Hamilton by
sympy for symbolic `a, b`, checked `Mⁿ = I` for `n = 3, 4, 6` on all five pairs with a witness
against every smaller power, and `(M − I)² = 0` for the three affine representatives. It also
checked prose that no one else had: the five-pair count, the README's result-2 periods
`2, 3, 4, 6` for `(0,0), (1,1), (1,2), (1,3)`, and the badge arithmetic `56 = 22 + 22 + 12`.

It found two further defects, both fixed:

- **Stale cross-references.** Rewriting `LIMITATIONS.md` renumbered its bullets, and
  `swarm/Statements.lean` still pointed at "bullet 2" and "bullet 3" for what are now bullets 3
  and 4. Numbers rot; the docstring now names the bullet by its content instead.
- **A claim needing a qualifier.** `cartan a b` is a generalised Cartan matrix in Kac's sense
  (`a_ij ≤ 0`, `a_ij = 0 ⟺ a_ji = 0`) only for `a, b ≥ 0` with matched zeros; the determinant
  identity holds for all `a, b : ℤ`. The docstring in `swarm/Targets.lean` and
  `RankTwoClassification.lean` now says which is which.

One timing caveat, recorded for accuracy: m1 read `swarm/Targets.lean` before the docstring
correction in §6.2 landed, so its remark that the `titsForm` docstring "is also correct" refers to
the pre-correction text. Its mathematics is right — the old sentence was true — but the point of
the correction is that positive semidefiniteness at `ab = 4` and indefiniteness above are true and
*not proved*, which is a different claim from true.

Contention was the failure mode in both passes: pre-assigning triples did not stop the board
refusing 167 registrations, and three members burned their run. If this is repeated, the shape
that works is one member per statement with the report as the only deliverable.

## 6. What the audit changed in the repository

1. **A counting error in published text.** `LIMITATIONS.md`, the `RankTwoClassification` module
   docstring, `swarm/TASK.md` and `swarm/RESULT.md` said `a*b ≤ 3` "leaves six pairs". It leaves
   **five**: `(1,1), (1,2), (2,1), (1,3), (3,1)` — `TASK.md` listed five while saying six. Found
   by the auditor, verified here by enumeration, fixed everywhere.
2. **Two docstrings claiming more than the statement carries.** "`(a,2)` spans the radical" (it
   is a zero of the form; radical membership is unproved) and "has no period at all" (the form of
   the claim is "no positive power is the identity"). Both reworded in `swarm/Statements.lean` and
   `swarm/Targets.lean`.
3. **A naming-convention note in the README.** Mathlib's `CoxeterMatrix.I m` has off-diagonal
   entry `m + 2`, so it is `I₂(m+2)` in this notation; Humphreys' `I₂(m)` has order `2m` and the
   conventions differ by 2. Without the note, a reader comparing the two sources sees a
   contradiction that is not there.
4. **A defect in the audit brief itself**, found and reported by the auditor: the brief pointed at
   Humphreys §2.4 for the dihedral material; that is "Some positive definite graphs", and the
   rank-two group is in Ch. 1 §1.1. Recorded so the next audit brief does not repeat it.

## 7. Falsification, and a misreading worth keeping

Brute force over `a, b ≤ 6` and vectors in `[-4,4]²`, and the degenerate cases to `n ≤ 400`, found
no counterexample to the period table, positive definiteness, `Q(a,2) = 0` at `ab = 4`,
`Q(a,2) < 0` above, or the degenerate statements.

The sweep did expose a **misreading**: each affine representative fixes a line pointwise —
`y = 2x` for `(1,4)`, `x = y` for `(2,2)`, `x = 2y` for `(4,1)`, since `T(v) − v = (2x−y)(1,2)` —
so `affine_no_positive_period` must not be read as "every orbit is infinite". It says no positive
power is the identity, witnessed by `(1,0)` whose drift is `(2,b) ≠ 0`, and the docstring says
exactly that. My own first sweep "found counterexamples" to the stronger claim I had invented.

## 8. What is still not verified

- Book-internal numbering (Kac's theorem number, Bourbaki's proposition numbers, Humphreys'
  section for a specific lemma). Chapters and statements are verified; numbers inside books are
  marked as unverified in the auditors' reports.
- Whether the integral reflection model is faithful to the Coxeter presentation. Nothing here
  proves it, and `LIMITATIONS.md` says so.
- Positive semidefiniteness at `ab = 4`, indefiniteness above, and the `H₂` geometry: asserted by
  the literature, not formalized here.
- Statements 4–12 have one independent reading, not two (§1).
- An LLM audit is not a referee. A human algebraist reading `swarm/Statements.lean` against Kac is
  still the standard this falls short of; it is a real independent reading, not the last word.

**How that gap closes, and how it does not.** No human reviewer has been secured, and the agents
working in this repository cannot secure one: there is no outreach channel, no way to engage or
pay a reviewer, and the GitHub integration here cannot open issues or post reviews to recruit one.
What has been prepared instead is [`REVIEW-PACKET.md`](REVIEW-PACKET.md): the five definitions, the
twelve statements, the specific source to check each against, the one question to answer per
statement, and what not to bother with — sized for about 30–45 minutes of an algebraist's time.
A reviewer's answers go in [`review/`](review/) using [`review/TEMPLATE.md`](review/TEMPLATE.md),
and when one arrives this section and §1 change to say so. Until then the honest description is:
machine-checked proofs, machine-checked meaning, two model readings on three statements and one on
the other nine.
