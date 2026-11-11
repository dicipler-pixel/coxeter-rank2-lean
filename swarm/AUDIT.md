# Independent audit of the twelve statements

An audit of `swarm/Statements.lean` — and of the README/LIMITATIONS sentences that describe it —
against the standard mathematics, by readers who did not write the statements and who did not see
the proofs or the author's review.

## 1. What this audit is, and how much independence it has

- **Independent of the author.** Three passes were run; the readers were
  `mistralai/mistral-large-4-0` (passes 1 and 2) and `deepseek/deepseek-v4.1-flash` (pass 3), never
  the `moonshotai/kimi-k3.1-pro` that wrote the proofs. They were given the statements, the
  definitions and the prose, and told not to open the proofs, the accepted submissions, this file,
  or anything under `.ultramath/` — the last because earlier reports contain the answers.
- **The shape that worked.** Pass 1 briefed six members on all twelve: five produced nothing,
  having spent the run contending over who covered what (317 duplicate direction registrations),
  and one delivered. Pass 2 partitioned four members into disjoint triples: three produced nothing,
  one delivered. Pass 3 ran **one member per statement, twelve separate swarms**: all twelve
  delivered, with no contention at all, because a one-member swarm has no board to fight over.
- **Readings per statement.** Statements 1–3 have three independent readings each (passes 1, 2
  and 3); statements 4–14 have two (passes 1 and 3, or 1 and 4 for the two added later). The
  single-reading gap this file recorded after pass 1 is closed for all fourteen.
- **Not referees.** These are language models. Nothing below is recorded as *verified* because an
  auditor said it: it is verified because it was computed here, quoted from a fetched source, or
  checked against the definitions. Where a citation was not checked, it is not repeated as fact.

## 2. Machine-checked anchors

**The objects are Mathlib's objects.** `cartan` equals, at specific `(a,b)`, the Cartan matrices
Mathlib curates from Bourbaki's plates (`Mathlib/LinearAlgebra/Matrix/Cartan.lean`); these compile
by `decide`:

```
cartan 1 1 = CartanMatrix.A 2          -- A₂
cartan 1 2 = CartanMatrix.C 2          -- C₂
cartan 2 1 = CartanMatrix.B 2          -- B₂
cartan 3 1 = CartanMatrix.G₂           -- Bourbaki's orientation
cartan 1 3 = (CartanMatrix.G₂).transpose
```

So the two representatives at `ab = 2` are B₂ and C₂ — one Coxeter group, dual Cartan
matrices — which is why "one representative per product" was a real gap.

**A transposition convention, checked.** The reflection pair of `RankTwoCertificate` satisfies
`s_i(α_j) = α_j − a_ji α_i` for `cartan b a`, not `cartan a b`:
`s1 a (α₂) = (a,1) = α₂ + a α₁` gives `a₂₁ = −a`, and `s2 b (α₁) = (1,b)` gives `a₁₂ = −b`. Nothing in the twelve is affected —
every statement depends on `a*b` alone, and `titsForm a b x y = titsForm b a y x` — but the two
writings are now distinguished in the `cartan` docstrings rather than left to a reader.

**The statements are kernel-checked** and CI-green on the pinned toolchain (`466c1c8`, `57bd938`,
`5e8b72d`, `9a780b6`). This audit is about what they *say*.

## 3. One table behind all twelve

Two reflections whose product has order `N` have Cartan product `a*b = 4cos²(π/N)`:

| N | 2 | 3 | 4 | 5 | 6 | ∞ |
|---|---|---|---|---|---|---|
| 4cos²(π/N) | 0 | 1 | 2 | (3+√5)/2 | 3 | 4 |
| statement | degenerate | period 3 | period 4 | *not integral* | period 6 | affine |

For integers `a, b ≥ 1`: `ab ≤ 3` ⟺ `ab < 4` ⟺ `det(cartan a b) > 0` ⟺ finite type. The table
explains the hypotheses rather than decorating them — `ab = 0` is excluded because the *geometric*
`ab = 0` pair is the commuting one (`a = b = 0`, `N = 2`, where the step is the negation, period 2),
while `a = 0, b ≠ 0` is realised by no real angle. That is what `zero_product_no_positive_period`
shows has infinite order.

## 4. The literature, quoted

- **Kac's criterion.** Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* (Oregon),
  Theorem 4.2.4, fetched and quoted: "Let A be an indecomposable GCM. Then: (i) A has finite type
  if and only if all its principal minors have positive determinant. (ii) A has affine type if and
  only if det A = 0 and all proper principal minors have positive determinant. (iii) A has
  indefinite type if and only if neither of the above conditions holds."
- **The rank-two trichotomy.** Andersen, Carbone, Penta, *Kac–Moody Fibonacci sequences…*, §1,
  fetched and quoted: for `a, b > 0` with `ab ≥ 4`, "When ab = 4, A is positive semi-definite but
  not positive definite, and we call A affine. When ab > 4, A is neither positive semi-definite nor
  positive definite, but every proper generalized Cartan submatrix is positive definite."
- **What that means here.** When the audit ran, the library proved positive definiteness for
  `ab ≤ 3` with `a, b ≥ 1`, vanishing at `(a,2)` at `ab = 4`, and negativity there above — the
  witness half of the trichotomy, with psd and indefiniteness disclaimed in `LIMITATIONS.md`. The
  readers called that out as the gap worth closing, so it was closed: `tits_semidefinite_at_four`
  and `tits_indefinite_above_four` were added afterwards (§5a), and the disclaimer in
  `LIMITATIONS.md` was replaced by what is now proved and what still is not.

## 5. Verdicts

Every statement was judged true as stated and non-vacuous, with its hypotheses live — and in
several cases *tighter than needed*. The qualifications, each now reflected in the text where it
belongs:

| # | Statement | Readings | Verdict | Qualification |
|---|---|---|---|---|
| 1 | `cartan_det` | 3 | matches | an identity for all `a, b ∈ ℤ`; `det > 0` alone does not decide finiteness |
| 2 | `finite_exact_period` | 3 | matches | five pairs, not six; one antecedent live per pair; faithfulness is **not** needed for this conclusion (the hom argument), only for transferring it to the group |
| 3 | `affine_unipotent` | 3 | matches | unipotence only — non-identity and infinite order are the sibling statements; the pairs are A₁^(1) and the twisted A₂^(2) with its transpose |
| 4 | `affine_iterate` | 2 | matches | sharp: `n = 2` is statement 3, so the pair is not redundant — `n = 2` gives unipotence, the induction gives drift |
| 5 | `affine_no_positive_period` | 2 | matches | pointwise at `(1,0)`, strictly stronger than "not the identity"; a "no periodic point" reading is false — the step fixes `y = (b/2)x` |
| 6 | `zero_product_iterate` | 2 | matches (doc fixed) | true for every `b`; the docstring's "shear" was vacuous at `b = 0` |
| 7 | `zero_product_no_positive_period` | 2 | matches | `b ≠ 0` necessary (`b = 0` is the negation, period 2); witness `(1,0)` necessary — `T²` fixes the line `x = 0`; the case is a negative control, not Coxeter data |
| 8 | `zero_partner_no_positive_period` | 2 | matches | `a ≠ 0` exactly necessary; witness `(0,1)` exactly necessary — `(1,0)` is 2-periodic for every `a` |
| 9 | `tits_positive_definite` | 2 | matches | hypotheses sharp; **excludes `(0,0)`**, where the form is identically zero — the README was wrong here |
| 10 | `tits_vanishes_at_four` | 2 | weaker than the standard fact | proves isotropy at `(a,2)`; the *raw* form vanishes there too, so it does not distinguish the symmetrisation. Closed afterwards by `tits_semidefinite_at_four` (§5a) |
| 11 | `tits_negative_above_four` | 2 | weaker than the standard fact | one negative value, not indefiniteness. Closed afterwards by `tits_indefinite_above_four` (§5a) |
| 12 | `golden_product_eq_four_cos_sq` | 2 | matches | arithmetic only; the `H₂` identification is context, and `LIMITATIONS.md` says so |

## 5a. Closing the gap the readers flagged

Two statements were added after the audit, written and proved by the coordinator and gated by
`scripts/gate.py` (parity, compile, kernel replay, axioms, false controls). Because they had no
independent reading, a fourth pass — one swarm per statement, on `meta/muse-spark-open`, a family
neither the author nor pass 3 used — read them. Both reported, and both readings are folded in
below; every statement in the library now has at least one independent reading.

| Statement | What it says | Why it was added |
|---|---|---|
| `tits_semidefinite_at_four` | at `a*b = 4`, `0 ≤ titsForm a b x y` for all `x, y` — with `tits_vanishes_at_four` this makes the form degenerate | the affine side of the trichotomy was a witness (`Q(a,2) = 0`) rather than a sign |
| `tits_indefinite_above_four` | above `a*b = 4` the form takes both signs, ∃ a positive and ∃ a negative value | indefiniteness was one negative value and an unstated `Q(1,0) = 2b > 0` |

What the fourth pass said:

- **`tits_semidefinite_at_four` — weaker than the standard fact.** True and correctly named: the
  name promises positive semidefiniteness and it delivers that. But "degenerate" in Kac's sense
  needs the radical, and the pair (13)+(10) entails degeneracy only through the standard lemma
  *PSD with an isotropic vector implies that vector is in the radical* (minimise `Q(v₀ + t w)` in
  `t`). True in any dimension, and a proof the library did not contain. The docstring's "together
  … makes it degenerate" was a correct informal corollary; `LIMITATIONS.md` disclosed the radical
  step, which the reader checked. **The missing piece was one line** — `B((a,2),(x,y)) = a·y·(4 − ab)`
  — and it is now proved: `tits_radical_at_four` establishes the radical membership and
  `tits_degenerate_at_four` states degeneracy in the standard form, `∃ v ≠ 0, ∀ w, B v w = 0`. The
  verdict on statement 13 stands as written; what it was missing has been added beside it rather
  than retrofitted into it.
- **`tits_indefinite_above_four` — matches.** And the reader drew the distinction I asked for more
  sharply than I had: "takes both signs" and "signature (1,1)" are *not* equivalent in general
  dimension — `x² − y²` on `ℝ³` is degenerate and takes both signs — but they coincide in rank two,
  because a real symmetric `2×2` form with `det = 0` is semidefinite. Since `det = ab(4 − ab) < 0`
  above the boundary, both signs force signature `(1,1)`, so the witnesses `(1,0)` and `(a,2)` do
  suffice for the standard claim, up to that elementary `2×2` lemma.

Both are one or two lines from what was already there: `2b·Q = (2bx − ab y)² + ab(4−ab)y²` gives
nonnegativity at `ab = 4`, and `Q(1,0) = 2b` supplies the positive value. `LIMITATIONS.md` now
states the two things still unproved — that `(a,2)` spans the radical of the bilinear form, and the
converses (positive definiteness forces `ab ≤ 3`, semidefiniteness forces `ab ≤ 4`).

## 6. What the audit changed in the repository

1. **A counting error.** "`a*b ≤ 3` leaves six pairs" (LIMITATIONS, module docstring, TASK, RESULT)
   — it leaves five: `(1,1), (1,2), (2,1), (1,3), (3,1)`.
2. **A false sentence in the README.** "The symmetrised Tits form is positive definite on the finite
   side" fails at `(a,b) = (0,0)` = A₁×A₁, where the symmetriser `diag(b,a)` degenerates and the
   form is identically zero — a pair the README itself lists as finite, with period 2. Now "for
   `a, b ≥ 1`", with the exception stated.
3. **Two docstrings claiming more than their statements.** "`(a,2)` spans the radical" and
   "degenerate at `a*b = 4`" — only vanishing is proved; both reworded to what is established.
4. **A vacuous clause.** "whose square is a shear" for the `a = 0` step fails at `b = 0`, where the
   step is the negation; the docstring now splits the cases.
5. **A convention now stated.** The reflection pair belongs to `cartan b a`, the transpose of the
   matrix the file names; `cartan`'s docstring says so in both copies.
6. **Stale cross-references.** Renumbering `LIMITATIONS.md` left `Statements.lean` pointing at the
   wrong bullets; it now names each bullet by content.
7. **A missing qualifier.** `cartan a b` is a generalised Cartan matrix in Kac's sense only for
   `a, b ≥ 0` with matched zeros; the determinant identity holds for all integers.
8. **A defect in the audit briefs themselves**, found by an auditor: they pointed at Humphreys §2.4
   for the dihedral material, which is "Some positive definite graphs"; the rank-two group is
   Ch. 1 §1.1.

## 7. What the twelve reads converged on

Four findings recurred across independent readers, which is why they are recorded rather than fixed
quietly:

- **The hypotheses are inert where the arithmetic forces them.** For statements 3, 4, 5 and 11,
  `ab = 4` or `4 < ab` over `ℕ` already forces `a, b ≥ 1`, and Lean's linter reports `ha` and `hb`
  unused. They are not wrong — they are what makes `cartan` a GCM with a positive symmetriser — but
  a reader should know they do no logical work.
- **The witness matters and is not arbitrary.** Statements 7 and 8 use opposite witnesses and
  swapping them would be false in both directions: `(1,0)` is 2-periodic under `step a 0` for every
  `a`, while `step 0 b` has `T²` fixing the line `x = 0`, so `(0,1)` is 2-periodic there. Each
  statement's witness is the one vector that cannot be fixed.
- **The twelve are the witness half of Kac's trichotomy.** Where the literature gives types and
  signatures, the library gives one negative value, one vanishing, one period. That is honest and
  labelled, and it is the natural next increment: indefiniteness is one line (`Q(1,0) = 2b > 0`
  alongside the negative vector), positive semidefiniteness at `ab = 4` is the discriminant.
- **The bare golden identity is weaker than its name suggests.** The missing link was computed by a
  reader but not stated: if the step had order 5 then `ab = 2 + 2cos(2π/5) = (3+√5)/2`, irrational,
  so no integral pair exists. That — not the identity — is "`H₂` is not crystallographic", and it is
  the better thirteenth statement.

## 8. Falsification, and a misreading worth keeping

Brute force over `a, b ≤ 6` and vectors in `[-4,4]²`, and the degenerate cases to `n ≤ 400`, found
no counterexample to the period table, positive definiteness, `Q(a,2) = 0` at `ab = 4`,
`Q(a,2) < 0` above, or the degenerate statements.

The sweep exposed a **misreading** an auditor then confirmed independently: each affine
representative fixes a line pointwise — `y = 2x` for `(1,4)`, `x = y` for `(2,2)`, `x = 2y` for
`(4,1)`, in general `y = (b/2)x` — so `affine_no_positive_period` must not be read as "every orbit
is infinite". It says no positive power is the identity, witnessed by `(1,0)` whose drift is
`(2,b) ≠ 0`. My own first sweep "found counterexamples" to the stronger claim I had invented, and my
first check of statement 5's iterate identity failed on a typing error of mine before it passed.

## 9. What is still not verified

- **Book-internal numbering.** Chapters and statements are verified; Kac's theorem number,
  Bourbaki's proposition numbers and one Humphreys section are marked unverified in the reports.
- **Whether the integral reflection model is faithful** to the Coxeter presentation. Nothing here
  proves it; `LIMITATIONS.md` says so. One reader sharpened this: faithfulness is not needed for
  statement 2's conclusion, only for reading it as an order in a Coxeter group.
- **Positive semidefiniteness at `ab = 4`, indefiniteness above, the `H₂` geometry**: asserted by
  the literature, not formalized here.
- **Freeze discipline.** Statements were edited after freezing five times, all recorded in
  [`FREEZE-LOG.md`](FREEZE-LOG.md) with before, after and reason: two syntax corrections, one
  rename, one split, one hold-and-restore. The split is the one a reviewer should look at — a
  conjunct was moved out of `tits_signature_at_four` because it was not provable in that proof,
  and came back later as its own theorem. Freezing is worth nothing if such moves are invisible.
- **An LLM audit is not a referee.** A human algebraist reading `swarm/Statements.lean` against Kac
  is still the standard this falls short of. No reviewer has been secured, and the agents in this
  repository cannot secure one: there is no outreach channel and the GitHub integration here cannot
  open issues or post reviews. What exists instead is [`REVIEW-PACKET.md`](REVIEW-PACKET.md) — the
  five definitions, the twelve statements, the source to check each against and one question per
  statement, sized for 30–45 minutes — with a verdict template in [`review/`](review/). When one
  arrives, this section and §1 change to say so.
