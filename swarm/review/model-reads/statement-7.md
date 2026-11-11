# Audit report — statement 7, `zero_product_no_positive_period`

Auditor: member `m1`. Statement audited: **only** number 7.

**Statement, verbatim from `swarm/Statements.lean`** (with its docstring):

```lean
/-- So for `b ≠ 0` no positive power is the identity, although `a*b = 0 < 4`. -/
theorem zero_product_no_positive_period (b : ℤ) (hb : b ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step 0 b) n (1, 0) ≠ (1, 0)
```

## Verdict

| statement | standard fact it appears to name | verdict | evidence | correction needed |
| :--- | :--- | :--- | :--- | :--- |
| 7 `zero_product_no_positive_period` | "For the degenerate product `a*b = 0` with a nonzero partner (`a = 0`, `b ≠ 0`), no positive power of the product `s₁s₂` is the identity; `a*b = 0 < 4`." The nearest literature fact is Kac's rank-two classification: for a rank-two generalised Cartan matrix with `a, b ≥ 1`, finite type ⟺ `a*b ≤ 3` ⟺ `det = 4 − a*b > 0`. The pair `(0, b)` with `b ≠ 0` is **not** a generalised Cartan matrix, so no literature theorem covers it. | **`matches`** — true, non-vacuous, both hypotheses necessary, name and docstring honest; the honest reading "`4 − a*b > 0` alone does not give finiteness" is correct *as a statement about arbitrary integral reflection pairs*. Qualified: the pair is outside the Cartan class, so this is a negative control / counterexample-shaped remark, not a classification statement. | Verbatim restatement proved in Lean 4 + Mathlib, no `sorry` (`check7.lean`: `#print axioms` = `[propext, Classical.choice, Quot.sound]`). Explicit computation (`arith7.py`): `step 0 b` has matrix `[[-1,0],[b,-1]] = −(I−N)`, `N = [[0,0],[b,0]]`, `N² = 0`, so `Tⁿ = (−1)ⁿ(I − nN)` and `Tⁿ(1,0) = ((−1)ⁿ, (−1)ⁿ⁺¹ n b)`, which equals `(1,0)` only if `n·b = 0`; for `b = 0` the product is `−id`, period 2. Generalised-Cartan conditions (C1)–(C3) (Kac; Tits) exclude `(0,b)`, `b ≠ 0`. | **None for the proposition.** Two documentation notes: (i) the docstring's "So" suggests it follows from statement 6, which supplies only the even iterates — the odd case (first coordinate flips to `−1`) is an extra one-line step; (ii) the statement's non-Cartan character should stay stated next to it (it is, in `Targets.lean`/`LIMITATIONS.md`), otherwise the remark can be misread as a defect of Kac's criterion. |

## 1. What it names, and what the literature actually has

The statement says: for the integral reflections `s₁(x,y) = (−x, y)` (this is `s1 0`) and
`s₂(x,y) = (x, bx − y)`, the product `T = s₁s₂` has no positive power equal to the identity,
and `a*b = 0` while `4 − a*b = 4 > 0`.

The literature fact in the neighbourhood is the rank-two case of Kac's finite/affine/indefinite
classification. A generalised Cartan matrix (GCM) is an integral matrix with
(C1) `a_ii = 2`, (C2) `a_ij ≤ 0` for `i ≠ j`, (C3) `a_ij = 0 ⟺ a_ji = 0`. For
`A = cartan a b = [[2,−a],[−b,2]]` with `a, b ≥ 1` we have `det A = 4 − a*b` and both proper
principal minors equal `2 > 0`; hence (Kac Ch. 4) `A` is of finite type iff `a*b ≤ 3`, of affine
type iff `a*b = 4`, and indefinite iff `a*b > 4`.

The pair in statement 7 is `(a, b) = (0, b)` with `b ≠ 0`. It violates (C3): `a₁₂ = 0` but
`a₂₁ = −b ≠ 0`. So `cartan 0 b` is not a GCM: there is no root system, no Weyl group and no
Kac–Moody algebra attached, and "the product of the two simple reflections" is not the Coxeter
element of anything. Inside the GCM class, `a*b = 0` forces `a = b = 0` by (C3), and that pair is
`A₁ × A₁`, whose product has **exact period 2** (verified in Lean, `zero_zero_exact_period_two`).
So there is no literature statement "at `a*b = 0` the product has no positive period"; the
symmetric product-0 pair is finite.

Conclusion on names: statement 7 has no literature source, which matches the brief's own table
("as 6: no source"). Its content is the arithmetic remark "`4 − a*b > 0` alone does not give
finiteness", and that remark is honest when "alone" is read as "as a numerical test on arbitrary
integral pairs `(a, b)`": `(0,0)` and `(0,1)` both have `4 − a*b = 4`, and one product has period
2 while the other has infinite order. It is *not* a correction to Kac's classification, because
`(0,b)` is outside the class to which the classification applies; the repository says so itself
(`Targets.lean` docstring on `cartan`, `LIMITATIONS.md`). The README's phrasing "has infinite
order on an explicit vector" is careful.

## 2. Hypotheses: missing, too strong, too weak?

* `hb : b ≠ 0` is **necessary**: at `b = 0`, `step 0 0 (x,y) = (−x,−y)`, so
  `iter (step 0 0) 2 (1,0) = (1,0)` (Lean `zero_zero_period_two`; exactly period 2,
  `zero_zero_exact_period_two`). Without `b ≠ 0` the proposition is false at `n = 2`.
* `hn : 0 < n` is **necessary**: `iter f 0 (1,0) = (1,0)`.
* **Sufficient and not too weak**: for every `b ≠ 0` and every `n > 0` the claim holds — proved for
  all integers `b`, with no sign condition.
* **Broader than a Coxeter reading**: `b` ranges over all nonzero integers, including `b < 0`
  (and `a = 0` is built into the term `step 0 b`). For `b < 0` the pair is again outside the
  Cartan class, and the proposition stays true, so this generality is harmless: it does not
  overclaim, it merely is not a statement about Cartan data.
* **Nothing missing**: no positivity hypothesis on `b` is needed for this claim, no explicit
  `a*b = 0` hypothesis is needed, and **no faithfulness hypothesis is needed**, because the claim
  is about a linear map on `ℤ × ℤ`, not about a group presentation. (Any transfer to a Coxeter
  group would need faithfulness, which the repository explicitly does not claim; statement 7 makes
  no such transfer.)

## 3. Carrier and quantifier order

Carrier `V = ℤ × ℤ`; the statement is `∀ b ≠ 0, ∀ n > 0` about the single orbit of the fixed
vector `(1,0)`. It is a genuinely universally quantified statement — no conjunction of
implications over cases, no finite case list. The single vector is a witness: if
`iter f n (1,0) ≠ (1,0)` then `fⁿ ≠ id`, so the statement delivers the map-level claim its
docstring makes ("no positive power is the identity"). That is formalised as
`no_universal_positive_period` in `check7.lean`:
`∀ n > 0, ¬ ∀ v : V, iter (step 0 b) n v = v`.

Strictly, one fixed vector that works for *all* `n` is more than the map statement needs (a
per-`n` witness would do), so it is a strengthening — but it is true here (the orbit is infinite),
so it is harmless, and it is the cheapest form available in this model.

The choice of witness is essential, and the statement is calibrated to it: `iter (step 0 b) 2 (0,y)
= (0,y)` for every `y` (Lean `y_axis_fixed_by_square`), so with the witness `(0,1)` the claim would
be false at `n = 2`. The statement is therefore genuinely a statement about the orbit of `(1,0)`,
not an illicit claim about all vectors — and that is exactly what "no positive power is the
identity" requires.

## 4. The definitions it uses

`step 0 b (x,y) = (−x, b·x − y)`, matrix `M = [[-1,0],[b,-1]] = −(I−N)` with
`N = [[0,0],[b,0]]`, `N² = 0`. Verifications (`arith7.py`): `trace M = −2`, `det M = 1`,
characteristic polynomial `(λ+1)²`; `Mⁿ = (−1)ⁿ(I − nN)` for all `n ≥ 1`, hence

`Mⁿ(1,0) = ((−1)ⁿ, (−1)ⁿ⁺¹·n·b)`,

so even iterates are `(1, −2kb)` (linear drift, `even_iterate` in `check7.lean`) and odd iterates
have first coordinate `−1` (`odd_iterate`). Consequently the map itself has infinite order for
`b ≠ 0`, not merely the one orbit.

Mechanism: `T = step 0 b` is **−unipotent**, `T² = I − 2N` is a nontrivial transvection. This is a
different mechanism from the affine statements (`a*b = 4`), where `T = I + N` is unipotent and
drifts linearly; statement 7 cannot be derived from statement 4's formula and does not claim to.

`HasExactPeriod` is **not** used, and correctly so: since no positive `n` is a universal period,
`HasExactPeriod (step 0 b) n` is false for every `n > 0` (Lean `no_exact_period`). The
universal-quantifier form used is the only correct form, which confirms the file's remark that
`HasExactPeriod` "is not claimed, and would be the wrong form here".

## 5. Vacuity

Not vacuous. The hypotheses are satisfiable and the conclusion non-trivial: `b = 1, n = 1` gives
`iter (step 0 1) 1 (1,0) = (−1,1) ≠ (1,0)`. The proof needs the parity/linear-drift computation,
not a rewriting of the hypothesis.

## 6. Name and docstring

The name promises no positive period; the proposition delivers it (via the witness), and in fact
the map has infinite order. The docstring "for `b ≠ 0` no positive power is the identity, although
`a*b = 0 < 4`" is accurate: `a = 0` gives `a*b = 0 < 4`, and no positive power is the identity.

Two documentation nits, neither a mathematical error:

* the "So" reads as if the statement follows from statement 6 (`zero_product_iterate`), which
  controls only the even iterates; the odd case — first coordinate flips to `−1` — is an extra
  one-line argument (`odd_iterate`), not covered by statement 6;
* statement 7 covers only the `a = 0` half of `LIMITATIONS.md`'s "`ab = 0` with a nonzero partner
  has infinite order"; the `b = 0` half is statement 8, which is outside this audit.

The README's "has infinite order on an explicit vector" is loose (a vector has an infinite orbit;
the map has infinite order) but not false — and I verified the map-level claim, so the sentence is
supported.

## 7. True but not what it says?

It is true, and it is true for the reason it states; the qualification is different. A reader who
takes the docstring's last clause as a remark about Cartan matrices would over-read it: within the
GCM class the determinant does decide, and the only GCM with `a*b = 0` is `(0,0) = A₁ × A₁`, whose
product has exact period 2. What statement 7 really establishes is that the *numerical* test
`4 − a*b > 0` has no content for a reflection pair that is not Cartan data — precisely the failure
mode that the hypotheses `1 ≤ a, 1 ≤ b` of the finite-side statements exclude. As a negative
control, kept next to — not in place of — the classification statements, and with its non-Cartan
status stated, it is defensible and worth keeping. The repository already states that status in
`Targets.lean` and `LIMITATIONS.md`.

## Blindness

Files I opened: `swarm/review/AUDIT-BRIEF.md`; `swarm/Statements.lean`; `swarm/Targets.lean`;
`RankTwoCertificate.lean`; `README.md`; `LIMITATIONS.md`; `lean-toolchain` (one line, to report
the pinned Lean version).

Files I did **not** open: `RankTwoClassification.lean`; `swarm/Classification.lean`;
`swarm/selftest/`; `swarm/submissions/`; `swarm/RESULT.md`; `swarm/AUDIT.md`;
`swarm/REVIEW-PACKET.md`; every other file under `swarm/review/`; and **anything under
`.ultramath/` other than my own directory `m1`** — I did not read any other member's report or
verdict. Directory listings showed some of those names; I did not open them. I audited no
statement other than number 7. No proof of the repository's own theorems was consulted.

For transparency about the concurrent edits noted below: I read `git diff` output for the three
allowed files `README.md`, `swarm/Statements.lean` and `swarm/Targets.lean`, after `git status`
showed them modified. I did **not** run `git diff` on, or read, `RankTwoClassification.lean`.

## Sources: verified vs from memory

**Verified this session** (searched/fetched):

* Generalised Cartan matrix conditions (C1) `a_ii = 2`, (C2) `a_ij ≤ 0` for `i ≠ j`,
  (C3) `a_ij = 0 ⟺ a_ji = 0`: arXiv:1810.05562 §2.1; J. Tits, "Groups and group functors
  attached to Kac–Moody data", §1, conditions (C1)–(C4), where dropping positive definiteness
  (C4) "the matrix is called a generalized Cartan matrix, or GCM" (checked in the PDF);
  SageMath `CartanMatrix` documentation (attributes the conditions to Kac).
* The Cartan-matrix conditions `a_ij = 0 ⟺ a_ji = 0`, `a_ij ≤ 0` integral, `det A ≠ 0` with all
  principal minors positive, and the affine variant (drop `det A ≠ 0`, require all *proper*
  principal minors positive): Bergvelt & ten Kroode, *Lectures on Kac–Moody algebras*, CWI
  Syllabus 30 (1992), `https://ir.cwi.nl/pub/12928`, §1.9 eq. (1.9.8) and §3.4 eq. (3.4.10)
  (checked in the PDF; note this is a CWI syllabus volume, **not** Kac's book — I first assumed
  otherwise and corrected it).
* Rank two: Tits, same paper, §3, "In rank 2, there are two GCM of affine type, one standard
  `[[2,−2],[−2,2]]` and one twisted `[[2,−2],[−4,2]]`" — so in the affine class `a, b ≥ 1` and
  `a*b = 4`. The split finite/affine/indefinite at `a*b ≤ 3` / `= 4` / `> 4` for `[[2,−a],[−b,2]]`
  is stated in Forte, *The Automorphic Universe* (PhD thesis, Napoli), §2.2.2 (secondary source);
  I also checked the `2×2` case directly (det `= 4 − a*b`, proper principal minors `= 2 > 0`).
* `a_ij·a_ji = 4cos²(π/m_ij) ∈ {0,1,2,3}` for the Cartan matrix of a root system: MIT 18.745
  Lecture 23, Prop. 23.4 (following Bourbaki Ch. VI).

**From memory, numbering only, not verified in a copy of the book**: Kac, *Infinite-Dimensional
Lie Algebras*, 3rd ed., Ch. 4 "A classification of generalized Cartan matrices", Theorem 4.3 and
Table Aff 1; Bourbaki, Ch. IV §1 no. 2 and Ch. VI §1; Humphreys, Ch. 1 §1.1 and Ch. 6 §6.4.
Nothing in the verdict depends on this numbering: the verdict rests on the Lean proof and the
elementary `2×2` computation.

**Local, reproducible evidence**:

* `check7.lean` — `V`, `s1`, `s2`, `step`, `iter` copied verbatim from `RankTwoCertificate.lean`
  (textually identical, compared by string match) plus the statement verbatim; `lean check7.lean`
  exits 0, and `#print axioms zero_product_no_positive_period` reports
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`. Environment: Lean
  4.33.1 with the VM's Mathlib; the repository pins `leanprover/lean4:v4.33.0` (one patch below).
  Besides the target, the file proves: `no_universal_positive_period` (map-level: no positive `n`
  is a universal period), `no_exact_period` (`HasExactPeriod (step 0 b) n` is false for `n > 0`),
  `even_iterate` / `odd_iterate` (the parity formulas), `zero_zero_period_two` and
  `zero_zero_exact_period_two` (`b = 0` gives exact period 2, so the hypothesis is needed), and
  `y_axis_fixed_by_square` (`(0,y)` would be the wrong witness).
* `arith7.py` — the matrix, `Mⁿ = (−1)ⁿ(I − nN)` for `n ≤ 49`, the parity formulas for `k ≤ 39`,
  the map-level order check, brute force over `1 ≤ |b| ≤ 40, 1 ≤ n ≤ 200` (no counterexample), and
  the two hypothesis checks.

## Repository unchanged

I modified no repository file. Every shell command ran in `.ultramath/smwbdn3mz/m1/`, and my only
writes are there (`audit-report.md`, `check7.lean`, `arith7.py`, `.scratch/`).

Concurrency note, since it bears on reproducibility: at my first check (≈ 00:29 VM time)
`git status --short` and `git diff --stat` printed nothing. At the final check four tracked files
showed modifications — `README.md`, `RankTwoClassification.lean`, `swarm/Statements.lean`,
`swarm/Targets.lean`, mtimes 00:30–00:32 — which are **not mine**: the tree is being edited
concurrently by someone else while I audit. Statement 7 is unaffected: I re-read
`swarm/Statements.lean` and re-ran the string comparison at the end of the audit — its statement
text is byte-for-byte what `check7.lean` proves, and its docstring is unchanged. `git diff --
swarm/Statements.lean` touches only the module docstring's T5 bullet and statement 6's docstring;
`Targets.lean` gains a note on the `s1/s2`-versus-`cartan` transpose convention (which does not
affect `step 0 b`); the README edit adds a caveat about `(0,0)` to the Tits-form sentence and
leaves the sentence I quote unchanged.
