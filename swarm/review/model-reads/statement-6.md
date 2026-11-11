# Audit — statement 6, `zero_product_iterate`

Auditor: member `m1` (swarm `smwbdn3l1`), auditing only statement 6 of `swarm/Statements.lean`.
Repository read, never written. All my artefacts are in this directory.

Statement as frozen (`swarm/Statements.lean`, section T4, with its docstring):

```lean
/-- With `a = 0`, the Coxeter step is `(x, y) ↦ (-x, b*x - y)`, whose square is a shear. -/
theorem zero_product_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n) (x, y) = (x, y - 2 * (n : ℤ) * b * x)
```

## One-row table

| Statement | Standard fact it is named for | Verdict | Evidence | Correction needed |
|---|---|---|---|---|
| 6, `zero_product_iterate`, as quoted above | **None in the literature.** With `a = 0`, `b ≠ 0` the matrix `cartan 0 b = !![2, 0; -b, 2]` is *not* a generalized Cartan matrix in Kac's sense: `a₁₂ = 0` while `a₂₁ = -b ≠ 0`, violating axiom (C3) `a_ij = 0 ⟺ a_ji = 0` (Kleshchev, *Lectures on Infinite Dimensional Lie Algebras*, Def. 1.2.1 — **verified** against the fetched text; Kac, Ch. 4 §1, Def. 4.1 — **from memory**). So there is no Kac–Moody algebra, no Weyl group and no Coxeter element here whose iterate the statement could describe. The only standard content is elementary: `M² = I + N` with `N² = 0` gives `M^{2n} = I + nN`; equivalently `s₁ 0` and `s₂ b` are two involutions whose product has infinite order for `b ≠ 0`, so the group they generate is the infinite dihedral group (type `I₂(∞)`) — a group-theoretic reading the statement does not make and the library does not formalize. | **`misleading as named or documented`.** The proposition is TRUE, and it is not missing a hypothesis (none is needed; it is Lean-proved from `propext` alone). What is missing is the fact the name invokes: there is no Cartan/Coxeter statement for this pair, and the docstring's "whose square is a shear" is false at `b = 0`, which the statement's quantifiers include. (With that one docstring correction the honest label becomes `matches`: the proposition then says exactly the elementary computation it states, no more and no less.) | Computation: `step 0 b` is `M = [[-1,0],[b,-1]]`, `det = 1`, `trace = -2`, charpoly `(λ+1)²`; `M² = I + N`, `N = [[0,0],[-2b,0]]`, `N² = 0`, so `M^{2n} = I + nN = [[1,0],[-2nb,1]]`, i.e. `(x,y) ↦ (x, y - 2nbx)` — exactly the right-hand side (`arithmetic-check.log`, sympy, exact, `b ∈ [-20,20]`, `0 ≤ n ≤ 20`: 0 mismatches; also symbolic). Lean: `Check.lean` proves the verbatim statement, `#print axioms` = `[propext]`. | Documentation only: qualify "shear" with `b ≠ 0` (at `b = 0` the square is the identity — `step 0 0 = -1` has order 2); add one sentence that `(0,b)`, `b ≠ 0`, is not a generalized Cartan matrix (the docstring of `Targets.cartan` already says this), so `Coxeter step` here means the formal extension of the formula, and that this statement is the `a*b = 0` analogue of `affine_iterate`, a computation in the reflection model rather than a statement about a Coxeter element. Keeping the statement in the library is defensible on that basis (see §3). |

## 1. The five audit questions

**Hypotheses.** None are required: the identity holds for every `b : ℤ`, `n : ℕ`, `x y : ℤ`. Nothing is missing, and nothing would be gained by adding `b ≠ 0` or `0 ≤ b` — the statement is *stronger* than the "degenerate product with a nonzero partner" context of the T4 header, and it is still true (for `b < 0` the entry `a₂₁ = -b > 0` is even further from Cartan data, and the formula is unaffected). So on the hypothesis axis the statement is clean; the "stronger" is over the model, not over a standard fact, since no standard fact covers this range.

**Carrier and quantifier order.** It is a universally quantified identity about the explicit map `step 0 b` on `ℤ × ℤ`; one function, one statement, no conjunction over cases, no quantifier-order issue, and no `HasExactPeriod`. It mentions no Coxeter group, so it raises no faithfulness question — `LIMITATIONS.md`'s warning that the reflections are not shown to generate a Coxeter group is not a defect of *this* statement (it is a defect of statements 2 and 5).

**Meaning of the definitions used.** `step`, `s1`, `s2`, `iter` are unambiguous and used consistently: `step a b = s1 a ∘ s2 b`, so `step 0 b (x,y) = (-x, b*x - y)` and the sign in the conclusion is the correct one for that composition order. I checked this explicitly: for the reversed word `s2 b ∘ s1 0` the square is again a shear (`(x,y) ↦ (x, y + 2*b*x)`), and its `2n`-th iterate is `(x, y + 2 n b x)` — the opposite sign, so the statement's minus sign is the one attached to `step = s1 ∘ s2`, not a slip. So there is no sign or convention error; the doubling `2 * n` (ℕ) against `2 * (n : ℤ)` also matches.

**Vacuity.** Not vacuous — the identity genuinely constrains the even iterates, and it is exactly what rules out the possibility `iter (step 0 b) (2n) = id` for `b ≠ 0`. But it is *thin*: it is the binomial theorem for a nilpotent `N`, and as an "iterate" statement it is only the even half of the drift formula.

**Name and docstring.** `zero_product_iterate` is accurate as far as it goes (`a = 0` makes the product `a*b` zero). Two documentation defects: (i) "whose square is a shear" is true iff `b ≠ 0` — at `b = 0` the square is `I` (`step 0 0 (x,y) = (-x,-y)`, Lean: `step_zero_zero_sq_id`), and `b = 0` is in the statement's scope since `a = 0` makes `a*b = 0` for every `b`; (ii) "the Coxeter step" for a pair that is not a generalized Cartan matrix. Both are docstring-level, not proposition-level.

## 2. True but not what it says

The proposition is a correct matrix-power identity, and it is correct for a wider range of `b` than the surrounding prose describes, but it does not carry the content its context suggests. Its T4 context is "`a*b = 0` with a nonzero partner has no positive power equal to the identity", and the statement alone gives only the even iterates; the no-period reading needs the odd formula `iter (step 0 b) (2n+1) (x,y) = (-x, (2n+1)*b*x - y)` (Lean-checked here as `zero_product_iterate_odd`) together with `b ≠ 0`, and that is what statement 7 does. The "shear" reading also fails at the one parameter value that *is* inside Cartan theory: at `(0,0)` the matrix is `!![2,0;0,2]`, a genuine (decomposable) GCM of type `A₁ × A₁`, the step is `-1`, and the exact period is 2 — which is the `ab = 0` entry of the README's `2,3,4,6` list (`U2_exact`), not a shear at all. So the sentence "whose square is a shear" describes the pair that is *not* a Cartan pair, without saying so, and fails on the pair that is.

## 3. Is including it defensible?

Yes — as the computation it is, with corrected documentation; no, if a reader is allowed to take "Coxeter step" and "shear" at face value.

* It cannot mislead by being wrong: it is true for all `b`, `n`, `x`, `y`, needs no hypothesis, and I verified it both symbolically and in Lean.
* Its mathematical value in the library is real: it exhibits, *inside the model*, that `det(cartan 0 b) = 4 = 4 - a*b > 0` and that all principal minors (`2, 2, 4`) are positive, yet the map has infinite order. The finite-type criterion "all principal minors positive ⟺ finite type" (Kleshchev Thm 4.2.4(i), verified; Kac Thm 4.3, from memory) is a theorem *about GCMs*; the pair `(0,b)`, `b ≠ 0`, slips past the numerical test only because it fails axiom (C3) — and it is not symmetrizable either (`δ₁ a₁₂ = δ₂ a₂₁` would force `0 = -δ₂ b`). So `4 - a*b` alone indeed does not decide finiteness, which is the honest reading `LIMITATIONS.md` gives.
* What the library must not do is present it as a Coxeter-group fact. If a group-theoretic reading is wanted, the correct one is: for `b ≠ 0` the two involutions generate the infinite dihedral group, i.e. the Coxeter group with `m₁₂ = ∞` (standard: a group generated by two involutions is a quotient of `C₂ * C₂`; the product has infinite order here, so the quotient is `C₂ * C₂` itself — Humphreys Ch. 1 §1.1, **from memory**). The library does not formalize this, and `LIMITATIONS.md` correctly declines to claim that the reflection model is a faithful Coxeter representation. Statement 6 claims none of it, so it is defensible as long as it is not read as more.
* Suggested docstring, minimal fix: *"With `a = 0`: `step 0 b (x,y) = (-x, b*x - y)`, and its square is the shear `(x,y) ↦ (x, y - 2*b*x)` for `b ≠ 0` (the identity for `b = 0`). The pair `(0,b)` with `b ≠ 0` is not a generalized Cartan matrix in Kac's sense (`a₁₂ = 0`, `a₂₁ = -b`), so this is the formal extension of the step formula past the Cartan range: the `a*b = 0` analogue of `affine_iterate`. For `b ≠ 0` the two reflections still generate the infinite dihedral group, which is not claimed here."*

## 4. Blindness

I did **not** open `RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, `swarm/review/` (other than `AUDIT-BRIEF.md`), or anything under `.ultramath/` other than my own directory (I only wrote there; I read nothing from other members' directories). Disclosures: I did read `swarm/TASK.md` — the prover brief, which is not on the forbidden list but is also not on the "may read" list; it contains task framing and no proofs or verdicts. I listed the names of files in the repository root and in `swarm/` (names only). I ran `git status --porcelain` in the repository (empty).

## 5. Sources — verified versus from memory

**Verified** (text fetched and read): Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* (University of Oregon lecture notes, `pages.uoregon.edu/klesh/teaching/IDLALN.pdf`), Definition 1.2.1 (C1)–(C3), including `a_ij = 0 if and only if a_ji = 0`; Theorem 4.2.4 (finite type ⟺ all principal minors positive; affine ⟺ `det = 0` and proper principal minors positive); Theorem 4.1.12 (trichotomy). Excerpts kept in `sources-excerpt.txt`. My own computations (matrix powers, characteristic polynomial, nilpotence, exhaustive exact check) are verified directly in `arithmetic-check.log` and `Check.lean`.

**Seen in search results, not opened in full**: Perrin, *Introduction to Kac–Moody groups and Lie algebras*, Def. 4.2.1 (`a_ij = 0 ⇒ a_ji = 0`), and Andruskiewitsch's 2025 VUB slides citing `[Kac, Thm. 4.3]` — both restate the same axiom.

**From memory, not verified**: Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 §1 Definition 4.1 and the numbering of Theorem 4.3; Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 1 §1.1 (two involutions generate a dihedral group, `m = ∞` allowed). The brief's premise for statement 6 — "no source, this pair is not a generalised Cartan matrix" — I confirmed myself from the GCM axioms; the statement itself has no literature source to match, and its verdict rests on computation, not on a citation.

## 6. Repository untouched

Confirmed: I did not modify `$REPO`. Every file I wrote is in my own directory `.ultramath/smwbdn3l1/m1/`: `audit-report.md`, `Check.lean`, `arithmetic-check.log`, `sources-excerpt.txt`, plus *copies* `RankTwoCertificate.lean`, `Targets.lean` and the `.olean` files built from them (needed to compile the check; copies only). `git status --porcelain` in the repository prints nothing.

## Files

* `Check.lean` — Lean 4: the audited statement proved verbatim (`AuditStatement6.zero_product_iterate`, axioms `[propext]`), the odd-iterate formula, the even-power non-identity for `b ≠ 0`, and the `b = 0` facts (`step 0 0 = -1`, square `= id`, exact period 2).
* `arithmetic-check.log` — sympy: matrix, charpoly, `N² = 0`, symbolic `M^{2n}`, exhaustive exact check over `b ∈ [-20,20]`, `n ≤ 20`.
* `verify-check.log` — the Lean run of `Check.lean` (`exit=0`) with the `#print axioms` lines, showing no `sorryAx`.
* `sources-excerpt.txt` — the fetched definition and theorems behind the GCM citation.
