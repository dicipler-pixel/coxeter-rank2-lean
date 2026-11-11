# Audit — statement 8, `zero_partner_no_positive_period`

**Exact Lean text** (`swarm/Statements.lean`, lines 76–78, verbatim):

```lean
/-- The mirror case `b = 0`, `a ≠ 0`, on the witness `(0, 1)`. -/
theorem zero_partner_no_positive_period (a : ℤ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step a 0) n (0, 1) ≠ (0, 1)
```

Repository context: this is target **T4** of the file header ("the degenerate product `a*b = 0`
with a nonzero partner has no positive power equal to the identity (`HasExactPeriod` is not
claimed, and would be the wrong form here)"); `LIMITATIONS.md` claims "`4 − ab > 0` alone does not
give finiteness, because `ab = 0` with a nonzero partner has infinite order"; `README.md` claims
"A pair with `a*b = 0` and a nonzero partner has infinite order on an explicit vector
(`zero_product_no_positive_period`)". Definitions are those of `RankTwoCertificate.lean`
(`s1 a (x,y) = (-x + a y, y)`, `s2 b (x,y) = (x, b x - y)`, `step a b = s1 a ∘ s2 b`,
`iter f (n+1) = f ∘ iter f n`).

## 1. Verdict table

| statement | standard fact | verdict | evidence | correction needed |
|---|---|---|---|---|
| **8** `zero_partner_no_positive_period`: for all `a : ℤ` with `a ≠ 0` and all `n > 0`, `iter (step a 0) n (0,1) ≠ (0,1)`. | Two involutions whose product has infinite order generate the infinite dihedral group, and no positive power of the product is the identity — the rank-two `m = ∞` case of Coxeter theory (`I₂(∞)`). Here `step a 0 = s1 a ∘ s2 0 = −I − a·N` with `N² = 0 ≠ N`, so the product has infinite order: trace `−2`, determinant `1`, eigenvalue `−1` twice with a single Jordan block. The pair `(a,0)`, `a ≠ 0`, is *not* a generalised Cartan matrix (Kac's axiom (C3) fails: `a₁₂ = −a ≠ 0`, `a₂₁ = 0`), so the Cartan/Kac trichotomy does not cover it; what it instantiates is the Coxeter-theoretic `m = ∞` fact, whose honest evidence here is the computation. | **`matches`** — true as stated, hypotheses exactly tight, and it implies the map-level "no positive period" fact. It is in fact *stronger* than that fact (it asserts the specific orbit of `(0,1)` is infinite), and the strengthening is true. Not vacuous, not weaker, not misleading given the docstring (which names the witness). | Exact computation, §2: `iter (step a 0) n (x,y) = ((−1)ⁿ(x + n a y), (−1)ⁿ y)`, so `iter (step a 0) n (0,1) = ((−1)ⁿ n a, (−1)ⁿ)`, which is `(0,1)` only if `n a = 0` and `n` is even — impossible for `n > 0`, `a ≠ 0`. Machine-checked, `sorry`-free, axiom-clean proof in `.scratch/audit8.lean`. Literature: Humphreys §1.1 (product of the two simple reflections of `I₂(m)` has order `m`); for `m = ∞` the product of the two simple reflections is `id + N`, `N² = 0`, `N ≠ 0`, hence infinite order (Durham notes §8.4, verified); Kac Ch. 4 §1 (C3), verified. | **None.** Optional strengthening for symmetry with the mirror statement 7: add the iterate formula (`zero_product_iterate` has one) and/or the one-line map-level corollary `iter (step a 0) n ≠ id`. |

## 2. The computation, and why each hypothesis is there

In coordinates

```
step a 0 (x, y) = s1 a (x, −y) = (−x − a y, −y),
```

with matrix `M = [[−1, −a], [0, −1]] = −I − a·N`, `N = [[0,1],[0,0]]`, `N² = 0`. `N` commutes with
`I`, so `Mⁿ = (−1)ⁿ (I + n a N)`, i.e. the exact iterate

```
iter (step a 0) n (x, y) = ((−1)ⁿ · (x + (n:ℤ)·a·y), (−1)ⁿ · y)          (★)
```

(`AuditS8.iter_step_zero`, proved by induction). Hence

```
iter (step a 0) n (0, 1) = ((−1)ⁿ · n · a, (−1)ⁿ),
```

which equals `(0,1)` iff `(−1)ⁿ = 1` and `n·a = 0`. For `n > 0` and `a ≠ 0` both fail, so the
statement holds. `trace M = −2 = a·b − 2` at `b = 0`, `det M = 1`, characteristic polynomial
`(λ+1)²`; since `M + I = −aN ≠ 0`, `M` is not diagonalizable and has infinite order. So `M` is
conjugate in `GL(2,ℚ)` to `−[[1,1],[0,1]]`, a sign times a nontrivial unipotent — the same
det-1/trace-2 Jordan-block mechanism by which the literature handles the `m = ∞` Coxeter product.

**Tightness of the hypotheses.** Both are needed, and neither is excessive.

* `a ≠ 0` is *necessary*: at `a = 0`, `step 0 0 = −I`, so `iter (step 0 0) 2 (0,1) = (0,1)`, and
  the conclusion with `a = 0`, `n = 2` is false; the hypothesis cannot be dropped
  (`AuditS8.hypothesis_needed`). `(0,0)` is exactly the finite type `A₁ × A₁`, whose Coxeter
  element has period 2, so `a ≠ 0` excludes precisely the finite case.
* `0 < n` is *necessary*: `iter f 0` is the identity.
* `a ≠ 0` is not *too strong*: the proof is uniform in `a : ℤ`, so negative `a` are covered too
  (checked symbolically for `a = −1, −3`); `1 ≤ a` would be a stronger hypothesis than needed.
* The *witness* is necessary, and this is the sharp point of the statement: `y = 0` is fixed
  pointwise by `M² = I + 2aN`, so `iter (step a 0) 2 (1,0) = (1,0)` for **every** `a`
  (`AuditS8.mirror_witness_fails`). Statement 7's witness `(1,0)` does not transfer to the mirror
  case — under the conjugacy below it corresponds to `(0,1)`, and `(1,0)` itself is 2-periodic for
  `step a 0`. Using `(1,0)` here would have made the statement false; `(0,1)` is the correct
  witness, and the docstring says so.

**Relation to the map-level fact.** A positive power of `step a 0` equal to the identity would fix
every point, hence `(0,1)`; so the proposition implies "`step a 0` has no positive period"
(`AuditS8.no_positive_power_eq_id`). Conversely the map-level fact does *not* in general imply it
(a shear fixes a line), so the witness form is genuinely stronger — and here it is true (★).
`HasExactPeriod` is correctly not claimed: it demands a *universal* period `∀ x, iter f n x = x`,
and `step a 0`, `a ≠ 0`, has none, because `Mⁿ ≠ I` for all `n > 0`.

**The mirror relation is exact.** The swap `(x,y) ↦ (y,x)` conjugates `s1 a` to `s2 a` and `s2 0`
to `s1 0` (`AuditS8.swap_conj_s1`, `AuditS8.swap_conj_s2`), hence `step a 0 = s1 a ∘ s2 0` to
`s2 a ∘ s1 0 = (step 0 a)⁻¹`, and carries `(1,0)` to `(0,1)`. Inversion does not change orders or
return times, so statement 8 is literally statement 7 with the coordinates swapped; the witness
choice is forced by that correspondence.

## 3. True but not what it says (caveats worth recording)

1. **"No positive period" must be read at the level of the map, not the point.** For `a ≠ 0` the
   map `step a 0` *does* have periodic points: every `(x,0)` returns after 2 steps. Read as "no
   point of `ℤ²` is periodic" the name would be false. The docstring's "on the witness `(0,1)`"
   is what keeps it honest; the name remains defensible because the single-orbit statement
   implies the map-level one (§2).
2. **The pair `(a,0)`, `a ≠ 0`, is not a generalised Cartan matrix**, so the Cartan-matrix
   theory does not apply to it. Kac's axioms (C1) `a_ii = 2`, (C2) `a_ij ≤ 0`, (C3)
   `a_ij = 0 ⟺ a_ji = 0`; here `a₁₂ = −a ≠ 0` while `a₂₁ = 0`, violating (C3) (this is also said
   in the `cartan` docstring of `Targets.lean`), so the finite/affine trichotomy
   (`ab ≤ 3` / `ab = 4` / `ab > 4`, stated for positive integers `a, b`) says nothing here.
   What does apply is Coxeter theory, and it applies in full: `s1 a` and `s2 0` are still genuine
   involutions with fixed hyperplanes, their product has infinite order, so the group they generate
   is the infinite dihedral group — the Coxeter group of type `I₂(∞)`. The map
   `⟨s, t | s² = t² = 1⟩ → GL(2,ℤ)`, `s ↦ s1 a`, `t ↦ s2 0`, is injective: every nontrivial normal
   subgroup of `D_∞ ≅ ℤ ⋊ ℤ/2` contains a nonzero power of `st`, which the image does not. So the
   statement is a genuine rank-two Coxeter statement, of the `m = ∞` case — just not one attached
   to a generalised Cartan matrix. Including it is defensible on exactly that ground: it is true,
   elementary, it is the honest `m = ∞` companion of the finite cases, and it isolates a real
   phenomenon (item 3), provided it is labelled a statement about the reflection model rather than
   about GCMs — which the file header, the `cartan` docstring, `LIMITATIONS.md` and `README.md`
   all do.
3. **"`4 − ab > 0` alone does not give finiteness" is honest, with one qualification.** For this
   pair `det (cartan a 0) = 4 − 0 = 4 > 0` while the order is infinite, so the implication
   "positive Cartan determinant ⇒ finite order" genuinely fails *in the model*. It is not a defect
   in Kac's criterion: within the GCM class the proper principal minors of a `2×2` matrix are
   `2, 2 > 0`, so `det = 4 − ab > 0` *is* equivalent to finite type; the counterexample lives
   outside that class (`a ≠ 0, b = 0`, not a GCM). The careful reading is therefore "the
   determinant criterion needs the GCM hypotheses, and `ab = 0` with a nonzero partner is outside
   them" — which is a legitimate reason to carry `1 ≤ a, 1 ≤ b` in the finite statement. The
   naive order formula of the rank-two theory, `a b = 4 cos²(π/m)`, makes the point vivid: at
   `ab = 0` it predicts `m = 2` (order 2), correct for `(0,0)` but wrong for `(a,0)`, `a ≠ 0`.
   So the slogan "the product `ab` determines the period" fails exactly at `ab = 0`.
4. Minor: the naming split (7 = `zero_product_…` for `a = 0`, 8 = `zero_partner_…` for `b = 0`) is
   asymmetric but the docstrings disambiguate; cosmetic only.

## 4. Files, checks run, and repository state

* `.scratch/audit8.lean` — `s1`, `s2`, `step`, `iter` copied verbatim from `RankTwoCertificate.lean`
  (the repository is not imported, so no build artefacts are written into it); proves the statement
  verbatim (`AuditS8.zero_partner_no_positive_period`, identical text to `swarm/Statements.lean`
  77–78), plus `iter_step_zero` (★), `no_positive_power_eq_id`, `hypothesis_needed`,
  `mirror_witness_fails`, `orbit_grows`, `swap_conj_s1/s2`.
  `lean .scratch/audit8.lean` — exit 0, no `sorry`, and `#print axioms` gives only
  `propext, Classical.choice, Quot.sound` for every theorem above.
* `.scratch/check.py` — sympy: matrix of `step a b` (`[[ab−1, −a],[b, −1]]`), `Mⁿ = (−1)ⁿ(I + naN)`
  for `n ≤ 6`, orbit of `(0,1)` and of `(1,0)`, the `a = 0` failure, characteristic polynomials at
  `(1,1), (1,2), (1,3), (2,2), (0,0), (1,0)`, and `4cos²(π/m)` for `m = 2,3,4,6` = `0,1,2,3`.
* **I made no change to `$REPO`.** `git status --porcelain` was empty at my first check; at my last
  check it reports `M README.md`, a modification I did **not** make: that diff rewrites the sentence
  about the Tits form at `(a, b) = (0, 0)` — statement 9's subject, not mine — and I left it alone.
  The README sentence I quote above ("A pair with `a*b = 0` and a nonzero partner has infinite order
  on an explicit vector …") is unchanged (it appears as a context line of that diff) and is present
  in the working tree; `swarm/Statements.lean` is unmodified. Everything I created is under
  `.ultramath/smwbdn3ot/m1/` (which is `.gitignore`d). I audited no statement other than 8.

## 5. Blindness

Opened, and only these: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`,
`swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. **Not opened:**
`RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`,
`swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`,
`swarm/review/` (other than the brief), and anything else under `.ultramath/` — I did not read any
other auditor's report. Disclosure: I listed the repository root (names only, through the file
tool) and ran `git status`/`git log --oneline -3` to confirm the tree was clean, so I saw three
commit *subjects* ("Add the audit brief …", "Prepare a reviewer packet …", "Fold the second audit
pass in: two defects it found, fixed"); no file contents beyond the six listed above.

## 6. Sources: verified vs recalled

**Verified** (text fetched and read during this audit):

* Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Ch. 4 §1: definition of generalised Cartan
  matrix, (C1) `a_ii = 2`, (C2) `a_ij ≤ 0` for `i ≠ j`, (C3) `a_ij = 0 ⟹ a_ji = 0` (stated
  both ways) — read in the publisher's sample PDF of the book's Introduction (p. xi) and in
  A. Kleshchev, *Lectures on Infinite Dimensional Lie Algebras*, Def. 1.2.1 (restating Kac).
  This is the basis for "`(a,0)` is not a GCM".
* Rank-two trichotomy: `A = [[2,−a],[−b,2]]` with `a, b` **positive integers** is of finite /
  affine / indefinite type iff `ab ≤ 3` / `ab = 4` / `ab > 4` — A. Kleshchev, *Lectures on IDLA*,
  Example 4.1.3 (verified text); the same positive-integer hypothesis is used in the rank-two
  Kac–Moody literature (e.g. the Rutgers rank-two Fibonacci paper, verified excerpt). Kac's own
  numbering of this example is **not** verified (see below).
* Humphreys, *Reflection Groups and Coxeter Groups*, §1.1, type `I₂(m)`: "a rotation through
  `2π/m` can be achieved as a product of two reflections relative to a pair of adjacent diagonals
  which meet at an angle `θ := π/m`", and the computed product is the rotation through `2θ` —
  verified in the book's preview text. This is the `m < ∞` side and fixes the meaning of "the
  product of the two simple reflections has order `m`".
* `m = ∞` mechanism: for `m = ∞` the product of the two simple reflections is `id + N` with
  `N ≠ 0`, `N² = 0` (determinant 1, trace 2, not the identity), hence conjugate to `[[1,1],[0,1]]`
  and of infinite order — P. Tumarkin, Durham *Combinatorics* notes, §8.4 (verified text).
  M. Davis, *Introduction to Coxeter Groups* (handout): "a dihedral group is determined by the
  order `m` of `st`, `m ≥ 2` or `∞`" (verified text).
* Wikipedia, *Infinite dihedral group*: presentation `⟨x, y | x² = y² = 1⟩` (used only as a
  sanity check, not as a mathematical source).

**From memory / not fetched:**

* Bourbaki, *Lie Groups and Lie Algebras*, Ch. IV §1 no. 2 — the source the brief names for the
  rank-two `m = ∞` case. I did not fetch a copy; the claim I use from it (two involutions whose
  product has infinite order generate the infinite dihedral group) is verified instead by the
  sources above and by the computation.
* Kac Ch. 4 §4.3 numbering of the rank-two example, and Kac Prop. 4.7 ("finite type iff
  `det A ≠ 0` and all proper principal minors `> 0`"): the statement of Prop. 4.7 appeared in the
  scanned-text excerpt I read, but its numbering and page are recalled.
* Page numbers throughout.
