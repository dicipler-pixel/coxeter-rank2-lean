# Audit report — statement 1, `cartan_det`

**Statement audited** (`swarm/Statements.lean`, section "T1 — the determinant"):

```lean
theorem cartan_det (a b : ℤ) : (cartan a b).det = 4 - a * b := by
  sorry
```

with, from `swarm/Targets.lean` (line 19),

```lean
def cartan (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, -a; -b, 2]
```

so `cartan a b = [[2, -a], [-b, 2]]` over `ℤ`, and `.det` is Mathlib's `Matrix.det`.

## Verdict table

| # | statement | standard fact | verdict | evidence | correction needed |
| :-: | :--- | :--- | :--- | :--- | :--- |
| 1 | `cartan_det (a b : ℤ) : (cartan a b).det = 4 - a * b`, i.e. `det [[2,-a],[-b,2]] = 4 - a*b` | For the rank-two generalised Cartan matrix `A = [[2,-a],[-b,2]]` (Kac's GCM axioms: `a_ii = 2`, `a_ij ≤ 0` for `i ≠ j`, `a_ij = 0 ⟺ a_ji = 0`; indecomposable in rank two means `a, b ≥ 1`), `det A = 4 - ab`, and the sign of `4 - ab` is the finite/affine/indefinite trichotomy: `ab ≤ 3 ↔ det ≥ 1` (finite: `A₂, B₂/C₂, G₂`), `ab = 4 ↔ det = 0` (affine), `ab > 4 ↔ det < 0` (indefinite) | **matches** | Explicit computation of the 2×2 determinant (Lean proof + sympy, § Supporting computations); Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Ch. 4 "A Classification of Generalized Cartan Matrices", pp. 47–58; Kleshchev, *Lectures on Infinite Dimensional Lie Algebras*, Ch. 1 §1.2 Definition 1.2.1 (GCM axioms) and Ch. 4 Example 4.1.3, p. 51; Aguadé–Ruiz, *Cohomology of Kac–Moody groups over a finite field*, Algebr. Geom. Topol. 13 (2013), §2, p. 2210 (`Δ∇ = 4 − ab`); Bourbaki, *Lie Groups and Lie Algebras* Ch. VI §1 no. 3 (p. 148) and no. 5, Définition 3 (p. 154) | none |

## Why `matches`, and what the statement does not say

The proposition is exactly the rank-two Cartan determinant: the 2×2 matrix with `2` on the
diagonal and `-a`, `-b` off the diagonal has determinant `2·2 − (−a)(−b) = 4 − ab`. Mathlib's
`det` on `Matrix (Fin 2) (Fin 2) ℤ` is the Leibniz determinant, so the statement is the
literature identity and nothing else. It is **not vacuous**: there is no hypothesis that could be
failing or doing the work, and the equation is a genuine constraint whose two sides both vary
with `a` and `b` — `(a,b) = (2,2)` gives `0`, `(3,2)` gives `−2`, `(0,0)` gives `4`.

Three points an auditor should record, none of which is a defect:

1. **Hypotheses.** The standard fact is stated for `a, b ≥ 1` (or, more generally, for `a, b ≥ 0`
   with `a = 0 ⟺ b = 0`, the condition under which `cartan a b` still satisfies Kac's GCM axioms;
   `a = b = 0` gives the decomposable `A₁ × A₁`). The Lean statement drops every hypothesis and
   quantifies over `a b : ℤ`. This is a **benign generalisation**: the identity is a polynomial
   identity in `a, b`, so no hypothesis is needed for it, and dropping the GCM hypotheses cannot
   make it false — it only makes the statement also speak about matrices that are not GCMs. So
   the hypotheses are neither too weak nor too strong *for the identity*; `1 ≤ a, 1 ≤ b` would be
   needed only for the separate interpretation of `4 − ab` as the type criterion (Kac Ch. 4:
   finite `⟺ ab ≤ 3`, affine `⟺ ab = 4`, indefinite `⟺ ab > 4`), which this statement does not
   assert. The repository documents the extension honestly: `Targets.lean`'s docstring on
   `cartan` says the matrix is a GCM in Kac's sense "only when `a, b ≥ 0` and `a = 0 ⟺ b = 0`;
   the determinant identity below holds for all `a, b : ℤ`".
2. **What it does not carry.** `det = 4 − ab` alone does not imply that `det > 0` forces finite
   type, nor that `a*b = 4` gives unipotence; those are separate statements in this repository
   and separate theorems in the literature. The name `cartan_det` and the repository's framing
   ("T1 the Cartan determinant `4 - a*b`", `LIMITATIONS.md`: "the determinant is `4 − a*b`
   (`cartan_det`) and the characteristic polynomial is `λ² − (a*b − 2)λ + 1`") promise only the
   determinant, so there is no over-claim. Read alone, the statement has the modest content of a
   2×2 determinant identity; its interest is as the algebraic input to the classification.
3. **Carrier, quantifier order, definitions.** There is no map and no nested hypothesis here, so
   the "conjunction of implications" and "faithful action" failure modes listed in the brief do
   not apply. `cartan` is the standard matrix, with the same sign convention as Kac's
   `A = [[2,−a],[−b,2]]` (`A₂`, `B₂/C₂`, `G₂` at `(a,b) = (1,1),(1,2)/(2,1),(1,3)/(3,1)`), so the
   determinant computed is the Cartan determinant and not that of a transpose-with-different-
   signs variant (in rank two, and for any `a,b`, `det` is symmetric in `a,b` anyway).

**True but not what it says: nothing.** The proposition does not hold by accident, is not
vacuously true, and does not promise more than it is named and documented to deliver; the only
thing a downstream reader must keep straight is that the finite/affine/indefinite trichotomy is
carried by other statements (and other theorems), not by `cartan_det`.

## Supporting computations

**Lean.** I copied `def cartan` and the theorem statement verbatim from the repository (the texts
are character-identical; verified with `grep`, including the `ℤ` codepoints) into
`.scratch/CartanDetCheck.lean` in my directory and replaced `sorry` by a proof:

```lean
theorem cartan_det (a b : ℤ) : (cartan a b).det = 4 - a * b := by
  rw [cartan, Matrix.det_fin_two]
  simp
```

`lean CartanDetCheck.lean` exits `0`; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`. The same file contains eleven `decide` checks:
`(1,1) ↦ 3` (A₂), `(1,2)`, `(2,1) ↦ 2` (B₂/C₂), `(1,3)`, `(3,1) ↦ 1` (G₂), `(2,2)`, `(1,4)`,
`(4,1) ↦ 0` (affine `A₁⁽¹⁾`, `A₂⁽²⁾`), `(0,0) ↦ 4` (`A₁ × A₁`), `(0,5) ↦ 4` (not a GCM:
`a_12 = 0`, `a_21 ≠ 0`), `(3,2) ↦ −2` (indefinite).

**sympy.** `det([[2,-a],[-b,2]]) = -a*b + 4` symbolically, and each of the eleven values above
agrees with `4 - a*b`. Also, the Coxeter element of `RankTwoCertificate` has matrix
`[[ab-1, -a], [b, -1]]`, trace `ab - 2`, determinant `1`, characteristic polynomial
`λ² − (ab−2)λ + 1` with discriminant `ab(ab−4) = −ab · det(cartan a b)`. That is why `4 − ab`
is the right invariant to compute, and it is consistent with the periods `3, 4, 6` at
`ab = 1, 2, 3` and unipotence at `ab = 4`; it is context, not part of statement 1.

**Cross-check against Bourbaki's rank-two formula.** For a reduced root system with basis
`B = {α, β}`, Bourbaki's Cartan matrix is `(n(α,β))` with `n(α,α) = 2`, and by Ch. VI §1 no. 3
the product `n(α,β)n(β,α)` equals `4cos²θ` (θ the angle between `α` and `β`), is an integer and
is `< 4`. Writing `a = −n(α,β)`, `b = −n(β,α)` gives exactly `cartan a b`, so `ab ∈ {0,1,2,3}`
and `det = 4 − ab ≥ 1`; with `θ = π − π/m`, `m = ord(s_α s_β)`, this is `4sin²(π/m)`, equal to
`3, 2, 1` at `m = 3, 4, 6`. That is the finite side, where the determinant identity has its
content. (This derivation is mine; the Bourbaki inputs are cited below.)

## Blindness

I did **not** open `RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`,
`swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, anything in
`swarm/review/` other than `AUDIT-BRIEF.md`, or any file under `.ultramath/` other than the files
I created myself (my directory was empty when I started, and I neither listed nor read another
member's directory). `FalseControls/` and `scripts/` are not forbidden, but I did not open them
either, as they are irrelevant to this statement. Files I read: `swarm/review/AUDIT-BRIEF.md`,
`swarm/Statements.lean`, `swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`,
`LIMITATIONS.md`. Of those, only `swarm/Statements.lean` and `swarm/Targets.lean` carry the
statement and its definitions; the two files with docstrings (`Targets.lean`, `LIMITATIONS.md`)
describe scope, and I have taken them as claims about scope only, not as evidence for the
mathematics.

## Sources: verified vs from memory

**Verified today (fetched and read):**
- Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed. (CUP 1990): Chapter 4 is titled "A
  Classification of Generalized Cartan Matrices", pp. 47–58; Chapter 5 starts at p. 59
  (publisher's chapter listing, Cambridge Core / Google Books contents). I did **not** obtain
  Kac's Chapter 4 text (paywalled); the chapter title and page range are verified, its contents
  are not.
- Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* (Univ. of Oregon lecture notes),
  Ch. 1 §1.2, **Definition 1.2.1**: "A matrix `A ∈ M_n(ℤ)` is a generalized Cartan matrix (GCM)
  if (C1) `a_ii = 2` for all `i`; (C2) `a_ij ≤ 0` for all `i ≠ j`; (C3) `a_ij = 0` if and only
  if `a_ji = 0`." Chapter 4 "The Classification of Generalized Cartan Matrices",
  **Example 4.1.3, p. 51**:
  "Let `a, b` be positive integers, and `A = [[2,−a],[−b,2]]`. Then `A` is of finite (resp.
  affine, resp. indefinite) type if and only if `ab ≤ 3` (resp. `ab = 4`, resp. `ab > 4`)."
  Its Theorem 4.3.1 proof also lists "finite diagrams of rank 2 are `A₂, C₂, G₂`" and "affine
  diagrams of rank 2 are `A₁⁽¹⁾, A₂⁽²⁾`".
- Aguadé–Ruiz, *Cohomology of Kac–Moody groups over a finite field*, Algebr. Geom. Topol. 13
  (2013) 2207–2238, §2, **p. 2210**: with `a, b` positive integers and `A = [[2,−a],[−b,2]]` the
  generalized Cartan matrix, "We denote `Δ = s₁t₂ − s₂t₁`, `∇ = n₁m₂ − n₂m₁`, so that
  `Δ∇ = 4 − ab`" — i.e. `det A = 4 − ab` in a published source.
- Bourbaki, *Groupes et algèbres de Lie*, Ch. VI §1 (published text, scan): **no. 3 "Relations
  entre deux racines", p. 148**: `n(α,β)n(β,α) = 4cos²(·) < 4`, stated to be an integer (the OCR
  of the scan also prints a candidate list of values; I rely only on integrality and `< 4`);
  **no. 5, Définition 3, p. 154**: "On appelle matrice de Cartan de `R`
  (relativement à `B`) la matrice `(n(α,β))`", with `n(α,α) = 2` and `n(α,β) ∈ {0,−1,−2,−3}`
  for `α ≠ β`. (English edition: *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI §1.)

**From memory, not verified in the text:** that Kac's own §4.1–4.3 state the rank-two case in
exactly the form above and that Tables Fin/Aff list `det A`; that Bourbaki's no. 3 formula is
written with `m = ord(s_α s_β)` rather than the angle (I verified it as `4cos²` of the angle);
Humphreys' *Reflection Groups and Coxeter Groups* (not needed for this statement and not
consulted). Kac's own wording of the GCM axioms was seen only as a search-index excerpt of the
publisher's sample PDF (Introduction, p. xi) — the axioms themselves are verified in Kleshchev
§1.2, Definition 1.2.1, quoted above.

## Repository status

I did not modify the repository: no tracked file was created, edited or deleted (`git status
--porcelain -uno` and `git diff --stat` are both empty). Everything I wrote is inside my own
directory `.ultramath/smwbdn3bg/m1/`: this report and `.scratch/CartanDetCheck.lean` plus three
downloaded PDFs of the sources cited above (`.scratch/klesh.pdf`, `.scratch/bourbaki.pdf`,
`.scratch/agt.pdf`) and one empty file, `.scratch/kac_sample.pdf`, left by a blocked download of
the publisher's Kac sample.
