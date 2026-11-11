# Audit — statement 9, `tits_positive_definite`

Auditor: m1. Repository: `/workspace/nucleus/work/projects/p-870b05c7d9a34cc6a7491c6863177ba6/repo`.
Statement audited (verbatim from `swarm/Statements.lean`):

```lean
theorem tits_positive_definite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3)
    (x y : ℝ) (h : (x, y) ≠ 0) : 0 < titsForm (a : ℤ) (b : ℤ) x y
```

## 1. Verdict

| statement | standard fact | verdict | evidence | correction needed |
|---|---|---|---|---|
| 9 `tits_positive_definite` | For positive integers `a, b` the GCM `[[2,−a],[−b,2]]` is of **finite type** exactly when `a·b ≤ 3`; a symmetrizable GCM of finite type has its invariant form `(·\|·)` positive definite on the real span of the simple roots; and `titsForm a b x y` is a positive multiple of `(xα₁+yα₂ \| xα₁+yα₂)`. Hence the form is positive definite — Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 §4.3 (Thm 4.3 + Table Fin) and Ch. 2 §2.3; Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* §4.1–4.3. | **`matches`** | **Read in source** (Kleshchev): Ex. 4.1.3 p. 51 (`A = [[2,−a],[−b,2]]` is finite/affine/indefinite type iff `ab ≤ 3` / `= 4` / `> 4` for positive integers `a,b`); Prop. 4.2.1 p. 58; Thm 4.2.4 p. 60; **Prop. 4.3.2 p. 63: for an indecomposable GCM, "(i) A is of finite type" ⟺ "(ii) A is symmetrizable and the (·\|·) on h_ℝ is positive definite"**; §2.2 (2.7) `(αᵢ\|αⱼ) = aᵢⱼ/εᵢ`. **Explicit computation**: `2b·titsForm a b x y = (2bx − aby)² + ab(4 − ab)y²`, and `2b > 0`, `ab(4−ab) > 0` under the hypotheses; `2×2` criterion `2b > 0 ∧ det = ab(4−ab) > 0`; all five admissible pairs verified symbolically (eigenvalues `1,3`; `3∓√5`; `4∓√13`, all positive). **Lean**: `leancheck/TitsCheck.lean` proves the character-identical statement from definitions textually identical to `Targets.lean` (axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`). | None. Optional docstring precision: "finite side" here means the three indecomposable rank-two types `A₂, B₂/C₂, G₂`; `A₁⊕A₁ = (0,0)` is finite type but excluded (see §3). |

## 2. What the statement names, and whether it says it

The named fact is the finite-type half of the rank-two sign trichotomy for the symmetrised Cartan–Tits form. In this notation:

* `cartan a b = [[2,−a],[−b,2]]`; with `a, b ≥ 1` this satisfies Kac's GCM axioms (`aᵢᵢ = 2`, `aᵢⱼ ≤ 0` for `i ≠ j`, `aᵢⱼ = 0 ⟺ aⱼᵢ = 0`), is indecomposable, and is symmetrizable with `A = D·B`, `D = diag(ε₁,ε₂) = diag(a,b) > 0`, `B = [[2/a,−1],[−1,2/b]]` symmetric (Kleshchev Lemma 2.1.2: such `D` is unique up to a positive scalar; condition (2.2) gives `ε₂a = ε₁b`).
* `titsForm a b x y = 2b x² − 2ab xy + 2a y²`. Two exact identities, both machine-checked symbolically:
  * `titsForm a b x y = (x,y)ᵀ (diag(b,a)·cartan a b) (x,y)` — i.e. it *is* the quadratic form of the symmetrised bilinear form, in the repo's stated symmetriser `diag(b,a)` (which is `ab·D⁻¹`, a positive multiple of Kleshchev's `D` when `ab > 0`);
  * `titsForm a b x y = ab·(xα₁+yα₂ | xα₁+yα₂)` in Kleshchev's normalisation `(αᵢ|αⱼ) = aᵢⱼ/εᵢ`.

So it is **not** the raw/quiver quadratic form but a positive constant multiple of the symmetrised invariant form; positivity of that constant does not affect definiteness. (Relative to the quiver-theoretic Tits form `q_Q(x) = Σxᵢ² − Σ_{arrows} xᵢxⱼ` the normalisation differs by the factor 2 at `a = b = 1`; again only a positive constant.)

The chain of the standard fact, all read in the source:

1. `a, b ∈ ℤ_{>0}` and `ab ≤ 3` ⟹ `A` of finite type (Kleshchev Ex. 4.1.3).
2. finite type ⟹ symmetrizable with `(·|·)` positive definite on `h_ℝ` (Kleshchev Prop. 4.3.2, (i)⇒(ii), via Thm 4.2.3 + 4.2.4; equivalently `det > 0` with all principal minors positive, `2 > 0` and `4 − ab > 0`). Kleshchev states (ii) on `h_ℝ`; the map `ν : h → h*` of §2.2 is an isometry for `(·|·)` (his (2.6): `ν(αᵢ∨) = εᵢαᵢ`), so positive definiteness on `h_ℝ` and on `h*_ℝ = ℝα₁ ⊕ ℝα₂` are the same condition — which is the carrier `(x,y) : ℝ × ℝ` used by the statement.
3. `(·|·)` positive definite on the real span `ℝα₁ ⊕ ℝα₂` ⟺ `titsForm a b x y > 0` for `(x,y) ≠ 0` (positive scalar multiple, step above).

Under `1 ≤ a, 1 ≤ b` the hypothesis `ab ≤ 3` is *exactly* `ab ∈ {1,2,3}`, i.e. exactly `4 − ab > 0`, i.e. exactly the finite-type condition; there is no slack in either direction (`ab = 4` is affine: `titsForm 2 2 1 1 = 0`; `ab > 4` is indefinite: `titsForm 2 3 1 1 = −2 < 0`). The five admissible pairs `(1,1),(1,2),(2,1),(1,3),(3,1)` are `A₂, B₂, C₂, G₂` and their transposes, i.e. **all** positive-integer rank-two representatives on the finite side, not one per product.

## 3. Hypotheses, carrier, quantifiers, vacuity, naming

**Hypotheses — are they needed, are they enough?** Both are load-bearing, and the list is sharp:

* `a b : ℕ` (not `ℤ`): over `ℤ`, `(a,b) = (−1,−1)` satisfies `ab = 1 ≤ 3` but `titsForm (−1) (−1) 1 0 = −2 < 0`, so the statement would be false.
* `1 ≤ a`, `1 ≤ b`: without them (still `a, b : ℕ`) the statement is false — `titsForm 0 1 0 1 = 0` and `titsForm 1 0 0 1 = 0` (form only positive *semi*definite). So the guard is necessary, not decoration.
* `a * b ≤ 3` jointly with the above is sufficient and exact (see §2). There is no missing hypothesis: no faithfulness, no integrality of `(x,y)`, nothing about reflection groups is needed for a statement about a quadratic form on `ℝ²`.

**Carrier and quantifier order.** Quantification is over *all* pairs at once (`∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*b ≤ 3 → ∀ x y : ℝ, (x,y) ≠ 0 → …`), i.e. a single implication with a numeric hypothesis — not a conjunction of implications `ab = 1 → …`, `ab = 2 → …` (the defect that affects statement 2 does **not** affect this one). The carrier `ℝ × ℝ` with `(x,y) ≠ 0` is the right one: positivity of the invariant form is a statement about the real span of the simple roots, `ℝα₁ ⊕ ℝα₂`. (Restricting to `ℤ × ℤ` would have been strictly weaker; `ℝ²` is the standard carrier.)

**Vacuity.** None. The hypothesis `(x,y) ≠ 0` is satisfiable, the form is a genuine positive definite form on each of the five pairs (eigenvalues computed), and the proposition becomes false under each single weakening listed above. It is not true "for a trivial reason".

**Name and docstring.** `tits_positive_definite` / "Finite side: the Tits form is positive definite." — accurate for what is proved. The name does not promise the converse, and `Targets.lean`'s docstring ("What the targets prove is positive definiteness for `1 ≤ a, b` with `a*b ≤ 3`") describes exactly the proposition. The only overreach is in `README.md` ("The symmetrised Tits form of the Cartan matrix is positive definite on the finite side"), whose "finite side" as listed in that same README includes the product `ab = 0`, represented by `(0,0)` — see the next section.

## 4. True but not quite what the surrounding prose says

Two honest qualifications, neither of which makes the proposition wrong:

1. **One direction of a biconditional.** The standard fact (Kleshchev Prop. 4.3.2, Kac Thm 4.3) is an equivalence: finite type ⟺ the symmetrised form is positive definite. Statement 9 delivers `⟹` only, in rank two. That is the normal decomposition here, since statements 10 and 11 carry the affine and indefinite sides; it is not a weakening of the claim the name makes.
2. **`ab = 0` / `A₁⊕A₁` is silently outside the "finite side".** `(a,b) = (0,0)` *is* a GCM of finite type (the decomposable `A₁⊕A₁`, all principal minors `2,2,4` positive), and its invariant form is `2x² + 2y²`, positive definite. But the definition in `Targets.lean` uses the fixed symmetriser `diag(b,a)`, which at `(0,0)` is `diag(0,0)` — not a positive symmetriser — so `titsForm 0 0 x y = 0` identically. The hypothesis `1 ≤ a, 1 ≤ b` therefore is what keeps statement 9 true, and it also means statement 9 does *not* cover the whole finite side as the README advertises (products `0,1,2,3`); it covers the three indecomposable rank-two finite types (five representatives). A cosmetic fix would be to say "positive definite for the indecomposable finite types (`ab ∈ {1,2,3}`)" in the README, or to add the `(0,0)` case with the symmetriser `diag(1,1)`. This is a defect of `titsForm` as a formula at `ab = 0`, not of statement 9, whose hypotheses exclude it explicitly.

## 5. Blindness

I did not open `RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, `swarm/review/` (other than `AUDIT-BRIEF.md`), or anything under `$REPO/.ultramath/` other than my own directory (which was empty when I started; every file in it was created by me). Files I did read: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. `git status --porcelain` at the repo root printed nothing, before and after my work.

## 6. Sources: verified vs from memory

* **Verified (read in the source, author's PDF):** A. Kleshchev, *Lectures on Infinite Dimensional Lie Algebras* (2007), `https://darkwing.uoregon.edu/~klesh/teaching/IDLALN3.pdf` (also `IDLALN1.pdf`): Example 4.1.3 (p. 51), Remark 4.1.14 (p. 58), Lemma 4.1.13, Proposition 4.2.1 (p. 58), Theorem 4.2.3 (p. 60), Theorem 4.2.4 (p. 60), Proposition 4.3.2 (p. 63), Lemma 2.1.1 / 2.1.2 and §2.2 formulas (2.1)–(2.10) (pp. 26–28). Page numbers are the notes' own; the quotations above are from the extracted text of that PDF (local copy in `.scratch/`, not a repository file).
* **Corroborated but not read in the primary text (treat as recalled):** Kac, *Infinite-Dimensional Lie Algebras* (3rd ed., CUP 1990), Ch. 4 §4.3 Theorem 4.3 and Table Fin, and Ch. 2 §2.3 (invariant bilinear form). I did not open Kac's book; the content I attribute to it is quoted with the same content by independent secondary sources (e.g. `theses.gla.ac.uk/84704`, Thm 2.4 "Cf. [Kac90, Theorem 4.3]"; `sites.pitt.edu/~bion/pdf/mehrle-thesis.pdf`, Thm 1.4.9), and it coincides with Kleshchev Thm 4.2.4, which I did read.
* Everything algebraic in §1–§3 (identities, determinants, eigenvalues, counterexamples) is my own computation, run and reproducible with the commands below. No part of the verdict rests on an unverified citation.

## 7. Repository untouched; artefacts

No file of `$REPO` was modified (`git status --porcelain` clean throughout). Artefacts, all in my own working directory:

* `audit-report.md` — this file.
* `leancheck/TitsCheck.lean` — `cartan` and `titsForm` copied verbatim from `swarm/Targets.lean`, statement 9 copied verbatim from `swarm/Statements.lean` (checked character-identical by script), with a complete proof. Run:
  `lean .ultramath/smwbdn3qn/m1/leancheck/TitsCheck.lean`
  Output: `'OperatorFirst.CoxeterRankTwo.tits_positive_definite' depends on axioms: [propext, Classical.choice, Quot.sound]`.
* The proof is by the identity `2b·titsForm = (2bx − aby)² + ab(4−ab)y²`: both summands positive when `y ≠ 0`; when `y = 0`, `x ≠ 0` and the first summand is `(2bx)² > 0`; then divide by `2b > 0`.
