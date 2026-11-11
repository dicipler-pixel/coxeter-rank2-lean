# Audit report — statement 11, `tits_negative_above_four`

Auditor: m1 (swarm smwbdn3ug). Statement audited, verbatim from `swarm/Statements.lean`:

```lean
theorem tits_negative_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 < 0
```

Definitions (`swarm/Targets.lean`, read, not modified):
`cartan a b = !![2, -a; -b, 2]`, `titsForm a b x y = 2*b*x^2 - 2*(a*b)*x*y + 2*a*y^2`
(the quadratic form of `diag(b,a) * cartan a b`, which is symmetric).

## Row

| statement | standard fact | verdict | evidence | correction needed |
| :--- | :--- | :--- | :--- | :--- |
| 11 `tits_negative_above_four`: for `a b : ℕ`, `1 ≤ a`, `1 ≤ b`, `4 < a*b`, the Tits form of `[[2,−a],[−b,2]]` is negative at the single vector `(a,2)` | Kac Ch. 4 (rank-two case): `A = [[2,−a],[−b,2]]`, `a,b ≥ 1`, is of finite type iff `ab ≤ 3`, of affine type iff `ab = 4`, of **indefinite type** iff `ab > 4`; in the indefinite case the symmetrised Tits form `q_A` is **indefinite** — in rank two of signature `(1,1)` — and Kac's criterion gives `u > 0` with `A u < 0` | **weaker than the standard fact** (true, non-vacuous, and accurately named/documented; it is the "one negative value" half of indefiniteness, not indefiniteness/signature/type) | explicit computation (§1 below, also Lean-checked); Kac Ch. 4 Thm 4.3 via secondary restatements; Fomin–Zelevinsky §2.4 for `ab ≶ 4`; Carbone for signature `(1,1)` at `ab > 4` | none for truth; to state the literature fact add indefiniteness/signature, e.g. `∃ v, titsForm a b v < 0` together with `∃ w, 0 < titsForm a b w` (one line from the identity in §1). `ha`, `hb` are **redundant** over `ℕ` (both follow from `hab`) but harmless — the statement with and without them is logically equivalent |

## 1. Computation (the statement is true, and thin)

With `D = diag(b,a)`, `D·A = [[2b, −ab],[−ab, 2a]]` is symmetric and

`titsForm a b x y = (x,y)ᵀ (D·A) (x,y) = Σ_i d_i x_i (A x)_i`,  `d = (b,a)`.

Both identities verified symbolically, and in Lean with the definitions copied verbatim. Hence, at `x = (a,2)`:

- `A·(a,2)ᵀ = (2a − 2a, −ab + 4) = (0, 4 − ab)`;
- `titsForm a b a 2 = b·a·0 + a·2·(4 − ab) = −2a(ab − 4)`;
- for `a,b ≥ 1` and `ab > 4` (so `ab ≥ 5`) this is `≤ −2 < 0`. True, no edge cases.

`det(D·A) = ab(4 − ab) < 0` and `trace = 2(a+b) > 0` for `ab > 4`, so the form really does have signature `(1,1)` there, and `titsForm a b 1 0 = 2b > 0` gives the positive value. The statement asserts only the negative value; the positive one (and hence indefiniteness) is never stated, although it is one line away.

Boundary notes: over `ℤ` the statement is **false** (`a = −1, b = −5`: `ab = 5 > 4`, `titsForm = +2`), Lean-checked; so the `ℕ` carrier is doing real work and the mathematical content used is exactly `a > 0`. `ha`, `hb` are literally redundant: `4 < a*b` over `ℕ` already forces `a, b ≥ 1` (Lean-checked). Hypotheses are therefore correct in substance and only cosmetically redundant.

Normalisation: `titsForm` is the quadratic form `xᵀ(D·A)x`, i.e. **twice** the normalised Tits form `q_A(x) = ½ xᵀ(D·A)x` customary in the literature; a positive factor, so all sign conclusions transfer, but the value `−2a(ab−4)` is twice the "natural" `−a(ab−4)`. `cartan a b` with `a,b ≥ 1` is a legitimate indecomposable symmetrisable GCM in Kac's sense (`a_ij ≤ 0`, `a_ij = 0 ⟺ a_ji = 0` holds with all entries nonzero, symmetriser `diag(b,a)`), so the hypotheses of Kac Ch. 4 are met; the statement itself does not use that.

## 2. True but not what the name suggests

The statement is not vacuous — `(a,b) = (2,3)` satisfies the hypotheses and the conclusion — but its entire content is the arithmetic inequality `a(ab−4) > 0`: a single evaluation of a quadratic form at the vector `(a,2)`. It carries no linear-algebraic or group-theoretic content: no rank, kernel, radical, signature, no root or reflection, no statement that `A` is not of finite/affine type, and no statement about `step`/`V` or a Coxeter group. The vector `(a,2)` is not arbitrary: it is exactly the null vector of `A` at `ab = 4` (`A(a,2)ᵀ = (0, 4−ab)`, spanning `ker A` for the two affine rank-two GCMs `(2,2)` and `(1,4)`), continued past the affine point; that is why the value is proportional to `ab − 4`. So the statement is the "negative somewhere above four" fragment of the standard indefinite-type fact, and it is a *positive* vector that is evaluated, matching the shape of Kac's criterion (`∃ u > 0, Au < 0`). The docstring in `Statements.lean` ("the same vector makes the form negative once `a*b > 4`") promises only this, and `LIMITATIONS.md` explicitly disclaims indefiniteness above (`"that it is indefinite above [is] not formalized"`), in agreement with the docstring of `titsForm` in `Targets.lean`. So the naming is honest; what is missing is the literature's stronger claim, not something the repository claims.

Lean check of the statement itself (definitions `cartan`, `titsForm` copied verbatim into my own directory; the repository was not imported, built, or touched):

```
'Audit11.tits_negative_above_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Sources — verified vs from memory

Verified (pages/excerpts read during this audit):
- **Fomin–Zelevinsky**, *Positivity and canonical bases in rank 2 cluster algebras of finite and affine types* (arXiv:math/0307082), §2.4: `A(b,c) = [[2,−b],[−c,2]]` "is of finite (resp. affine, indefinite) type if so is `A(b,c)`, i.e. if `bc ≤ 3` (resp. `bc = 4`, `bc > 4`)" — verified from the paper's text.
- **Carbone**, *The geometry of rank 2 hyperbolic root systems* (Rutgers preprint): "When `ab < 4`, `A` is positive definite ... `ab = 4`, positive semi-definite but not positive definite ... `ab > 4`, `A` is indefinite but every proper generalized Cartan submatrix is positive definite, and so `A` is hyperbolic" — verified; and the companion rank-2 paper states the Lorentzian "metric of signature `(1,1)` when `ab > 4`" — verified.
- **Kac Thm 4.3 as restated by secondary sources**: Vendramin, *VUB-Leerstoel 2025–2026*, lecture 4: "Theorem (Vinberg) [Kac, Thm. 4.3] ... (Indefinite) there is `u > 0` s.t. `Au < 0`"; and Mehrle, *Structure and Representation Theory of Infinite-dimensional Lie Algebras* (Pittsburgh thesis), Thm 1.3.10 / Cor. 1.3.11 (attributed to Vinberg 1971): `A` is of finite/affine/indefinite type iff there is `x > 0` with `Ax > 0`, `= 0`, `< 0`; Lemma 1.4.3 there gives finite ⟺ positive definite, affine ⟺ positive semidefinite of rank `n−1` for symmetric `A`. Both verified from the sources' text.
- Chapter title and page range of Kac Ch. 4 ("A Classification of Generalized Cartan Matrices", pp. 47–58, 3rd ed.) verified from the Cambridge University Press catalogue entry.
- Normalisation `q(x) = ½ x M xᵀ` for the form attached to a symmetric matrix `M`: stated in arXiv:1107.3299; quiver Tits form convention in the Encyclopedia of Mathematics entry "Tits quadratic form" — verified.
- `Kac–Moody algebra` overview (Wikipedia): symmetrisable indecomposable `C = DS` is finite/affine/indefinite type according as `S` is positive definite / positive semidefinite / indefinite — verified as a secondary summary.

From memory / not verified directly:
- **Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Ch. 4 and its Table Aff were not opened** (no access). The attribution of the trichotomy to "Kac Thm 4.3" rests on Vendramin's notes; the theorem number could not be checked against the book itself.
- The equivalence "indefinite type ⟺ the Tits form `q_A` is indefinite" is recalled as standard for symmetrisable GCMs (it follows from the symmetric-case lemma restated above plus the symmetriser); I verified only the rank-two instance (`det(D·A) < 0` for `ab > 4`), not the general statement in Kac.
- Kac's exact definition/normalisation of the Tits form in Ch. 2 is recalled, not read; the sign conclusions used here are independent of the normalisation.

## 4. Blindness

I did **not** open `RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, any other file under `swarm/review/` besides `AUDIT-BRIEF.md`, or anything under `.ultramath/` other than files in my own directory `.ultramath/smwbdn3ug/m1/`. Files read: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. Nothing was read from the classification/proof side of the repository.

## 5. Repository untouched

I made no change to `$REPO`. All writing was in `.ultramath/smwbdn3ug/m1/` (this report and `.scratch/Audit11.lean`). The Lean check used copies of `cartan`/`titsForm` in my own directory rather than importing or building the repository, so no build artefacts were created in `$REPO`; `git status --porcelain` in `$REPO` is empty.
