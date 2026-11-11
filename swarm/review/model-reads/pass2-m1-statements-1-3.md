# Audit report — member m1, statements 1–3 (`cartan_det`, `finite_exact_period`, `affine_unipotent`)

Swarm smwb7g95j. Audited files (only these): `swarm/Statements.lean`, `swarm/Targets.lean`,
`RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. Blind protocol respected: I did **not**
open `RankTwoClassification.lean`, `swarm/submissions/`, `$REPO/.ultramath/` (beyond listing my own
empty directory `m1/`), `swarm/RESULT.md`, or `swarm/Classification.lean`. The repository was **not
modified by me**: every shell/file call I made was read-only; `git status` shows the tree was
already modified relative to HEAD before my session began (mtimes of the modified files are
21:31:35–21:32:44, my first command ran later, and I issued no write to the repo).

Model facts used throughout (all verified by explicit sympy computation in this session):
`step a b` has matrix `M(a,b) = [[a*b-1, -a],[b, -1]]` on `V = ℤ×ℤ` (columns = images of
`(1,0),(0,1)`); `det M = 1`, `trace M = a*b - 2`, char poly `λ² - (a*b-2)λ + 1`, and Cayley–Hamilton
holds exactly: `M² = (a*b-2)·M - I` for **all** integer `a,b`. `s1 a`, `s2 b` are involutions.
`det (cartan a b) = 4 - a*b` for all `a,b ∈ ℤ`.

## Per-statement table

| # | statement | standard fact it names | verdict | evidence | correction |
|---|-----------|------------------------|---------|----------|------------|
| 1 | `cartan_det (a b : ℤ) : (cartan a b).det = 4 - a*b` | Determinant of the rank-2 (generalised) Cartan matrix `[[2,-a],[-b,2]]`, the quantity behind the finite/affine/indefinite trichotomy by principal minors: for `a,b ≥ 1`, finite type iff `ab ≤ 3`, affine iff `ab = 4`, indefinite iff `ab > 4` | **matches** | Computation: `det = 2·2 - (-a)(-b) = 4 - a*b`, exact for all `a,b ∈ ℤ` (no hypotheses needed — it is a matrix identity, not a GCM statement, so none are missing; not vacuous). Literature: Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Ch. 4 ("A Classification of GCMs", pp. 47–58), **Ex. 4.1.3** (exactly this rank-2 matrix: finite/affine/indefinite iff `ab ≤ 3` / `= 4` / `> 4`) and **Thm 4.2.4** (finite iff all principal minors > 0; affine iff `det = 0` and proper principal minors > 0); Bourbaki, *Lie Groups and Lie Algebras*, Ch. VI §1 no. 5 (Cartan matrix). Section numbers verified via web (Cambridge chapter listing; Klesh's lecture notes reproducing Kac's numbering 4.1.3/4.2.4; Wikipedia "Cartan matrix" restates Thm 4.2.4) | None for the statement. Optional docstring remark in `Targets.lean`: `cartan a b` is a GCM in the strict sense (Kac Def. 4.1.1: `a_ij ≤ 0`, `a_ij = 0 ⟺ a_ji = 0`) only for `a,b ≥ 0` with matched zeros; "off-diagonal magnitudes" presumes that. The determinant identity itself is correctly stated for all `a,b : ℤ` |
| 2 | `finite_exact_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*b ≤ 3) : (a*b = 1 → HasExactPeriod (step a b) 3) ∧ (a*b = 2 → … 4) ∧ (a*b = 3 → … 6)` | In the rank-2 Coxeter/Weyl group with Cartan integers `(a,b)`, the Coxeter element `s₁s₂` has order `m` with `ab = 4cos²(π/m)`: order 3 for `A₂ = I₂(3)` (`ab=1`), 4 for `B₂ = I₂(4)` (`ab=2`), 6 for `G₂ = I₂(6)` (`ab=3`); crystallographic rank-2 `m ∈ {2,3,4,6}` | **matches** | Computation: for all five pairs `(1,1),(1,2),(2,1),(1,3),(3,1)` (exactly the pairs with `a,b ≥ 1, ab ≤ 3`), `M^n = I` for `n = 3,4,6` resp. per product, no smaller positive power is `I`, and for each `0 < m < n` an integer witness `x ∈ ℤ²` with `M^m x ≠ x` exists — so `HasExactPeriod (step a b) n` holds; `HasExactPeriod f n` is exactly "order of the map `f` is `n`" (first conjunct = `f^n = id`, second = no smaller universal period), which equals the order of the Weyl-group Coxeter element since the action on the root lattice `ℤ×ℤ` is faithful. Literature: Humphreys, *Reflection Groups and Coxeter Groups*, §5.3–5.4 (geometric representation faithful; `st` has order `m(s,t)`), §6.4/§6.6 (finite and crystallographic Coxeter groups; rank-2 crystallographic `m ∈ {2,3,4,6}`; TOC pp. 108, 132–135 verified via web); `ab = 4cos²(π/m)` (Cartan product vs Coxeter exponent) — verified via secondary source (Vinberg's theorem as quoted in UBC Coxeter notes), also implicit in Humphreys §6.6 / Bourbaki Ch. VI §1 no. 5; Kac Ex. 4.1.3 (`ab ≤ 3` finite). Quantifier order is fine: hypotheses precede the conjunction; per pair exactly one antecedent fires (`ab ∈ {1,2,3}`), and the implications map `1→3, 2→4, 3→6` correctly (not swapped); not vacuous. The period depends only on `ab` (char poly depends only on `trace = ab-2`, `det = 1`), so quantifying over all five representatives rather than one per product is correct and non-redundant | None. Docstring "3 for A₂, 4 for B₂, 6 for G₂" is correct. Prose finding (not the statement): the module docstring of `Statements.lean` cites "LIMITATIONS bullet 2" for T2; the five-pairs discussion is **bullet 3** of `LIMITATIONS.md` (bullet 2 is about the model not being proved a faithful Coxeter representation) — mislabeled pointer |
| 3 | `affine_unipotent (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a*b = 4) (v : V) : step a b (step a b v) = 2 • step a b v - v` | At `ab = 4` the rank-2 Cartan matrix is of **affine type** (the three representatives `(1,4),(2,2),(4,1)`, all `Ã₁`), and the Coxeter element of the affine rank-2 Weyl group is unipotent on the root lattice: `(T - I)² = 0` (equivalently `T² = 2T - I`, char poly `(λ-1)²` with `T ≠ I`), hence linear drift `Tⁿv = v + n(Tv - v)` and no positive period | **matches** | Computation: for each of `(1,4),(2,2),(4,1)`, `(M-I)² = 0` and `M² = 2M - I` exactly (symbolically, all `v`), `M ≠ I`; drift formula `Mⁿv = v + n(Mv - v)` verified for `n = 0..5`; `Mⁿ(1,0) ≠ (1,0)` for `n = 1..8`. The stated pointwise identity is exactly `(T² - 2T + I)v = 0 ⟺ (T-I)²v = 0`. Literature: Kac Ch. 4, Ex. 4.1.3 and Thm 4.2.4 (`ab = 4` ⟺ affine type, `det = 0` + proper principal minors `2,2 > 0`); Humphreys §6.5 "Affine Coxeter groups" (p. 133; `I₂(∞)` = infinite dihedral, product of the two generators of infinite order); Bourbaki Ch. VI §2 "Affine Weyl group" (p. 186) — section TOC verified via web. Hypotheses `1 ≤ a, 1 ≤ b, ab = 4` pick out exactly the three affine GCM representatives; not vacuous. (The identity in fact holds for **all** integer `a,b` with `ab = 4` by Cayley–Hamilton, so the hypotheses are the mathematically relevant ones, not a restriction that weakens anything) | None. Docstring "(T - 1)² = 0" matches the pointwise statement exactly |

## True-but-not-what-it-says / prose findings

1. `cartan_det` is an identity for all `a,b ∈ ℤ`, including inputs for which `cartan a b` is not a
   GCM (e.g. `a = 0, b ≠ 0`, where the zero-matching axiom `a_ij = 0 ⟺ a_ji = 0` fails). The
   sign-of-determinant reading (`4 - ab > 0` ⟺ finite) is only valid under the GCM hypotheses —
   which is exactly why `finite_exact_period` carries `1 ≤ a, 1 ≤ b`. `LIMITATIONS.md` states this
   caveat correctly, and I verified the underlying phenomenon computationally: for `a = 0, b ≠ 0`,
   `det cartan = 4 > 0` yet `step 0 b` has `(T+I)² = 0`, `T ≠ -I`… i.e. infinite order on `(1,0)`.
2. `LIMITATIONS.md` bullet 3 arithmetic checks: the five pairs with `1 ≤ a, b, ab ≤ 3` are exactly
   `(1,1),(1,2),(2,1),(1,3),(3,1)` — count 5 and list correct. The "characteristic-polynomial
   identity `step² = (a*b - 2) • step - 1`" and char poly `λ² - (a*b-2)λ + 1` verified exactly by
   sympy for symbolic `a,b` (Cayley–Hamilton residual is the zero matrix).
3. `Statements.lean` module docstring: "T2 … — LIMITATIONS bullet 2" is a mislabeled cross-reference
   (the five-pairs bullet is bullet 3; the closed-items section also covers it). "T3 … all three
   representatives" is correct: `(1,4),(2,2),(4,1)`.
4. `README.md` result 2 prose: products `ab = 0,1,2,3` with representatives `(0,0),(1,1),(1,2),(1,3)`
   give periods `2,3,4,6` — verified (`step 0 0 = -I` has exact period 2; orders 3,4,6 as above).
   Result 3 prose about `finite_exact_period` / `affine_unipotent` matches what the statements say.
   Badge/table arithmetic `56 = 22 + 22 + 12` is consistent (`RankTwoCertificate.lean` contains
   exactly 22 `theorem`s).
5. `LIMITATIONS.md` sentence "The bilinear form takes the value `a*y*(4 − a*b)` at `(a, 2)`"
   (about m3's `tits_vanishes_at_four`, but prose in a file I read): verified — the quadratic form
   gives `Q(a,2) = 2a(4-ab) = a·y·(4-ab)` at `y = 2`. The `titsForm` docstring in `Targets.lean`
   ("symmetrised Tits form … positive definite exactly on `0 < ab < 4`, 1-dim radical at `ab = 4`,
   indefinite above", for `a,b > 0`) is also correct: its matrix `[[2b,-ab],[-ab,2a]] = diag(b,a)·cartan`
   is the standard symmetrisation, `det = ab(4-ab)`, and its eigenvalues are positive for all five
   finite pairs (computed: `1,3`; `3±√5`; `4±√13`).
6. Golden-ratio prose in `RankTwoCertificate.lean` header (m4's statement area): verified
   `4cos²(π/5) = (3+√5)/2` exactly, and `(3+√5)/2 ∈ (2,3)`, so "not an integer" and "between 2
   and 3" are correct.

## Sources: verified vs memory

- **Verified via web this session**: Kac 3rd ed. Ch. 4 title/pages (Cambridge), and the numbering
  **Ex. 4.1.3** (rank-2 trichotomy `ab ≤ 3 / = 4 / > 4`) and **Thm 4.2.4** (principal-minor
  criterion: finite iff all principal minors > 0; affine iff `det = 0` and proper principal minors
  > 0) as reproduced in Klesh's lecture notes on Kac's book; Humphreys' TOC (Ch. 5 §5.3 geometric
  representation p. 108; Ch. 6: §6.4 finite, §6.5 affine, §6.6 crystallographic, pp. 129–135;
  `I₂(m)` = dihedral of order `2m` as the rank-2 example); Bourbaki Ch. IV–VI TOC (Cartan matrix
  Ch. VI §1 no. 5; Coxeter transformations VI §1 no. 12 p. 182; affine Weyl group VI §2 p. 186;
  classification + Plate X "irreducible systems of rank 2" p. 291).
- **Cited from memory / secondary sources, not independently verified**: the exact wording of
  Humphreys §6.6 that rank-2 crystallographic `m ∈ {2,3,4,6}` (TOC verified; the fact is standard
  and was cross-checked against multiple secondary sources); the identity `ab = 4cos²(π/m)` linking
  Cartan product to Coxeter exponent (quoted from Vinberg's theorem in UBC Coxeter-group notes,
  consistent with Bourbaki VI §1 no. 5); that the order of `st` in `I₂(m)` is exactly `m` (built
  into the definition of a Coxeter system and proved in Humphreys §5.3–5.4 — section verified,
  sentence from memory).
- **All arithmetic** (determinants, traces, char polynomials, Cayley–Hamilton, orders of the
  five finite maps incl. the `∃x` witness clause, unipotence at the three `ab=4` representatives,
  drift formula, `a=0` infinite-order case, five-pair count, Tits-form values, golden identity)
  **verified by explicit sympy computation this session** (script run in the VM; output checked).

## Repository state

Not modified by me. All my file/shell operations were reads; `git status --porcelain` output
(`M LIMITATIONS.md`, `M README.md`, `M RankTwoClassification.lean`, `M swarm/RESULT.md`,
`M swarm/Statements.lean`, `M swarm/TASK.md`, `M swarm/Targets.lean`, `?? swarm/AUDIT.md`)
predates my session (file mtimes 21:31:35–21:32:44 vs. my first command later; I issued no writes).
My only output file is this one:
`/workspace/nucleus/work/projects/p-870b05c7d9a34cc6a7491c6863177ba6/repo/.ultramath/smwb7g95j/m1/audit-report.md`
