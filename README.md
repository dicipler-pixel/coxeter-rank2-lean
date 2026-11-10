<div align="center">

# Rank-two Coxeter groups — Lean proofs

**The rank-two Coxeter group `I₂(m + 2)` is the dihedral group of order `2(m + 2)`, checked against Mathlib's own objects, with exact integral certificates for the finite and affine rank-two cases.**

[![Lean proof check](https://github.com/dicipler-pixel/coxeter-rank2-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/coxeter-rank2-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.33.0-blue)
![Theorems](https://img.shields.io/badge/theorems-56-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)

Jeromie Beasley

</div>

---

## The three results

**1. The dihedral isomorphism.** The canonical homomorphism from Mathlib's presented Coxeter
group `(CoxeterMatrix.I m).Group` to `DihedralGroup (m + 2)` is surjective, has trivial kernel via
a two-coset normal form in the presented group, and so is an isomorphism
(`toDihedral_surjective`, `hasDihedralNormalForm`, `toDihedral_injective`). The order
`2(m + 2)` is Mathlib's `DihedralGroup.nat_card` for the target group; it is not restated here.

**2. Finite versus affine in rank two.** With the integral reflections
`s₁(x, y) = (−x + a y, y)` and `s₂(x, y) = (x, b x − y)`, the crystallographic products
`ab = 0, 1, 2, 3`, represented by `(a, b) = (0, 0), (1, 1), (1, 2), (1, 3)`, give Coxeter elements
of exact period `2, 3, 4, 6`; the affine product `ab = 4`,
represented by `(2, 2)`, has linear drift and no positive period; and the golden product
`(3 + √5)/2` of `H₂ = I₂(5)` lies strictly between `2` and `3`, so it is not an integer
(`U2_exact` … `U6_exact`, `Uaff_iterate`, `Uaff_no_positive_period`,
`golden_product_not_integer`).

**3. The finite/affine boundary, for every representative.** In the integral reflection model of
`RankTwoCertificate`, every pair with `a, b ≥ 1` and `a*b ≤ 3` has the exact period its finite
type prescribes (`finite_exact_period`), and every pair with `a*b = 4` is unipotent with linear
drift and no positive period (`affine_unipotent`, `affine_iterate`, `affine_no_positive_period`).
A pair with `a*b = 0` and a nonzero partner has infinite order on an explicit vector
(`zero_product_no_positive_period`) — so `4 − a*b > 0` alone does not make the product finite.
The symmetrised Tits form of the Cartan matrix is positive definite on the finite side, vanishes
at `(a, 2)` at `a*b = 4`, and is negative there above (`tits_positive_definite`,
`tits_vanishes_at_four`, `tits_negative_above_four`). These are statements about the reflection
model; what they do and do not establish is set out in [`LIMITATIONS.md`](LIMITATIONS.md).

| File | Theorems | What it does |
| :--- | :-: | :--- |
| [`RankTwoCertificate.lean`](RankTwoCertificate.lean) | 22 | Integral reflection certificates: exact periods, affine drift, the golden obstruction |
| [`DihedralBridge.lean`](DihedralBridge.lean) | 22 | The isomorphism `(CoxeterMatrix.I m).Group ≃* DihedralGroup (m + 2)` |
| [`RankTwoClassification.lean`](RankTwoClassification.lean) | 12 | The finite/affine boundary for every representative, in the integral reflection model |
| | **56** | |

The theorem is mathematically standard; the contribution is a checked formalization against
Mathlib's actual `CoxeterMatrix.I` and `DihedralGroup`, a rank-two step toward a
computer-verified finite/affine Coxeter classification.

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml) on GitHub:

1. **Build**: every module compiles against Lean v4.33.0 and Mathlib `v4.33.0`.
2. **Independent replay**: every module is re-checked by Lean's separate kernel checker.
3. **Axiom audit**: every named theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`. No `sorry`, no project axioms, no `native_decide`.
4. **False control**: the claim that the affine element fixes `(1, 0)` (it sends it to `(3, 2)`) must fail to compile, for a mathematical reason.

```bash
lake exe cache get
lake build
python3 scripts/verify.py
```

## Licence, citation and AI use

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
