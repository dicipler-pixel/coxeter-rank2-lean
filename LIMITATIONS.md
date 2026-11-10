# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* This is rank two only. The finite/affine classification of Coxeter groups in general is not
  formalized, and for rank ≥ 3 nothing is claimed.
* `RankTwoClassification.lean` proves the rank-two boundary in the **integral reflection model**
  of `RankTwoCertificate` (`s₁`, `s₂` acting on `ℤ × ℤ`). It does not prove that those
  reflections generate a Coxeter group, nor that the model is faithful to the Coxeter
  presentation. The dihedral isomorphism is a separate result in `DihedralBridge.lean` and does
  not transfer this representation.
* `finite_exact_period` quantifies over `1 ≤ a, b` with `a*b ≤ 3`, which leaves five pairs —
  `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)`. It is a finite statement about those five,
  established by case analysis, not a general theorem in `a` and `b`. The affine statements at
  `a*b = 4` **are** general in `(a, b)`: they follow from the characteristic-polynomial identity
  `step² = (a*b − 2) • step − 1`.
* `tits_vanishes_at_four` proves that the symmetrised Tits form vanishes at `(a, 2)` when
  `a*b = 4`. That `(a, 2)` spans the radical of the associated bilinear form, that the form is
  positive semidefinite at `a*b = 4`, and that it is indefinite above are not formalized. The
  bilinear form takes the value `a*y*(4 − a*b)` at `(a, 2)`, so radical membership is a one-line
  computation this release does not include.
* The golden product is proved to equal `4cos²(π/5)`. That this number is the Cartan product of
  `I₂(5)`, and the full `H₂` geometry, are not formalized.
* `product_lt_four_cases`, `finite_margin_positive` and `affine_margin_zero` are arithmetic
  bookkeeping: `p < 4 → p ∈ {0, 1, 2, 3}`, `p < 4 → 0 < 4 − p` (one direction only) and
  `4 − 4 = 0`. For the finite side they are superseded by `RankTwoClassification.lean` and kept
  for the record.

## Listed as open in earlier releases, now closed

* *"The period certificates use one integral representative per product `ab`; other
  representatives with the same product are not treated separately."* Closed by
  `finite_exact_period` and the three `affine_*` statements.
* *"The link from the Cartan determinant `4 − ab` to finiteness is not formalized."* Closed in
  rank two: the determinant is `4 − a*b` (`cartan_det`) and the characteristic polynomial is
  `λ² − (a*b − 2)λ + 1`, so `a*b = 4` is exactly unipotence and `a*b ≤ 3` is exactly a finite
  period. Closing it made one thing precise that the old wording hid: `4 − ab > 0` alone does
  not give finiteness, because `ab = 0` with a nonzero partner has infinite order. That is why
  the finite statement carries `1 ≤ a, 1 ≤ b`.
* *"The golden product is identified with `4cos²(π/5)` only half-way."* Closed as arithmetic
  (`golden_product_eq_four_cos_sq`); the geometry behind it is not.
