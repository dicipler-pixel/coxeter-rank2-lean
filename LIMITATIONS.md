# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* This is rank two only. The finite/affine classification of Coxeter groups in general is not
  formalized.
* The period certificates use one integral representative per product `ab`; other
  representatives with the same product are not treated separately.
* The golden product is shown non-integral; its identification with `4cos²(π/5)`, the Cartan
  product of `I₂(5)`, and the full `H₂` geometry are not formalized.
* `product_lt_four_cases`, `finite_margin_positive` and `affine_margin_zero` are arithmetic
  bookkeeping: `p < 4 → p ∈ {0, 1, 2, 3}`, `p < 4 → 0 < 4 − p` (one direction only) and
  `4 − 4 = 0`. The link from the Cartan determinant `4 − ab` to finiteness, mentioned in their
  docstrings, is not formalized.
