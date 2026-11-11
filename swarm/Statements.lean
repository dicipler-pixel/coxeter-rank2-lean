import Targets

/-!
# Frozen target statements: rank-two finite/affine classification

`LIMITATIONS.md` records what this library does not do. This file freezes the statements
that close three of its bullets, so that a submission is checked against a statement that
cannot drift. Bodies are `sorry` here on purpose and must be replaced in a submission;
`scripts/gate.py` compares each statement text against this file and refuses a submission
that changes one.

What each target closes:

* **T1** the Cartan determinant `4 - a*b`;
* **T2** *every* representative `(a, b)` with `a, b ≥ 1` and `a*b ≤ 3`, not one per
  product — see the five-pair bullet in `LIMITATIONS.md`;
* **T3** the affine side `a*b = 4` for all three representatives, by unipotence rather
  than by one worked example;
* **T4** the degenerate product `a*b = 0` with a nonzero partner has no positive power equal to
  the identity (`HasExactPeriod` is not claimed, and would be the wrong form here):
  `4 - a*b` alone does not decide finiteness of the product;
* **T5** the sign of the Tits form — positive definite for `1 ≤ a, b` with `a*b ≤ 3` (at
  `(0, 0)` the symmetriser degenerates and the form is identically zero), nonnegative at
  `a*b = 4` with `(a, 2)` in the radical of the bilinear form (so degenerate), and taking both
  signs above — and the converses hold, so the trichotomy is an if-and-only-if, with signature
  `(1, 1)` above the boundary — see the Tits bullet in `LIMITATIONS.md`;
* **T6** `4cos²(π/5) = (3+√5)/2`, the identification the golden paragraph only half makes.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-! ## T1 — the determinant -/

theorem cartan_det (a b : ℤ) : (cartan a b).det = 4 - a * b := by
  sorry

/-! ## T2 — finite side, every representative -/

/-- For every `a, b ≥ 1` with `a*b ≤ 3`, the Coxeter element has the exact period the
finite type prescribes: `3` for `A₂`, `4` for `B₂`, `6` for `G₂`. -/
theorem finite_exact_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    (a * b = 1 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 3) ∧
      (a * b = 2 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 4) ∧
        (a * b = 3 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 6) := by
  sorry

/-! ## T3 — affine side, every representative -/

/-- Every rank-two representative with `a*b = 4` is unipotent: `(T - 1)² = 0`. -/
theorem affine_unipotent (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) (v : V) :
    step (a : ℤ) (b : ℤ) (step (a : ℤ) (b : ℤ) v) = 2 • step (a : ℤ) (b : ℤ) v - v := by
  sorry

/-- Unipotence turned into the iterate: `Tⁿ v = v + n(T v - v)`, linear drift. -/
theorem affine_iterate (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (v : V) :
    iter (step (a : ℤ) (b : ℤ)) n v = v + (n : ℤ) • (step (a : ℤ) (b : ℤ) v - v) := by
  sorry

/-- Hence no positive power of an affine representative is the identity. -/
theorem affine_no_positive_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (hn : 0 < n) : iter (step (a : ℤ) (b : ℤ)) n (1, 0) ≠ (1, 0) := by
  sorry

/-! ## T4 — degenerate product `a*b = 0` with a nonzero partner -/

/-- With `a = 0`, the Coxeter step is `(x, y) ↦ (-x, b*x - y)`. For `b ≠ 0` its square is a
nonzero shear; at `b = 0` the step is the negation and the square is the identity. -/
theorem zero_product_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n) (x, y) = (x, y - 2 * (n : ℤ) * b * x) := by
  sorry

/-- So for `b ≠ 0` no positive power is the identity, although `a*b = 0 < 4`. -/
theorem zero_product_no_positive_period (b : ℤ) (hb : b ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step 0 b) n (1, 0) ≠ (1, 0) := by
  sorry

/-- The mirror case `b = 0`, `a ≠ 0`, on the witness `(0, 1)`. -/
theorem zero_partner_no_positive_period (a : ℤ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step a 0) n (0, 1) ≠ (0, 1) := by
  sorry

/-! ## T5 — the sign of the Tits form -/

/-- Finite side: the Tits form is positive definite. -/
theorem tits_positive_definite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3)
    (x y : ℝ) (h : (x, y) ≠ 0) : 0 < titsForm (a : ℤ) (b : ℤ) x y := by
  sorry

/-- Affine side, semidefinite: at `a*b = 4` the symmetrised form is nonnegative everywhere, which
together with its vanishing at `(a, 2)` makes it degenerate there. -/
theorem tits_semidefinite_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (x y : ℝ) : 0 ≤ titsForm (a : ℤ) (b : ℤ) x y := by
  sorry

/-- Affine side: `titsForm a b a 2 = -2 a (a*b - 4)`, so `(a, 2)` is a zero of the form at
`a*b = 4`. Radical membership is true but is not what this proves; see `Targets.titsForm`. -/
theorem tits_vanishes_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 = 0 := by
  sorry

/-- Indefinite side: the same vector makes the form negative once `a*b > 4`. -/
theorem tits_negative_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 < 0 := by
  sorry

/-- Affine side: at `a*b = 4` the vector `(a, 2)` is in the radical of the bilinear form. -/
theorem tits_radical_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (x y : ℝ) : titsBilin (a : ℤ) (b : ℤ) (a, 2) (x, y) = 0 := by
  sorry

/-- Affine side, the standard statement: the bilinear form is degenerate at `a*b = 4`. -/
theorem tits_degenerate_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    ∃ v : ℝ × ℝ, v ≠ 0 ∧ ∀ w : ℝ × ℝ, titsBilin (a : ℤ) (b : ℤ) v w = 0 := by
  sorry

/-- The finite side is exactly positive definiteness, not merely implied by it. -/
theorem tits_posDef_iff_le_three (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∀ x y : ℝ, (x, y) ≠ 0 → 0 < titsForm (a : ℤ) (b : ℤ) x y) ↔ a * b ≤ 3 := by
  sorry

/-- The affine side is exactly nonnegativity: semidefinite if and only if `a*b ≤ 4`. -/
theorem tits_semidef_iff_le_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∀ x y : ℝ, 0 ≤ titsForm (a : ℤ) (b : ℤ) x y) ↔ a * b ≤ 4 := by
  sorry

/-- Finite side, as a signature statement: below the boundary the form is positive definite on the
whole plane, so `sigPos = 2` and `sigNeg = 0`. -/
theorem tits_signature_below_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 2 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 0 := by
  sorry

/-- Affine side, as a signature statement: at the boundary the form is semidefinite with a
one-dimensional radical, so `sigPos = 1` and `sigNeg = 0`. -/
theorem tits_signature_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 0 := by
  sorry

/-- Affine side: the radical is exactly one-dimensional at the boundary, so with `sigPos = 1` and
`sigNeg = 0` the signature is `(1, 0)` in the strong sense. -/
theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  sorry

/-- Affine side, sharpest form: the radical is spanned by the vector `(a, 2)`. -/
theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  sorry


/-- Indefinite side, as a signature statement rather than a pair of witnesses: above the boundary
the form has signature `(1, 1)` — one positive and one negative dimension. -/
theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  sorry

/-- Indefinite side: above the boundary the form takes both signs, so it is indefinite. -/
theorem tits_indefinite_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    (∃ x y : ℝ, 0 < titsForm (a : ℤ) (b : ℤ) x y) ∧
      ∃ x y : ℝ, titsForm (a : ℤ) (b : ℤ) x y < 0 := by
  sorry

/-! ## T6 — the golden product -/

theorem golden_product_eq_four_cos_sq :
    4 * Real.cos (Real.pi / 5) ^ 2 = (3 + Real.sqrt 5) / 2 := by
  sorry

end OperatorFirst.CoxeterRankTwo
