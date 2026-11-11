# Provenance of the 23 frozen statements

For each statement: the repository lemmas its proof is built from, the Mathlib facts its proof term
mentions, and the mathematical source it is checked against. Extraction from the compiled module,
not from memory.

## Method, and its limits

`#print` on each declaration of `RankTwoClassification.lean` yields the elaborated proof term; the
identifiers in that term are then split into this repository's own declarations and external ones.

The first attempt used the kernel environment directly (`ConstantInfo.value?` + `getUsedConstants`),
which is the obvious way and does not work here: for theorems imported from another module Lean
returns no value at all, and even for declarations in the same module the query came back empty.
That is worth stating because it silently produced a table with every dependency column blank
except the types — a wrong answer that looked like a complete one. Parsing `#print` gives the term
that is actually stored.

Limits, stated so a reviewer knows what the columns do and do not mean:

* **One level.** A Mathlib lemma's own dependencies are not followed. "Uses
  `QuadraticForm.sigPos_add_finrank_le_of_nonpos`" does not say what that lemma rests on.
* **Textual.** Identifier matching on a printed term can catch a name mentioned in a `have` type
  and miss one the elaborator inlined, and can see a notation's expansion. It is a good index, not
  a proof of minimality.
* **Plumbing excluded.** Typeclass instances, coercions and core constructors are dropped from the
  columns to keep them readable. They are in the term; they are not in this table.
* **Ideas are not proof terms.** Nothing here records where a route came from. That is
  `RESULT.md` and `AUDIT.md`.

## The statements

| # | Statement | Repository lemmas | Mathlib facts mentioned | Source |
|---|---|---|---|---|
| 1 | `cartan_det` | — | `Matrix.det_fin_two` | Kac Ch. 4 (generalised Cartan matrices); Bourbaki VI §1 no. 5 |
| 2 | `finite_exact_period` | — | — | Humphreys Ch. 1 §1.1 (`I₂(m)`), Ch. 6 (finite; crystallographic `m ∈ {2,3,4,6}`); Bourbaki IV §1 |
| 3 | `affine_unipotent` | `step_sq_char` | — | Kac Ch. 4 (affine type: `det = 0`, proper principal minors > 0); Humphreys Ch. 6 §6.5 |
| 4 | `affine_iterate` | `affine_unipotent`, `step_add`, `step_smul`, `step_sub` | — | no independent source — formal consequence of `affine_unipotent` |
| 5 | `affine_no_positive_period` | `affine_iterate` | — | Bourbaki IV §1 no. 2 (`m = ∞`, infinite dihedral) |
| 6 | `zero_product_iterate` | — | — | none — `(0,b)`, `b ≠ 0`, is not a generalised Cartan matrix |
| 7 | `zero_product_no_positive_period` | `zero_product_iterate`, `zero_product_odd_iterate` | — | none — a negative control for Kac's criterion outside the GCM class |
| 8 | `zero_partner_no_positive_period` | `zero_partner_iterate`, `zero_partner_odd_iterate` | — | none — mirror of the previous one |
| 9 | `tits_positive_definite` | — | — | Kac Ch. 2 (invariant form), Ch. 4 (finite type criterion) |
| 10 | `tits_semidefinite_at_four` | — | — | Kac Ch. 4 (affine type: positive semidefinite of corank 1) |
| 11 | `tits_vanishes_at_four` | — | — | Kac Ch. 4 (affine type) |
| 12 | `tits_negative_above_four` | — | — | Kac Ch. 4 (indefinite type) |
| 13 | `tits_radical_at_four` | — | — | Kac Ch. 4 (affine: radical of corank 1) |
| 14 | `tits_degenerate_at_four` | `tits_radical_at_four` | — | Kac Ch. 4 (degenerate invariant form at the boundary) |
| 15 | `tits_posDef_iff_le_three` | `tits_posDef_imp_le_three`, `tits_positive_definite` | — | Kac Ch. 4, the principal-minor criterion read in both directions |
| 16 | `tits_semidef_iff_le_four` | `tits_positive_definite`, `tits_semidef_imp_le_four`, `tits_semidefinite_at_four` | — | Kac Ch. 4, the same criterion for the semidefinite bound |
| 17 | `tits_signature_below_four` | `posDef_on_top_iff` | `Module.finrank`, `Module.finrank_fin_fun`, `QuadraticForm.sigPos_add_finrank_le_of_nonpos`, `QuadraticMap.neg_apply`, `finrank_top`, `le_sigPos_of_posDef` … (+3) | Kac Ch. 4 (finite type, signature `(n,0)`); Mathlib `sigPos`/`sigNeg` |
| 18 | `tits_signature_at_four` | `tits_semidefinite_at_four`, `tits_vanishes_at_four` | `Module.finrank`, `Module.finrank_fin_fun`, `QuadraticForm.sigPos_add_finrank_le_of_nonpos`, `QuadraticMap.map_smul`, `QuadraticMap.neg_apply`, `QuadraticMap.restrict_apply` … (+6) | Kac Ch. 4 (affine type, signature `(n−1,0)` with a one-dimensional radical) |
| 19 | `tits_radical_finrank_at_four` | `tits_signature_at_four` | `Module.finrank`, `Module.finrank_fin_fun`, `QuadraticForm.sigPos_add_sigNeg_add_radical`, `QuadraticMap.radical`, `sigNeg`, `sigPos` | Kac Ch. 4 (corank 1), via Mathlib's inertia identity |
| 20 | `tits_radical_eq_span_at_four` | `mem_radical_at_four`, `tits_radical_finrank_at_four` | `Module.finrank`, `QuadraticMap.radical`, `Submodule.eq_of_le_of_finrank_eq`, `Submodule.span_singleton_le_iff_mem`, `finrank_span_singleton` | Kac Ch. 4 (the null root spans the radical) |
| 21 | `tits_signature_above_four` | `tits_negative_above_four` | `Module.finrank`, `Module.finrank_fin_fun`, `QuadraticForm.sigPos_add_finrank_le_of_nonpos`, `QuadraticMap.map_smul`, `QuadraticMap.neg_apply`, `QuadraticMap.restrict_apply` … (+6) | Kac Ch. 4 (indefinite type, signature `(n−1,1)`); Mathlib `sigPos`/`sigNeg` |
| 22 | `tits_indefinite_above_four` | `tits_negative_above_four` | — | Kac Ch. 4 (indefinite type: the form takes both signs) |
| 23 | `golden_product_eq_four_cos_sq` | — | `Real.cos`, `Real.cos_pi_div_five` | trigonometry (`cos(π/5) = (1+√5)/4`); the `H₂ = I₂(5)` context is not formalized |

## The helper lemmas underneath

| Lemma | Repository lemmas | Mathlib facts mentioned |
|---|---|---|
| `mem_radical_at_four` | `titsQF_shift`, `tits_vanishes_at_four` | `QuadraticMap.mem_radical_iff'`, `QuadraticMap.radical` |
| `pair_a_two_ne_zero` | — | — |
| `pair_ne_zero_of_ne_zero` | — | — |
| `posDef_on_top_iff` | `pair_ne_zero_of_ne_zero`, `tits_positive_definite` | `QuadraticMap.restrict`, `QuadraticMap.restrict_apply` |
| `step_add` | — | — |
| `step_smul` | — | — |
| `step_sq_char` | — | — |
| `step_sub` | — | — |
| `titsBilin_self` | — | — |
| `titsForm_shift` | — | — |
| `titsQF_shift` | `titsForm_shift` | — |
| `tits_posDef_imp_le_three` | `pair_a_two_ne_zero`, `tits_negative_above_four`, `tits_vanishes_at_four` | — |
| `tits_semidef_imp_le_four` | `tits_negative_above_four` | — |
| `zero_partner_iterate` | — | — |
| `zero_partner_odd_iterate` | `zero_partner_iterate` | — |
| `zero_product_odd_iterate` | `zero_product_iterate` | — |

## Reading the table against `AUDIT.md`

Three statements have no literature source, and that is deliberate rather than an omission: the
`zero_*` trio treats pairs `(0, b)` with `b ≠ 0`, which violate the generalised-Cartan-matrix
condition `a_ij = 0 ⟺ a_ji = 0`. There is no theorem in Kac to match them against, because they are
not Coxeter data; their role is to show that `4 − ab > 0` does not by itself give finiteness. A
reviewer should check that they say that, not that they say something in a book.

Everything else traces to Kac Ch. 4 (the finite/affine/indefinite trichotomy by principal minors),
with Ch. 2 for the invariant form, and to Humphreys Ch. 1 §1.1 / Ch. 6 or Bourbaki IV §1 for the
rank-two Coxeter side. Chapter and section level is what the audits could verify; the proposition
numbering inside those books is marked unverified in `AUDIT.md`.

