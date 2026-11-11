# Reviewer packet: twelve statements, checked against the literature

For an algebraist who has not worked on this repository. Time: about 30–45 minutes for the twelve
statements of the first campaign, 50–70 for all eighteen. You are not
asked to read proofs or to know Lean. You are asked one thing: **does each statement say the
standard mathematical fact its name and docstring claim, under the hypotheses written?**

If you can do that, this repository stops resting on machine and language-model readings for
statements 4–12, and `swarm/AUDIT.md` gets a human name against each verdict.

## What you are given, and what is already done

The objects are five definitions. `V = ℤ × ℤ`, and for integers `a, b`:

```lean
s1 a (x, y) = (-x + a*y, y)              -- simple reflection 1
s2 b (x, y) = ( x,     b*x - y)          -- simple reflection 2
step a b    = s1 a ∘ s2 b                -- the Coxeter element
iter f n    = f iterated n times
HasExactPeriod f n ⇔ (∀ x, iter f n x = x) ∧ ∀ m, 0 < m → m < n → ∃ x, iter f m x ≠ x
cartan a b  = !![2, -a; -b, 2]           -- rank-two Cartan matrix, off-diagonal magnitudes a, b
titsForm a b x y = 2*b*x² - 2*(a*b)*x*y + 2*a*y²   -- symmetrised invariant form, Gram = diag(b,a) * cartan
titsBilin a b u v = 2b·u₁v₁ - ab(u₁v₂ + u₂v₁) + 2a·u₂v₂        -- its polar form
```

`HasExactPeriod f n` is "the map `f` has exact period `n`". `titsForm` is the quadratic form of
`diag(b,a) * cartan a b`.

Already done, so that you do not have to do it: the twelve propositions are machine-checked and
replayed in an independent kernel checker on every push, with every axiom audited; `cartan` has
been identified in Lean with Mathlib's Bourbaki-plate matrices `A 2`, `C 2`, `B 2`, `G₂` and
`G₂ᵀ`; the arithmetic in each statement has been checked symbolically and by brute force; and the
statement texts have been read independently by two language models (see `swarm/AUDIT.md`). What
none of that establishes is **meaning** — whether the proposition is the theorem you would state.

## The twelve, and the question for each

The Lean statements are in `swarm/Statements.lean`; they are reproduced in plain form here.

| # | Statement | What it says | Read against | The question for you |
|---|---|---|---|---|
| 1 | `cartan_det` | `det(cartan a b) = 4 − a·b`, for all `a, b ∈ ℤ` | Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 (classification of generalised Cartan matrices); Bourbaki, *Lie* Ch. VI §1 | Is a matrix identity with no hypotheses the right thing to state, or should it carry the GCM hypotheses? |
| 2 | `finite_exact_period` | for `1 ≤ a, b` and `a·b ≤ 3`: exact period 3 if `a·b = 1`, 4 if `= 2`, 6 if `= 3` | Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 1 §1.1 (`I₂(m)`; the product of the two simple reflections is a rotation through `2π/m`, order `m`), Ch. 6 (crystallographic `m ∈ {2,3,4,6}`); Bourbaki Ch. IV §1 | Is "exact period of the map on `ℤ²`" the right formalisation of "order of the Coxeter element"? Does that need the action to be faithful, and is that the reviewer-relevant gap? |
| 3 | `affine_unipotent` | at `a·b = 4`: `step² v = 2·step v − v`, i.e. `(T − 1)² = 0` | Kac Ch. 4 (affine type: `det = 0`, proper principal minors `> 0`); Humphreys Ch. 6 §6.5 | Is unipotence the right statement of the affine case here, or should it be about the affine Weyl group directly? |
| 4 | `affine_iterate` | at `a·b = 4`: `Tⁿ v = v + n·(T v − v)` | follows from 3 | Any hidden assumption in passing from `(T−1)² = 0` to the iterate? |
| 5 | `affine_no_positive_period` | at `a·b = 4` and `n > 0`: `Tⁿ(1,0) ≠ (1,0)` | Bourbaki Ch. IV §1 no. 2 (`m = ∞`, infinite dihedral) | A single witness vector rules out `Tⁿ = id`. Is that the right strength, given the map fixes a line pointwise? |
| 6 | `zero_product_iterate` | with `a = 0`: the square of the step is the shear `(x, y) ↦ (x, y − 2bx)` | — (no source: this pair is not a generalised Cartan matrix) | Is it right to include a case the literature does not treat as Coxeter data? |
| 7 | `zero_product_no_positive_period` | with `a·b = 0` and `b ≠ 0`: `Tⁿ(1,0) ≠ (1,0)` | — | Is "`4 − ab > 0` alone does not give finiteness" the honest and useful reading? |
| 8 | `zero_partner_no_positive_period` | the mirror case, on the witness `(0,1)` | — | same |
| 9 | `tits_positive_definite` | `1 ≤ a, b`, `a·b ≤ 3`, `(x,y) ≠ 0` ⟹ `titsForm a b x y > 0` | Kac Ch. 2 (invariant form), Ch. 4 (finite type criterion) | Is `titsForm` the symmetrised form you would use, and are the hypotheses exactly the finite side? |
| 10 | `tits_vanishes_at_four` | at `a·b = 4`: `titsForm a b a 2 = 0` | Kac Ch. 4; the rank-two trichotomy | Does the *name* promise more than the proposition (radical membership vs vanishing)? |
| 11 | `tits_negative_above_four` | at `a·b > 4`: `titsForm a b a 2 < 0` | Kac Ch. 4 (indefinite type) | Same: negativity at one vector is not indefiniteness. Is that distinction drawn correctly where the repository claims it? |
| 12 | `golden_product_eq_four_cos_sq` | `4cos²(π/5) = (3+√5)/2` | trigonometry; `H₂ = I₂(5)` | Is it acceptable to prove only the arithmetic and to say in `LIMITATIONS.md` that the `H₂` geometry is not formalized? |
| 13 | `tits_semidefinite_at_four` | at `a·b = 4`: `0 ≤ titsForm a b x y` for all `x, y` | Kac Ch. 4 (affine type: psd of corank 1) | With `tits_vanishes_at_four` this makes the form degenerate. Is nonnegativity plus a zero the right way to say "degenerate", or should radical membership be proved separately? |
| 14 | `tits_indefinite_above_four` | at `a·b > 4`: the form takes both signs | Kac Ch. 4 (indefinite type) | Is "both signs" the right definition of indefinite here, and does the pair of witnesses (`(1,0)` and `(a,2)`) carry it? |
| 15 | `tits_radical_at_four` | at `a·b = 4`: `B((a,2), w) = 0` for every `w` | Kac Ch. 4 (affine: radical of corank 1) | Is `B` here the polar form of the Tits form, and is `(a,2)` the right radical vector, or should it be normalised? |
| 16 | `tits_degenerate_at_four` | at `a·b = 4`: `∃ v ≠ 0, ∀ w, B v w = 0` | Kac Ch. 4 | Is this the standard statement that the form is degenerate, and does it need corank exactly 1 stated separately? |
| 17 | `tits_posDef_iff_le_three` | the form is positive off the origin iff `a·b ≤ 3` | Kac Ch. 4, the principal-minor criterion | This is the converse that makes the criterion an iff. Does proving it from the two excluded cases (`a·b = 4` and above) carry the same content as Kac's principal-minor argument? |
| 18 | `tits_semidef_iff_le_four` | the form is nonnegative everywhere iff `a·b ≤ 4` | Kac Ch. 4 | Same question for the affine bound. |

## What to send back

Copy `swarm/review/TEMPLATE.md`, fill one row per statement, and put it in `swarm/review/` with
your name and the date. The verdict column takes one of: **matches / weaker / stronger /
misleading as named / false as stated**, and the final column any correction to the statement, its
docstring, or a README/LIMITATIONS sentence.

A verdict of "matches" for all twelve is a perfectly good outcome — it is the outcome the two
model passes reached, and a human confirming it is worth more than a third model saying so.

## What is deliberately not asked

- Not to check the proofs. They are kernel-checked and CI-replayed; if a proof were wrong the
  build would fail.
- Not to check the arithmetic. It has been checked symbolically and by brute force, and the
  scripts are in `swarm/AUDIT.md` §7.
- Not to agree with the docstrings. The four defects the model passes found were all in prose, not
  in propositions; that is where a reader earns their keep.

## If you find a defect

Say so in the verdict column and stop there — a corrected statement would need re-proving and
re-freezing, which is a separate piece of work. Two precedents are in the git history: the
"six pairs" count and the "spans the radical" docstring, both fixed by a reader who never touched
a proof.
