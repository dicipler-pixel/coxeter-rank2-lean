# Audit — statement 5, `affine_no_positive_period`

**Statement as frozen in `swarm/Statements.lean`** (docstring: *"Hence no positive power of an
affine representative is the identity."*):

```lean
theorem affine_no_positive_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (hn : 0 < n) : iter (step (a : ℤ) (b : ℤ)) n (1, 0) ≠ (1, 0)
```

## Verdict

| statement | standard fact it appears to name | verdict | evidence | correction needed |
|---|---|---|---|---|
| `affine_no_positive_period`: for every `a, b ≥ 1` with `a*b = 4`, the orbit of `(1,0)` under `step a b = s₁s₂` never returns to `(1,0)` at a positive time | In the rank-two Coxeter group with `a₁₂a₂₁ = 4` (`m = ∞`, affine type `A₁⁽¹⁾`) the product `s₁s₂` has **infinite order** — no positive period; in the reflection representation it is a nontrivial unipotent element with linear drift `(s₁s₂)ⁿe₁ = e₁ + 2n(e₁+e₂)`. Bourbaki, *Lie Groups and Lie Algebras*, Ch. IV §1 no. 2 (dihedral groups; `m = ∞` is the infinite dihedral group) [not read directly]; Davis, *The Geometry and Topology of Coxeter Groups*, Lemma 6.12.3 (order of `ρᵢρⱼ` is `mᵢⱼ`, with the explicit `m = ∞` drift) [verified]; Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 (affine type ⟺ `det = 0` with a positive null vector) [criterion verified from the book's own Introduction §0.3] | **matches** — true, non-vacuous, and the standard fact follows from it. It is stated in the strictly *stronger* pointwise form: it pins the witness `(1,0)` (= the simple root `α₁`) instead of quantifying `∃ v`, so it also yields "no positive power of the map is the identity" | Computation and a Lean proof in `check5.lean`: `a*b = 4` gives `iter (step a b) n (1,0) = (2n+1, b·n)`, whose first coordinate is `2n+1 ≥ 3` for `n > 0`. At `a = b = 2` this is exactly Davis's `e₁ + 2n(e₁+e₂)`. The map-level corollary `iter (step a b) n ≠ id` is proved in the same file | None required. Optional: `ha`, `hb` are unused and derivable from `hab` (Lean's linter reports both); the name/docstring do not mention the witness `(1,0)` |

## What is true but not quite what it says

The statement is **pointwise at one vector**, not about the map, while the docstring ("Hence no
positive power of an affine representative is the identity") is a map-level claim. The implication
is immediate and is proved in `check5.lean` (`iter (step a b) n ≠ id`), so nothing is overstated;
but the literal content of the Lean proposition is "the point `(1,0)` is not periodic", and a reader
who supplies the natural map-level reading should know that it comes from a one-line inference, not
from the statement itself.

The witness is not decoration: a reading "no point has a positive period" would be **false**. For
`a*b = 4` the step fixes the line `{(x,y) | y = b·x/2}`, i.e. `(1,1)` for `(2,2)`, `(2,1)` for
`(4,1)`, `(1,2)` for `(1,4)` (checked in `check5.lean`), and `(0,0)` is fixed for every linear step.
So specifying `(1,0)` is necessary, and the choice is canonical rather than arbitrary: `(1,0)` is a
simple root of `s₁`, and the orbit of a root in the infinite dihedral/affine case is infinite.

Hypotheses: `ha, hb` are redundant. With `a, b : ℕ` and `a*b = 4` only `(1,4)`, `(2,2)`, `(4,1)`
occur, all with `a, b ≥ 1`; Lean reports both binders unused, and the proof in `check5.lean` never
uses them. All three pairs are generalised Cartan matrices of affine type in Kac's sense: with
`A = [[2,-a],[-b,2]]`, `Aδ = 0` for `δ = (a,2) > 0` exactly when `a*b = 4`; the asymmetric pairs
are the same Coxeter group `D_∞` in a different root normalisation (the standard symmetric
representative is `(2,2)`), so covering all three is legitimate, not an overreach.

Scope: only `a*b = 4` is claimed. `a*b > 4` (indefinite, `tr = a*b − 2 > 2`) also has infinite
order, but is correctly not claimed by a statement named *affine* — the statement should not be read
as "`a*b ≥ 4`". `HasExactPeriod f n` is a reasonable notion for a map (universal period plus
minimality) and is the right shape for the finite side, but a *negative* claim cannot be stated as
the negation of `HasExactPeriod f n` for one `n`: it needs `∀ n > 0, ¬(∀ v, iter f n v = v)`, i.e.
"no positive power is the identity", which is what the docstring says and what this statement yields.

Model versus group: `LIMITATIONS.md` already states that the integral model is not proved to be a
faithful representation of the Coxeter presentation. That gap does not affect this statement, which
needs only the concrete computation, and the "affine" in the name is itself a computation on the
Cartan matrix, not a faithfulness claim. It does mean, though, that "the affine rank-two Coxeter
group is infinite" is *not* obtained from this statement inside the repository: that inference needs
faithfulness (Tits) or the abstract dihedral argument, and `LIMITATIONS.md` says the
`DihedralBridge` isomorphism does not transfer this representation.

The statement is also a corollary of `affine_iterate` (the second step of T3); the implication does
check out, by the identical drift formula — so the three affine statements form a chain, with this
one the pointwise consequence of the other two.

## Checks run (evidence)

* `python3`/`sympy`: for each of `(1,4), (2,2), (4,1)`: matrix `[[ab−1, −a],[b, −1]]` with
  `tr = 2`, `det = 1`, characteristic polynomial `(λ−1)²`, `(M−I)² = 0`; orbit of `(1,0)` is
  `(3,4), (5,8), (7,12), …` / `(3,2), (5,4), (7,6), …` / `(3,1), (5,2), (7,3), …`, i.e.
  `(2n+1, bn)`; no `k ≤ 50` with `M^k = I` or `M^k(1,0) = (1,0)`; fixed space of `M` is one line
  (spanned by `(1,2)`, `(1,1)`, `(2,1)` respectively).
* `lean check5.lean`: compiles with exit status 0 (warnings only: two unused binders, one style
  linter note). It contains a self-contained copy of `V, s1, s2, step, iter`, the proof of the drift
  formula and of `affine_no_positive_period` itself (hypotheses exactly as in the frozen statement),
  plus the non-vacuity and fixed-point examples. `#print axioms` reports
  `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

## Blindness

I read only: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`,
`RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`. I did **not** open
`RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`,
`swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, any other file
under `swarm/review/`, or anything under `.ultramath/` outside my own directory. Disclosure: a
directory listing of the repository root showed me the *names* of the top-level entries
(`verification`, `FalseControls`, `.ultramath`, …); no forbidden file was opened or read.

## Sources: verified vs from memory

* **Verified** (read in the fetched PDF, `people.math.osu.edu/davis.12/davisbook.pdf`):
  M. W. Davis, *The Geometry and Topology of Coxeter Groups*, Definition 6.8.11 and eq. (6.21)
  (cosine matrix `cᵢⱼ = −cos(π/mᵢⱼ)`, with `mᵢⱼ = ∞` read as `cᵢⱼ = −1`); Lemma 6.12.3 ("the order of
  `ρᵢρⱼ` is `mᵢⱼ`", whose proof for `m = ∞` computes `(ρᵢρⱼ)ⁿ(eᵢ) = 2n(eᵢ+eⱼ) + eᵢ`, hence infinite
  order); §3.1, Example 3.1.3 (infinite dihedral group, product is a translation of infinite order),
  Lemma 3.1.5 and Example 3.1.6 (a dihedral group generated by two involutions is determined by the
  order `m` of their product; `m = ∞` means the relation `(st)^m` is omitted); Davis's bibliography,
  where `[29]` is Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, and Lemma 3.1.5 is
  attributed to `[29, Prop. 2, p. 2]`.
* **Verified, indirectly**: Bourbaki, Ch. IV §1 no. 2 is the section "Dihedral groups" beginning on
  p. 2 of Ch. IV, and Prop. 2 there is the dihedral characterisation cited by Davis; the section
  title and page were confirmed from the published table of contents. I did **not** read Bourbaki's
  text itself, so the exact wording of `m = ∞` is from Davis's rendering plus memory.
* **Verified from the book's own Introduction §0.3** (publisher sample PDF of Kac's
  *Infinite-Dimensional Lie Algebras*): the classification of GCMs into finite / affine /
  indefinite by the existence of `δ > 0` with `Aδ > 0`, `Aδ = 0`, `Aδ < 0`; affine entails
  `det A = 0` and non-negative principal minors. The rank-two equivalence `a*b = 4 ⟺` affine is my
  computation with this criterion, not a quoted theorem.
* **From memory, not verified**: Humphreys, *Reflection Groups and Coxeter Groups* — I checked an
  excerpt of §1.1 (only the finite `I₂(m)`, `m ≥ 3`, case: `s_αs_β` is rotation through `2π/m`), and
  did not verify Humphreys' treatment of `m = ∞`, so I do not rely on it. Kac's Ch. 4 numbering and
  Table `Aff 1` are recalled, not checked; I rely only on the criterion above.

## Repository

I did not modify the repository: `git status --porcelain` shows no changes at all (not even
untracked, since `.ultramath/` is ignored). My only writes are `check5.lean` and `audit-report.md`
in my own directory `.ultramath/smwbdn3j5/m1/`; the `.scratch/` directory of downloaded reference
material was deleted after use.
