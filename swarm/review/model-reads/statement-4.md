# Audit — statement 4, `affine_iterate`

Statement text audited (verbatim from `swarm/Statements.lean`):

```lean
/-- Unipotence turned into the iterate: `Tⁿ v = v + n(T v - v)`, linear drift. -/
theorem affine_iterate (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (v : V) :
    iter (step (a : ℤ) (b : ℤ)) n v = v + (n : ℤ) • (step (a : ℤ) (b : ℤ) v - v)
```

## Verdict

| statement | standard fact | verdict | evidence | correction needed |
| --- | --- | --- | --- | --- |
| `affine_iterate` — for `a b : ℕ`, `1 ≤ a`, `1 ≤ b`, `a*b = 4`, all `n : ℕ`, all `v : ℤ×ℤ`: `iter (step a b) n v = v + (n:ℤ) • (step a b v − v)`, docstring "Unipotence turned into the iterate: `Tⁿ v = v + n(T v − v)`, linear drift" | A unipotent endomorphism `T = 1 + N` with `N² = 0` (equivalently `T² = 2T − 1`) satisfies `Tⁿ = 1 + nN`, i.e. `Tⁿv = v + n(Tv − v)`: it acts as a translation and the n-th iterate translates n times. In rank two the Coxeter element `s₁s₂` is such a translation exactly in affine type (`a*b = 4`), which is why it has no positive period and, moreover, drifts linearly. | **matches** | (1) Exact computation: the matrix of `step a b` is `!![a*b−1, −a; b, −1]`, trace `a*b−2`, determinant `1`, characteristic polynomial `λ² − (a*b−2)λ + 1`; `N := T − 1` satisfies `N² = (a*b−4)·T` identically, and `det T = 1`, so `N² = 0 ⇔ a*b = 4`; the binomial theorem then gives the identity for every `n` and `v`. Verified symbolically for `n = 0…9` on all three pairs `(1,4), (2,2), (4,1)` by `check/compute.py`, and machine-checked in Lean 4 in `check/Audit.lean` (statement transcribed verbatim from `Statements.lean` over verbatim `V, s1, s2, step, iter` from `RankTwoCertificate.lean`): compiles with no `sorry`, `#print axioms affine_iterate` = `[propext, Classical.choice, Quot.sound]`. (2) `a*b = 4` with `a,b ≥ 1` is exactly the affine condition for `!![2,−a; −b,2]`, and in affine type the product of the two simple reflections is a translation: `r₀r_θ = t_{ν(θ∨)}` — Kleshchev, *Lectures on Infinite Dimensional Lie Algebras*, §4.1 Ex. 4.1.3 and §6.4 (6.9)–(6.10). (3) Sharpness: for `a*b ≠ 4`, `N² = (a*b−4)T ≠ 0` and the conclusion fails already at `n = 2`; e.g. `(a,b) = (1,3)`, `v = (0,1)`: `T²v = (−1,−2)` but `v + 2(Tv−v) = (−2,−3)`. Machine-checked as `not_affine_iterate_two`: at `n = 2` on `(0,1)` the conclusion forces `a*b = 4`. | None for correctness. Optional tightening: `ha`, `hb` are redundant (see below) and could be dropped, or stated over `a b : ℤ`; keeping them costs nothing and matches the surrounding statements. |

## True, but worth saying plainly

**The hypotheses `ha`, `hb` do no work.** In `ℕ`, `a*b = 4` already forces `a ≠ 0` and `b ≠ 0`, hence `1 ≤ a`, `1 ≤ b` (`one_le_of_mul_eq_four`, machine-checked); and the conclusion is true for *every* `a b : ℤ` with `a*b = 4`, including the negative pairs that are not generalised Cartan matrices (`affine_iterate_int`, machine-checked, same statement with `ℕ` and the two inequalities removed). Lean's own linter says of the audited declaration: "Variable name `ha` is not explicitly referenced" (and the same for `hb`). So statement 4 is a special case of "an integral `2×2` map with trace `2` and determinant `1` — a linearised translation — iterates by drift"; the `ℕ`/`≥1` carrier cuts it down to exactly the three affine rank-two representatives `(1,4), (2,2), (4,1)`. That restriction is what makes the statement one about Cartan matrices rather than about all integer matrices, so it is a deliberate narrowing, not a defect.

**Relative to statement 3 it adds no hypothesis and no risk.** At `n = 2` the conclusion reads `v + 2•(Tv − v) = 2•Tv − v`, which is literally `affine_unipotent`; conversely statement 3 plus ℤ-linearity of `step a b` (it is a matrix) gives the identity for all `n` by the binomial theorem, with no intermediate term surviving because `N² = 0`. So the brief's "no independent source — check the implication from statement 3" has a clean answer: the implication is exactly `(1+N)ⁿ = 1 + nN` when `N² = 0`, it is an identity, and it is where the content of "linear drift" lives. Statement 4 is the strongest of the three affine statements and the form `affine_no_positive_period` consumes.

**Not vacuous.** `a*b = 4` with `a,b ≥ 1` is satisfiable (three pairs), and the conclusion is strong: for the three pairs `N(1,0) = (2, b) ≠ 0`, so the formula makes every positive iterate of `(1,0)` differ from `(1,0)`; it is strictly stronger than "no positive period". Verified numerically: `(2,2)` gives `(1,0) ↦ (3,2) ↦ (5,4) ↦ (7,6)`, `(1,4)` gives `(3,4), (5,8), (7,12)`, `(4,1)` gives `(3,1), (5,2), (7,3)`.

**Minor.** The formula also holds for `n : ℤ` (since `det T = 1`, `T` is invertible); stating it over `ℕ` loses nothing that is used downstream. Nothing about the statement requires the action to be faithful, and `HasExactPeriod` is not used here.

**Name and docstring.** `affine_iterate` promises "the iterate in the affine case", and `hab : a*b = 4` is exactly the affine condition; the docstring promises "`Tⁿ v = v + n(T v − v)`, linear drift", which is exactly the proposition. Neither promises the affine root system, the null root, or a faithful affine Weyl group action — `LIMITATIONS.md` already records that the model is `ℤ × ℤ` and is not shown to be faithful to the Coxeter presentation, and that limitation is unchanged by this statement.

## Blindness

Files I opened, all on the allowed list: `swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`.

I did **not** open `RankTwoClassification.lean`, `swarm/Classification.lean`, `swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`, `swarm/REVIEW-PACKET.md`, `swarm/review/` (beyond the brief), or any file under `$REPO/.ultramath/` other than the files I created myself (`audit-report.md`, `check/Audit.lean`, `check/compute.py`).

## Sources: verified vs from memory

*Verified (this session):*
- All arithmetic and the iterate identity: `check/compute.py` (sympy, re-runnable) — matrix, trace, determinant, characteristic polynomial, `N² = (a*b−4)T`, the identity for `n = 0…9` on `(1,4), (2,2), (4,1)`, and the failure at `(1,3)`.
- Truth of the statement as written: `check/Audit.lean`, compiled with `lean` (Lean 4.33.1 / Mathlib on `LEAN_PATH`), no `sorry`, axioms clean. Note that the repository has no built `.olean`s, so the check uses the definitions of `V, s1, s2, step, iter` copied *verbatim* (mechanically extracted) from `RankTwoCertificate.lean` and the statement copied verbatim from `swarm/Statements.lean`; no definition was altered.
- Affine/indefinite trichotomy for `!![2,−a;−b,2]` with `a,b` positive integers: Kleshchev, *Lectures on Infinite Dimensional Lie Algebras*, §4.1, Example 4.1.3 (finite ⟺ `ab ≤ 3`, affine ⟺ `ab = 4`, indefinite ⟺ `ab > 4`), read in the retrieved text of <https://darkwing.uoregon.edu/~klesh/teaching/IDLALN3.pdf>.
- "Product of the two simple reflections is a translation" in affine type: same notes, §6.4, eqs. (6.9)–(6.10) (`r₀r_θ = t_{ν(θ∨)}`), read in the retrieved text.

*From memory, not verified this session:*
- Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 and Table Aff 1: that the rank-two affine matrices are exactly `a*b = 4`, with `(2,2)` = `A₁^(1)` and `(1,4)` / `(4,1)` = `A₂^(2)` and its transpose. (The trichotomy above is a restatement of Kac's theorem; I did not open Kac.)
- Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 6 (`m ∈ {2,3,4,6}` for finite crystallographic rank two) — not needed for this statement, not opened.
- The authorship attribution of the lecture notes (inferred from the URL); the title and section contents are as retrieved.
- The binomial-theorem step itself is elementary and needs no source; it is proved outright in `check/Audit.lean`.

## Repository integrity

I did not modify `$REPO`. `git status --porcelain` in the repository reports `M README.md` and `M swarm/Statements.lean`; both modifications were already present in the working tree when I started, their diff is docstring-only and does not touch statement 4's text, and I did not write to either file. Everything I created is under `.ultramath/smwbdn3hc/m1/`: this report, `check/Audit.lean` (the Lean check), and `check/compute.py` (the sympy computation).
