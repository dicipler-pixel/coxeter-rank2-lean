# Member brief: rank-two finite/affine classification

You are one prover in a swarm. Your job is one file: a submission that proves the frozen
targets. You do not edit the repository. You report what you proved and, for what you did
not, why not.

## Where things are

Repository root: `/workspace/nucleus/work/projects/p-870b05c7d9a34cc6a7491c6863177ba6/repo`

```
swarm/Targets.lean      definitions: cartan, titsForm (+ RankTwoCertificate.lean, 44 proved theorems)
swarm/Statements.lean   the 12 frozen statements, bodies `sorry`
swarm/selftest/Good.lean 4 of the 12 already proved — reuse them
scripts/gate.py         the gate that decides whether your file is accepted
HARNESS.md              the protocol
LIMITATIONS.md          what the library does not claim
```

## Environment

Lean 4.33.1, Mathlib prebuilt; `LEAN_PATH` is already set in the shell, so `import Mathlib`
works without any build. Set up a working directory of your own:

Use a directory named after yourself — seven other members are working at the same time, so
two members in one directory will overwrite each other's `Submission.lean`.

```bash
REPO=/workspace/nucleus/work/projects/p-870b05c7d9a34cc6a7491c6863177ba6/repo
MEMBER=<your-name>          # e.g. m3
mkdir -p ~/work/$MEMBER && cd ~/work/$MEMBER
cp $REPO/swarm/Targets.lean $REPO/RankTwoCertificate.lean $REPO/swarm/Statements.lean .
lean -o RankTwoCertificate.olean RankTwoCertificate.lean    # ~10 s, once
lean -o Targets.olean Targets.lean                          # once
# then, as you edit:
lean -o Submission.olean Submission.lean
```

Self-check exactly as the coordinator will:

```bash
python3 $REPO/scripts/gate.py --submission ~/work/Submission.lean --partial
```

## The targets

Already proved in `swarm/selftest/Good.lean` — copy those four bodies, do not spend time on
them: `cartan_det`, `tits_vanishes_at_four`, `tits_negative_above_four`,
`golden_product_eq_four_cos_sq`.

The eight that remain, in rough order of how much they are worth:

1. `finite_exact_period` — T2. For **every** `a, b ≥ 1` with `a*b ≤ 3`, the step has the
   exact period the finite type prescribes (3, 4, 6). This is LIMITATIONS bullet 2 closed.
   There are six pairs: `(1,1) (1,2) (2,1) (1,3) (3,1)` plus the `a*b = 1` case. Useful
   facts: `step a b (x, y) = (-(b*x - y) + a*y, b*x - y)`, so each step is an explicit
   `2×2` integer matrix; its charpoly is `λ² - (ab-2)λ + 1`, so a universal period `n`
   follows from `T^n = 1` and exactness from a witness such as `(1, 0)`.
2. `affine_unipotent`, `affine_iterate`, `affine_no_positive_period` — T3. For every
   `a*b = 4` (`(1,4) (2,2) (4,1)`), `(T - 1)² = 0`, hence `Tⁿ v = v + n(T v - v)` by
   induction on `n`, hence no positive power fixes `(1, 0)` because `T(1,0) - (1,0) ≠ 0`
   (it is `(-(a+2), -1)`).
3. `zero_product_iterate`, `zero_product_no_positive_period`,
   `zero_partner_no_positive_period` — T4. With `a = 0` the square of the step is the shear
   `(x, y) ↦ (x, y - 2bx)`; iterate that, then split on the parity of `n`. The mirror case
   uses the witness `(0, 1)`.
4. `tits_positive_definite` — T5. `titsForm a b x y = 2b·x² - 2ab·xy + 2a·y²` is positive
   off the origin for `1 ≤ a, b`, `a*b ≤ 3`. A quadratic with positive leading coefficient
   and negative discriminant, or complete the square.

## Rules

* Statements are frozen: the gate compares your theorem text against `Statements.lean` up to
  whitespace. Do not change a binder, a hypothesis or a conclusion to make a proof go
  through — if a statement looks false, say so and give the counterexample.
* No `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `opaque`, `maxHeartbeats`.
  Helper lemmas are welcome and are audited too.
* Keep the namespace `OperatorFirst.CoxeterRankTwo`.
* Do not modify the repository. Work in your own directory.

## What to report

For each target: proved, or not proved. For each not proved, the diagnosis — which routes
you tried, where each broke, what extra fact would close it, and any counterexample you
have checked in Lean. A report of "tried `simp`, `ring`, `nlinarith`" is worth nothing; "the
`a*b = 1` case needs `T³ = 1` and `nlinarith` cannot see it because the hypothesis is on
`a*b` and not on `a` and `b` separately, so it must be case-split first" is worth
everything.
