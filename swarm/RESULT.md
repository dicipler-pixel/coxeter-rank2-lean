# Result: the twelve frozen statements are proved

One file, one gate run, no gaps: [RankTwoClassification.lean](../RankTwoClassification.lean) — promoted
from this campaign to the repository root and wired into the lakefile, `scripts/config.json`, the
README and `LIMITATIONS.md` — covers **12/12**
frozen targets with 19 audited declarations, axiom union exactly
`{propext, Classical.choice, Quot.sound}`, kernel replay clean.

The campaign's own copy, `swarm/Classification.lean`, is now a pointer to that module rather than a
second source of the same theorems; removing it needed an approval that did not arrive.

```
python3 scripts/gate.py --submission RankTwoClassification.lean
verdict: PASS   (12/12 covered, sha256 c4c9d374…)
```

## Who proved what

| Target | Prover | Route |
| :--- | :--- | :--- |
| `finite_exact_period` | swarm m1 | bound `a, b ≤ 3` from `1 ≤ a, 1 ≤ b`, then case split |
| `finite_exact_period` (second, independent) | swarm m6 | enumeration reusing `U3_exact`/`U4_exact`/`U6_exact`, plus direct `(2,1)` and `(3,1)` |
| `affine_unipotent`, `affine_iterate`, `affine_no_positive_period` | swarm m1 | charpoly identity `T² = (ab−2)T − 1`, linearity, induction on `n` |
| `zero_product_iterate`, `zero_product_no_positive_period`, `zero_partner_no_positive_period` | swarm m2 | the square of the step is a shear; parity split on `n` |
| `cartan_det`, `tits_vanishes_at_four`, `tits_negative_above_four`, `golden_product_eq_four_cos_sq` | coordinator | `det_fin_two`; `titsForm a b a 2 = 2a(4 − ab)`; `Real.cos_pi_div_five` |

m6's proof is not in `Classification.lean` (m1 covers the same statement by a more general
route); it is kept in `swarm/submissions/m6.lean` as a second, independent
check of the same statement.

## What this closes

Four of the six paragraphs of `LIMITATIONS.md`:

- **one representative per product** — no longer: every `(a, b)` with `a, b ≥ 1` and
  `a*b ≤ 3` has its exact period, and every `a*b = 4` representative is unipotent;
- **the Cartan determinant `4 − ab` is not connected to finiteness** — now it is:
  `T² = (ab−2)T − 1` is the charpoly identity, so `ab = 4` is exactly unipotence and
  `ab ≤ 3` is exactly a finite order with the type's period;
- **`4cos²(π/5)` is only half identified** — now `4cos²(π/5) = (3+√5)/2` is proved;
- **the Tits form sign is asserted, not proved** — now positive definite on `ab ≤ 3`,
  degenerate at `ab = 4`, negative above it.

It also records something the library did not say before: `ab = 0` with a nonzero partner
gives an infinite-order product, so `4 − ab > 0` alone does **not** make the product finite.
The off-diagonal pair has to be genuinely nonzero; that is why `1 ≤ a, 1 ≤ b` appears in the
finite statement.

## What it still does not do

- Rank three and above. The general finite/affine classification is untouched; this is
  rank two.
- The golden case is an arithmetic identity, not the `H₂` geometry: the Cartan matrix of
  `I₂(5)` and its reflection representation are not formalized.

## Late submissions (after the swarm ended)

Two members submitted after the swarm closed on m1, and the verdict channel refused them
(`swarm smwazmwcq has ended`). Both were gated by hand; neither changes the result.

| Member | File | Gate | What it is |
| :--- | :--- | :--- | :--- |
| m7 | `swarm/submissions/m7.lean` | PASS, 4/12 | **Independent** second proof of the three `zero_*` statements and `tits_positive_definite`: no helper lemma in common with m1 or m2, different route (bound `a,b ≤ 3`, derive `0 < x²+y²`, split the five pairs, close with `sq_nonneg (x - y)`). A real cross-check. |
| m8 | `swarm/submissions/m8.lean` | PASS, 8/12 | Integration, as its direction declared: all 15 declarations are m1's and m2's verbatim, including docstrings. Confirms the pieces compose, but is not new mathematics. |

## What the swarm refused, and why that was right

Direction d7 (member m5) tried to get `finite_exact_period` by transporting Mathlib's
`DihedralGroup` order through `DihedralBridge`. It was abandoned with the reason that the
bridge gives only `IGroup m ≃* DihedralGroup (m+2)` — no representation sending `c0, c1` to
`s1, s2`, and no identification of `coxRot` with `step`, so the route would duplicate the
period computation rather than shorten it. That is correct, and it is worth recording: the
dihedral isomorphism in this repository does not transfer the reflection representation, so
the period certificates cannot be imported from it.

## Wired into the library, and confirmed on the pin

`RankTwoClassification.lean` is now part of the audited library: in `lakefile.toml`'s `roots`,
in `scripts/config.json` (inventory `56`, axiom audit, false controls), in the README table and
theorem badge, and in `LIMITATIONS.md`, which now separates what is proved from what is still
open. `PROVENANCE.md` and `AI_USE.md` say where the proofs came from.

The pin-exact confirmation is the CI workflow, not any local run: the gate here used Lean
4.33.1 while the repository pins 4.33.0.

```
run 5  .github/workflows/build.yml  commit 466c1c8  conclusion: success  (3m 48s)
   Build every module                                        success
   Replay every module in the independent kernel checker      success
   Axiom audit, theorem inventory and false controls          success
```

The inventory step is what makes "56 theorems" a checked number: `scripts/verify.py` fails if
the count differs from `expected_theorems`, if any theorem's axioms leave
`{propext, Classical.choice, Quot.sound}`, or if the false control is accepted.

## Still open

Rank ≥ 3, faithfulness of the reflection model to the Coxeter presentation, radical membership
and positive semidefiniteness of the Tits form at `a*b = 4`, and the `H₂` geometry. See
[`../LIMITATIONS.md`](../LIMITATIONS.md).

## Second campaign: signature (1,1), proved five ways

`tits_signature_above_four` — above the boundary the Tits form has `sigPos = sigNeg = 1` in
Mathlib's sense — was proved five times by five different arguments, which is the strongest
evidence in this repository that a statement is not just true but natural:

| Route | Proved by | Idea |
| :--- | :--- | :--- |
| line bounds | coordinator, and independently swarm m4 | `(1,0)` is positive, `(a,2)` negative, so each index is at least 1; each line is also a nonpositive direction for the other index, so each is at most 1 |
| Sylvester | swarm m5 | the shear `(x,y) ↦ (x − (a/2)y, y)` makes the form a weighted sum of squares with weights `2b` and `a(4−ab)/2`, then `sigPos_of_equiv_weightedSumSquares` counts their signs |
| inertia identity | swarm m6 | `sigPos + sigNeg + finrank radical = 2` with two lower bounds forces both to be 1 |
| eigenvalues | swarm m3 | charpoly `λ² − 2(a+b)λ + ab(4−ab)` with `det < 0`, bridged from a spectral decomposition |
| hyperbolic pair | swarm m1 | `s = √(ab(ab−4))` gives the isotropic vector `(ab+s, 2b)`; reflecting produces `Q(e±) = ±2`, so the form is isometric to weights `(2,−2)` |

The library keeps the coordinator's proof; the other four are in `swarm/submissions/signature-*.lean`,
each gated with the same axiom set. Together with `tits_signature_below_four` and
`tits_signature_at_four`, the signature is now `(2,0)`, `(1,0)`, `(1,1)` on the three sides.

## Third campaign: the radical at the boundary, proved five ways

`tits_radical_finrank_at_four` (dimension exactly 1) and `tits_radical_eq_span_at_four` (the
radical *is* the line through `(a, 2)`) were proved five times, independently of the library:

| Route | Proved by | Idea |
| :--- | :--- | :--- |
| shift identity + inertia | swarm m1, adopted into the library | `Q(a+x, 2+y) = Q(x,y) + 2a(4−ab)(1+y)` vanishes at `ab = 4`, so `(a,2)` is radical; then `sigPos + sigNeg + dim radical = 2` |
| perfect square | swarm m3 | at `ab = 4`, `b·Q(v) = 2(b v₀ − 2 v₁)²`, so the radical is the kernel of one linear functional; rank–nullity gives dimension 1 |
| polar pairing | swarm m2, m5 | `polar(titsQF) = 2·titsBilin`; one pairing against `e₀` gives `2v₀ = a v₁`, hence `v ∈ ℝ·(a,2)` |
| matrix rank and coordinates | swarm m4 | the radical is the kernel of the polar map; span inclusion from `B((a,2),w) = a y (4−ab)`, reverse inclusion from one equation |

The library's own proof of the span statement is m1's route, adopted with attribution in the
source. `swarm/submissions/radical-m*.lean` holds the rest.

## How the submissions are checked

Each claim in this file is backed by a file under `swarm/submissions/`, and
[`MANIFEST.tsv`](submissions/MANIFEST.tsv) is what says which file backs which claim. CI gates
**every manifested claim** in `scripts/verify.py`, under the pinned toolchain, with the pinned
Mathlib on `LEAN_PATH` — so the tables above are pin-verified rather than reported.

Two properties are enforced, both tested by breaking them deliberately:

* every `.lean` file in the directory must appear in the manifest, as `gate` or `archived`; a new
  file that nobody classified fails the run rather than quietly going unchecked;
* every manifest row must name a file that exists, so a claim cannot lose its evidence when a file
  is renamed or removed.

**What "archived" means, and what it costs.** Four files are archived: `m8.lean` (an integration of
m1 and m2, which this file already calls not new mathematics), `radical-m2.lean` (the polar-pairing
route again, as in `radical-m5`), `order5-m1.lean` (five-fold unfolding again, as in the library),
and `order5-m5-vector.lean` (a matrix-free cross-check of `order5-m5`). They were gated when
accepted and are kept as the historical record, but they are **not re-gated on every push**. That is
a real reduction in coverage, and it is the price of not scaling with every file ever added: CI now
grows with the number of distinct claimed routes, which is a much slower-growing set than the
directory.

Before the manifest, every file was re-gated on every push and the run took about 14 minutes at 21
files; with the manifest it gates 17. The gating is also now parallel inside `verify.py` — the first
claim runs serially to fill the shared definition cache, the rest run `min(4, cpu_count)` at a time,
each with its own scratch directory and report file. Measured on four cores: 232 s serial, 131 s with
two workers, 81 s with four.

A job-level matrix would need a `.github/workflows/build.yml` edit, which this session cannot make —
the connected GitHub App has no `workflows` permission and such pushes are rejected. The YAML is
written out in [`CI-MATRIX-JOB.md`](CI-MATRIX-JOB.md) for whoever can apply it, together with the
reason it is the worse trade: each cell pays its own toolchain and Mathlib cache install, about four
minutes, against twenty-five seconds of gating.

## Fourth campaign: order five is impossible, proved five ways

The two statements of the `H₂` gap — `order_five_forces_golden_trace` (period 5 forces
`(a*b)² − 3(a*b) + 1 = 0`) and `no_integral_period_five` — were proved five times, independently:

| Route | Proved by | Idea |
| :--- | :--- | :--- |
| five-fold unfolding | coordinator, swarm m1, m4 | iterate `T² = tT − 1` four times, evaluate at `(1,0)` and `(0,1)`, then `t²+t−1 = 0` |
| Chebyshev recurrence | swarm m4 | `Tⁿv = fₙ·Tv − fₙ₋₁·v` by one induction, specialised at `n = 5` |
| geometric sum | swarm m2 | `T⁴+T³+T²+T+1 = T²(t²+t−1)`; surjectivity plus torsion-freeness replaces the degenerate-pair case split |
| matrix powers | swarm m5 | `M⁵ = 1` for `M = !![ab−1,−a;b,−1]`, then `M⁵ = c₅M − d₅1` entrywise |
| modulus 4 | swarm m3 | `5 ∤ |GL₂(ℤ/4)| = 96`, so a period-5 element would reduce to the identity, which is impossible |

One honest qualification, recorded because it is easy to miss: **m3's proof of the first
statement is vacuous.** Its mod-4 argument refutes the hypothesis outright, so the implication holds
by `exfalso` and the golden relation is never derived. That is a correct proof of the frozen
statement and it is the cheapest proof of the second one — but it is not independent evidence for
the content of the first, which the other four routes establish non-vacuously.

Two corrections to my own brief came out of the campaign: `step_sq_char` is in
`RankTwoClassification.lean`, not `RankTwoCertificate.lean` as the brief said (three members
reproved it rather than trust the pointer), and `t³ − 2t + 1 = 0` alone does not give the result —
it needs the combination `t·(d₅+1) − c₅` that m5 names.
