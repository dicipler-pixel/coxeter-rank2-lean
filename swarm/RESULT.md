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
| m7 | `swarm/submissions/m7.lean` | PASS, 4/12 | **Independent** second proof of the three `zero_*` statements and `tits_positive_definite`: no helper lemma in common with m1 or m2, different route (bound `a,b ≤ 3`, derive `0 < x²+y²`, split the six pairs, close with `sq_nonneg (x - y)`). A real cross-check. |
| m8 | `swarm/submissions/m8.lean` | PASS, 8/12 | Integration, as its direction declared: all 15 declarations are m1's and m2's verbatim, including docstrings. Confirms the pieces compose, but is not new mathematics. |

## What the swarm refused, and why that was right

Direction d7 (member m5) tried to get `finite_exact_period` by transporting Mathlib's
`DihedralGroup` order through `DihedralBridge`. It was abandoned with the reason that the
bridge gives only `IGroup m ≃* DihedralGroup (m+2)` — no representation sending `c0, c1` to
`s1, s2`, and no identification of `coxRot` with `step`, so the route would duplicate the
period computation rather than shorten it. That is correct, and it is worth recording: the
dihedral isomorphism in this repository does not transfer the reflection representation, so
the period certificates cannot be imported from it.

## Not yet done, deliberately

`Classification.lean` is not part of the audited library: it is not in `lakefile.toml`'s
`roots`, not in `scripts/config.json`, and not mentioned in `README.md` or
`LIMITATIONS.md`. Doing that would change the public theorem count (44 → 56), the badge, and
what CI checks, and it should be done under the pinned toolchain: the gate ran here under
Lean 4.33.1 while the repository pins 4.33.0, so a green CI run is the pin-exact
confirmation, not this report.
