import RankTwoClassification

/-!
# Campaign record: the accepted file was promoted

This file was the swarm's assembled submission: the twelve frozen statements of
`swarm/Statements.lean` with proofs, 12/12 through `scripts/gate.py`.

It is **not** a second source of those theorems. The accepted artifact now lives in
`RankTwoClassification.lean` at the repository root, where it is in the lakefile, in
`scripts/config.json`, and checked by CI under the pinned toolchain. That promotion also
carried three corrections found by auditing the statements against the mathematics:

* the theorem that proves the Tits form vanishes at `(a, 2)` at `a*b = 4` is named
  `tits_vanishes_at_four`, not `tits_radical_at_four` — radical membership is not what is
  proved there;
* the docstrings on `titsForm` and on that theorem now claim positive definiteness only for
  `a*b ≤ 3`, vanishing at `(a, 2)` at `a*b = 4`, and negativity at `(a, 2)` above, rather
  than "positive definite exactly when `0 < ab < 4`, indefinite above";
* three supporting declarations are `lemma` rather than `theorem`, so that every `theorem`
  in this library is a claimed result and the inventory in `scripts/verify.py` counts claims.

The proofs themselves are unchanged. `swarm/RESULT.md` records which member proved what.
-/
