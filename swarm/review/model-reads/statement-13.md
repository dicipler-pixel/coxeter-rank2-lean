# Audit Report — Statement 13 `tits_semidefinite_at_four`

## One-row summary

| statement | standard fact | verdict | evidence | correction needed |
|---|---|---|---|---|
| `tits_semidefinite_at_four (a b : ℕ) (1≤a)(1≤b)(a*b=4) (x y:ℝ): 0 ≤ titsForm a b x y` — docstring: "nonnegative everywhere, which together with its vanishing at `(a,2)` makes it degenerate there" | Kac, *Infinite-Dimensional Lie Algebras*, Ch. 4 (Thm 4.3; Ch. 2 invariant form): a GCM is affine iff symmetrised invariant form is positive semidefinite of corank 1 (radical 1-dim). In rank 2, `C=[2 -a; -b 2]` (`a,b≥0, a=0⇔b=0`) is affine iff `det C =4−ab=0` iff `ab=4`; then `B=diag(b,a)C=[[2b,−ab],[−ab,2a]]`, `Q(x,y)=2bx²−2ab xy+2a y²` has rank 1, kernel spanned by `(a,2)` (or `∝(2,b)`). Indefinite iff negative det. | **weaker than the standard fact** (true but incomplete as a formal degeneracy statement) | Arithmetic verified by sympy: `Q(a,2)=−2a(ab−4)=0` so `=0` at `ab=4`; `Q=2b(x−2/b·y)² ≥0` (discriminant `Δ=4ab y²(ab−4)=0` when `ab=4`, leading coeff `2b>0`). Matrix `det=ab(4−ab)=0`, `tr=2(a+b)>0` so eigenvalues `0, tr`. Hence PSD holds. Standard PSD+isotropic ⇒ degenerate lemma: if `Q≥0` and `Q(v₀)=0, v₀≠0` then `B(v₀,w)=0 ∀w` (from `Q(v₀+t w)≥0 ∀t` discriminant ≤0). Computation `B((a,2),(x,y))=a·y·(4−ab)` (verified) shows radical membership, but this computation is **not** a Lean theorem in the repo. Pair (13)+(10) mathematically implies degenerate in rank 2, but neither states `rank=1`, `det=0`, nor `∃v≠0 ∀w B(v,w)=0`. | For a faithful formalisation of “degenerate / corank 1” (Kac Ch. 4 wording) add one of: (i) `titsForm` radical membership `∀x y, Bilin((a,2),(x,y))=0` at `ab=4`; or (ii) rank/corank statement `det=0 ∧ ∃v≠0 Q(v)=0` with `Q` not identically zero; or at minimum an explicit lemma `PSD ∧ isotropic ⇒ degenerate`. As is, docstring claim “which together … makes it degenerate” is a true informal mathematical corollary, not a proved Lean proposition; LIMITATIONS.md/Targets.lean correctly acknowledge this gap. |

## True but not what it says

The proposition as typed is true. With `a*b=4` and `1≤a,1≤b` the only integer pairs are `(1,4),(2,2),(4,1)`, and `Q=2bx²−8xy+2ay²=2b(x−2y/b)² ≥0` indeed. Hypotheses `1≤a,1≤b` are exactly what Kac requires for a GCM (`a_ij≤0, a_ij=0⇔a_ji=0`) and are necessary: without them `titsForm` can be identically zero (`a=b=0 ⇒ Q≡0`) or have wrong sign in leading coefficient. Carrier `ℝ` and quantifier `∀x y` are correct. Not vacuous: `ab=4` is satisfiable (three witnesses). The docstring’s “makes it degenerate” is mathematically defensible — in any PSD symmetric form, isotropic forces radical (Cauchy–Schwarz) — so in rank 2 the pair (13)+(10) does entail degeneracy (rank 1). But formally the repo proves only `∀x y Q≥0` and separately `Q(a,2)=0` (statement 10); it does not prove `B((a,2),·)=0`, `rank=1`, or `corank=1`. That is why LIMITATIONS.md says “What is still not formalized is that `(a,2)` spans the radical … (`a·y·(4−ab)`)” and Targets.lean repeats it. Under strict reading “degenerate” means radical non-trivial, the Lean library states a weaker half (PSD + zero) and leaves the standard Ch. 4 conclusion as an informal comment.

## Blindness

I did **not** open any blindness-list files: did not open `$REPO/RankTwoClassification.lean`, `$REPO/swarm/Classification.lean`, `$REPO/swarm/selftest/`, `$REPO/swarm/submissions/`, `$REPO/swarm/RESULT.md`, `$REPO/swarm/AUDIT.md`, `$REPO/swarm/REVIEW-PACKET.md`, `$REPO/swarm/review/` (except `AUDIT-BRIEF.md` as instructed), nor anything under `$REPO/.ultramath/`. I read only allowed files: `swarm/Statements.lean`, `swarm/Targets.lean`, `RankTwoCertificate.lean`, `README.md`, `LIMITATIONS.md`, and this brief.

## Sources

Citations to Kac Ch. 4 / Ch. 2 and Bourbaki Ch. VI §1 are **from memory / training recall, not verified live** against a fetched text (no web fetch performed; site text not retrieved). All arithmetic identities quoted above were **verified** locally with Python/sympy in this session: `Q(a,2)=−2a(ab−4)`, `Δ=4ab(ab−4)y²`, `det=ab(4−ab)`, `B((a,2),(x,y))=a y(4−ab)`, and `Q=2b(x−2y/b)²` at `ab=4`.

## Repository modification

I did not modify `$REPO`. No files outside `.ultramath/smwbhzsee/m1/` were created or edited.

## Verdict detail

- **Not false:** `Q≥0` holds at all affine representatives; checked computationally.
- **Not stronger:** does not claim corank 1 when not true (trace >0 prevents identically zero).
- **Not misleading as named** if read with LIMITATIONS.md (which discloses radical not proved); the name `tits_semidefinite_at_four` itself promises only PSD, which it delivers. The docstring phrase “together … makes it degenerate” is an informal mathematical note; standing alone without the LIMITATIONS disclaimer it would be misleading as a formal claim, but the repo’s published prose explicitly flags the missing radical lemma, so the milder verdict “weaker than standard fact” is appropriate rather than “misleading”.

