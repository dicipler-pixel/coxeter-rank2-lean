# The harness

How a candidate proof becomes an accepted theorem in this repository: who does what, and
which mechanical check refuses it.

The design is taken from the four multi-agent formalization systems that are actually
published and maintained for Lean 4 — all checked against their own documentation, not
summarised from memory:

| System | What it contributes here |
| :--- | :--- |
| [Maestro](https://arxiv.org/html/2610.25920v1) — agentic formal proof by coordination | Workers report *why* an attempt failed, not only that it did; the coordinator decides retry / repair / replan. The member brief asks for diagnoses for this reason. |
| [Choir](https://arxiv.org/html/2609.31903v1) — open protocol for distributed formalization | The split this harness uses: the overseer freezes statements and task boundaries; workers hold no write access to the audited tree; a **deterministic gate** sits between a submission and acceptance, and checks that the published statement is unchanged. |
| [LeanMarathon](https://github.com/yuanhez/leanmarathon) | Role separation — blueprinter, reviewer, refiner, worker — and the rule that an agent's job ends only when its artifact is green, not when it has produced text. |
| [Archon](https://github.com/frenzymath/Archon) | Separate planning from proving so no single context has to hold both; three phases (scaffold → prove → polish), which here is `Statements.lean` → submission → gate. |

What is deliberately *not* taken: none of these systems' own model plumbing, their GitHub
automation, or their benchmark harnesses. This repository is small enough that the whole
protocol is one file of Python and two files of Lean.

## Roles

| Role | Who | Authority |
| :--- | :--- | :--- |
| Overseer | the repository owner | Owns the mathematics: what is worth proving, whether a statement says what it should, and whether an accepted result enters `README.md`. |
| Coordinator | the Open Math OS agent | Picks targets, briefs members, judges submissions, merges only what the gate passed. |
| Prover (member) | a swarm member, own directory | Writes one candidate file; no write access to the repository. |
| Adversary | a member's second job | Produces the false statement that must be rejected (the controls). |
| Gate | `scripts/gate.py` | Mechanical. Decides pass or fail on the artifact, not on the argument. |

## The four-part contract

1. **`swarm/Targets.lean`** — the definitions the targets talk about (`cartan`, `titsForm`),
   built on `RankTwoCertificate.lean`. The gate compiles the repository's copy; a submission
   *imports* it and cannot redefine anything underneath the statement.
2. **`swarm/Statements.lean`** — the target theorems as statements with `sorry` bodies.
   Same namespace, same hypotheses, same conclusion. Change one character of a statement and
   the submission is refused, however good the proof is.
3. **A submission** — one Lean file, `import Targets`, the frozen statements with proofs.
4. **`scripts/gate.py`** — runs six checks and writes `verification/gate-report.json`.

## The six checks and the hole each one closes

| Check | Refuses |
| :--- | :--- |
| banned tokens | `sorry`, `admit`, `native_decide`, a declared `axiom`, `unsafe`, `opaque`, `maxHeartbeats` — being accepted without a proof |
| statement parity | a weakened hypothesis or a strengthened conclusion: `1 ≤ a` silently becoming `0 < a`, `a*b ≤ 3` becoming `< 4` |
| compilation | an unfinished proof |
| kernel replay (`leanchecker`) | an elaborator bug: the module is re-checked by the separate kernel checker, not by the one that produced it |
| axiom audit (`#print axioms`) | `sorryAx` inside a helper, a hidden project axiom, `Lean.ofReduceBool` from `native_decide`. Allowed: `propext`, `Classical.choice`, `Quot.sound` |
| false controls | a gate that cannot say no — every file in `swarm/FalseControls/` must fail to compile *for a mathematical reason*, not a typo |

A `private` helper has a mangled internal name, so `#print axioms` cannot address it. The
gate therefore audits the targets by name and tries the helpers too; when a helper cannot
be named, it falls back to the targets alone and records that in `checks.axioms.note`.
That is sound — an axiom used by a helper is inherited by every theorem that reaches it —
and it means no member has to make a helper public to satisfy the checker.

## Evidence that the gate works

Measured in this VM, Lean 4.33.1 with the prebuilt Mathlib at `/opt/mathlib`:

| Submission | Verdict | Why |
| :--- | :--- | :--- |
| `swarm/selftest/Good.lean` (4 targets proved) | **PASS** (18 s cold, 7 s warm) | every check green, 4/12 targets covered under `--partial` |
| `swarm/Statements.lean` (the skeleton) | FAIL | `sorry` token, and `sorryAx` on all 12 theorems |
| `Good.lean` with `4 < a*b` weakened to `5 < a*b` | FAIL | `statement_parity` names `tits_negative_above_four` as changed |
| `swarm/FalseControls/*.lean` | rejected | "rejected for a mathematical reason" for both |

A gate that has only ever passed has not been tested. This one has been run in both
directions before any member was briefed.

Cost: the Mathlib import is about 10 s of the cold pass; with `verification/build` warm the
whole gate is about 7 s. Nothing here is slow enough to warrant a heartbeat or elaboration
investigation — recorded so that a later slow run can be compared against it.

## Running it

```bash
# the accepted artifact of the first campaign is now in the library: this still passes,
# with all twelve targets covered
python3 scripts/gate.py --submission RankTwoClassification.lean

# one pass on a candidate file (about 20 s cold, 7 s once verification/build is warm)
python3 scripts/gate.py --submission path/to/candidate.lean --partial

# acceptance: no missing targets allowed
python3 scripts/gate.py --submission path/to/candidate.lean
```

The report records the SHA-256 of the submission, of `Targets.lean`, of `Statements.lean`,
the Lean version, every command with its exit status in `verification/gate.log`, the axiom
set per theorem, and the false-control outcomes.

## Toolchain pin

The repository pins `leanprover/lean4:v4.33.0` with Mathlib `v4.33.0`. This VM's Lean and
Mathlib are `v4.33.1`. The gate therefore checks under a *different* Mathlib than the
repository claims, and says so: every report carries `environment.pin_match`, and a
mismatch prints a warning and is recorded in `verification/gate-report.json`.

`--strict-pin` turns that warning into a FAIL, for use in a pin-exact environment.

So a `PASS` here means "kernel-checked under this VM's toolchain", not "reproduced on the
pin". Acceptance into the audited library is the CI workflow's job — `lake build` +
`verify.py` under `v4.33.0` — which is why a gated module only enters `scripts/config.json`
and `README.md` after a green CI run on the pinned toolchain.

## What the harness does not decide

The gate checks that the frozen statements are proved. It cannot check that the frozen
statements say the mathematics their docstrings claim. That is the overseer's reading, and
`LIMITATIONS.md` is where it is written down. The gate is a proof checker with a
statement-integrity lock; it is not a referee.
