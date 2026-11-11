# The machine reads

The independent readings summarised in [`../../AUDIT.md`](../../AUDIT.md), kept here because
`.ultramath/` is not committed and a claim of independence should be checkable.

Each file is one reader's report, as delivered — including where it says what it could not verify.
Who read what, and which model:

| File | Reader | Model | Scope |
|---|---|---|---|
| `pass1-m5-all-twelve.md` | pass-1 m5 | mistral-large-4-0 | all twelve statements |
| `pass2-m1-statements-1-3.md` | pass-2 m1 | mistral-large-4-0 | statements 1–3 |
| `statement-1.md` … `statement-12.md` | pass-3 m1, one swarm per statement | deepseek-v4.1-flash | one statement each |
| `statement-13.md`, `statement-14.md` | pass-4 m1, one swarm per statement | muse-spark-open | the two trichotomy statements added after the audit |

These are language-model reports, not referees. Their verdicts are recorded in `AUDIT.md` only after
the claims were checked against the definitions, a computation, or a fetched source; where a report's
citation could not be checked, `AUDIT.md` does not repeat it as fact.

A **human** review goes in the parent directory instead, following `../TEMPLATE.md` — that is what
`AUDIT.md` §1 and §9 wait on, and no machine read substitutes for it.
