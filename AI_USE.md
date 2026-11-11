# AI use

The research questions behind this library are Jeromie Beasley's. AI tools (Claude and
ChatGPT) were used to search the literature, write and repair Lean proofs, and organise this
repository.

No statement here rests on an AI's say-so. Every proof is checked by the Lean kernel and
replayed by an independent kernel checker on every push, every theorem's axioms are audited,
and every false control must be rejected for the check to pass. What the statements mean, and
what they do not claim, is set out in plain words in `README.md` and `LIMITATIONS.md`.

The theorems of `RankTwoClassification.lean` were written by a swarm of agents working
from statements frozen in advance. None of them entered the library on an agent's say-so: each
was accepted by `scripts/gate.py` — statement text unchanged, module compiled, replayed in the
independent kernel checker, every theorem's axioms audited, and two deliberately false claims
required to fail — and the protocol that did it is `HARNESS.md`.
