# Reviewer records

One file per human reviewer, named after them, following `TEMPLATE.md`. The packet that explains
what is being asked is [`../REVIEW-PACKET.md`](../REVIEW-PACKET.md): twelve statements, about
30–45 minutes, no Lean and no proofs required.

Why this directory exists: the twelve statements have two independent language-model readings
(statements 1–3) and one (statements 4–12), plus machine checks for meaning and arithmetic — see
[`../AUDIT.md`](../AUDIT.md). A language model is not a referee. A record here is what closes that
gap, and `../AUDIT.md` §1 and §8 change when one arrives.

Nothing here is required for the library to be correct. Theorems are kernel-checked on every push
regardless. What a review changes is how much weight the *claims about meaning* in `README.md` and
`LIMITATIONS.md` are asked to carry on their own.
