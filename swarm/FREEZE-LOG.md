# Freeze log

Every change ever made to a statement in `Statements.lean` after it was frozen, with the reason.
The point of freezing is that a statement cannot be bent to fit a proof; the point of this file is
that when a statement *is* touched, the touch is visible and its meaning can be checked.

Rule for reading this file: a change is admissible here only if it is one of

* **syntax** — the same proposition, written differently, because the frozen text did not
  elaborate or elaborated as something else;
* **split** — one statement separated into several, each proved;
* **rename** — the same proposition under a name that says what it proves;
* **hold** — a statement temporarily withdrawn from the frozen set because it was not yet proved,
  and later restored.

A change that alters the proposition — a hypothesis, a quantifier, a carrier, a conclusion —
is not admissible at all. There is no entry of that kind, and there must never be one.

---

## 1. `tits_radical_at_four` → `tits_vanishes_at_four` (rename)

**Before.** `tits_radical_at_four (hab : a * b = 4) : titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 = 0`
**After.** the same proposition, named `tits_vanishes_at_four`.
**Why.** An independent audit pointed out that vanishing at a vector is not radical membership,
and the name promised the latter. The proof did not change; the name now says what is proved.
Radical membership became its own theorem much later (`tits_radical_at_four`, campaign 3).

## 2. `tits_signature_above_four` — dot notation to function application (syntax)

**Before.** `(titsQF (a : ℤ) (b : ℤ)).sigPos = 1 ∧ (titsQF (a : ℤ) (b : ℤ)).sigNeg = 1`
**After.** `sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1`
**Why.** `sigPos` is a function on quadratic forms, not a field of one, so the dot-notation form
does not elaborate at all. Nothing about the proposition changed: same function, same argument,
same conclusion. Caught by compiling, not by reasoning — and independently rediscovered by three
swarm members, which is some evidence that the notation is a trap rather than a slip.

## 3. `tits_signature_at_four` — the radical conjunct removed (split)

**Before.** `sigPos … = 1 ∧ sigNeg … = 0 ∧ Module.finrank ℝ (QuadraticMap.radical …) = 1`
**After.** `sigPos … = 1 ∧ sigNeg … = 0`, with the radical dimension proved separately as
`tits_radical_finrank_at_four`.
**Why, and this one is the honest weak spot.** I could not get the radical conjunct through in
that proof — the coordinate expansion failed — so instead of freezing a statement I could not
prove, I split off the part I could. The proposition lost nothing: the conjunct came back as its
own named theorem in the next commit, and `tits_radical_eq_span_at_four` after that. But the
sequence was "prove what is easy, name the rest later", and a reviewer is right to watch for it.
Recorded here rather than left in a commit message.

## 4. `tits_radical_eq_span_at_four` — held out, then restored (hold)

**Before.** frozen with the other radical statements.
**After.** removed from `Statements.lean` for one commit, restored once proved.
**Why.** Same reason as 3: it was frozen before it was proved, and the proof did not come. Holding
it out was better than leaving a frozen statement the library file could not satisfy; restoring it
was the first thing done after swarm member m1 found the shift-identity route.

## 5. `tits_radical_eq_span_at_four` — list literal to vector literal (syntax)

**Before.** `= ℝ ∙ ([(a : ℝ), 2] : Fin 2 → ℝ)`
**After.** `= ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ)`
**Why.** `[…]` elaborates as `List ℝ`; the vector notation is `![…]`. Same vector, written so that
it elaborates as a function `Fin 2 → ℝ`.

---

## What this log is for

Every entry above is one of the four admissible kinds, and each is checkable against the git
history. If a future change to `Statements.lean` is not one of those kinds, it belongs in a
review, not in this file.
