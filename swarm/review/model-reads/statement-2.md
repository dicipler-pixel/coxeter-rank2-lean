# Audit report — statement 2, `finite_exact_period`

Auditor: member `m1` (swarm `smwbdn3dn`). Statement audited: **only** number 2 of
`swarm/Statements.lean`. Files written (all in my own directory): this report, `verify.lean`
(machine check), `check.py`, `check2.py` (arithmetic).

## The statement and its docstring

```lean
theorem finite_exact_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    (a * b = 1 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 3) ∧
      (a * b = 2 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 4) ∧
        (a * b = 3 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 6)
```

Docstring: "For every `a, b ≥ 1` with `a*b ≤ 3`, the Coxeter element has the exact period the
finite type prescribes: `3` for `A₂`, `4` for `B₂`, `6` for `G₂`."

`step a b = s1 a ∘ s2 b` is a self-map of `V = ℤ × ℤ`, with
`s1 a (x,y) = (-x + a y, y)`, `s2 b (x,y) = (x, b x - y)`, and
`HasExactPeriod f n ⇔ (∀ x, iter f n x = x) ∧ ∀ m, 0 < m → m < n → ∃ x, iter f m x ≠ x`.

## 1. The standard fact the statement names

Rank two: in the dihedral Coxeter group `I₂(m)` the product `s₁s₂` of the two simple reflections
is a rotation through `2π/m`, hence has order exactly `m`; for the crystallographic finite cases
`m = 3, 4, 6` this is `A₂`, `B₂/C₂`, `G₂`. The dictionary tying the Cartan off-diagonal
magnitudes to `m` is

$$a\,b \;=\; 4\cos^2(\pi/m), \qquad\text{equivalently}\qquad \operatorname{tr} = a\,b - 2 = 2\cos(2\pi/m).$$

So `ab = 1, 2, 3` correspond to `m = 3, 4, 6`, and `ab = 4` corresponds to `2cos(2π/m) = 2`,
i.e. `m = ∞` (no finite rotation order — the affine side). All four values computed with sympy
(`check2.py`).

Citations:

* **Humphreys, *Reflection Groups and Coxeter Groups*, Ch. 1 §1.1, pp. 3–5** — the `I₂(m)`
  example: `𝓘ₘ` "contains m rotations (through multiples of 2π/m)", and a rotation through `2π/m`
  "can be achieved as a product of two reflections relative to a pair of adjacent diagonals
  which meet at an angle of θ := π/m"; the computation there shows `s_α s_β` is "(a
  counterclockwise) rotation through 2θ". **Verified**: I retrieved the text of §1.1, pp. 3–5,
  including the running head "1.1. Reflections 5".
* **Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §4 ("The geometric representation of a
  Coxeter group"), no. 2, pp. 95–96** — Prop. 1 (on the plane `E_{s,s'}`), and in its proof:
  for finite `m = m(s,s')` the product `σ_s σ_{s'}` "is the rotation with angle 2π/m. In
  particular, its order is m"; Prop. 2: `⟨σ_s, σ_{s'}⟩` is "a dihedral group of order
  `2m(s,s')`"; Prop. 4(c): in the group `W(M)`, `g_s g_{s'}` "is of order `m(s,s')`". **Verified**
  (text retrieved, including the running heads "§4. GEOMETRIC REPRESENTATION OF A COXETER GROUP"
  and p. 96). Note the brief points at Bourbaki Ch. IV §1; Ch. IV §1 no. 2 is titled "Dihedral
  groups" and carries the abstract rank-two statement, whereas the geometric statement with the
  rotation angle and the order of `g_s g_{s'}` is Ch. V §4 no. 2. Bourbaki proves Prop. 4(c)
  exactly by the argument used in §4(a) below: "order at most `m`" by the presentation, "at least
  `m`" because the geometric product has order exactly `m`.
* **Humphreys §2.3, p. 31** — the bilinear form of a Coxeter graph is
  `B(α_s, α_t) = −cos(π/m(s,t))`; after normalising `B(α_i, α_i) = 2` this is exactly
  `a_ij a_ji = 4cos²(π/m_ij)`. **Section and page verified** from the printed table of contents;
  the formula is the standard one (below, "recalled" line).
* **Humphreys §6.6, p. 135** ("Crystallographic Coxeter groups"): crystallographic ⇔
  `m(s,t) ∈ {2,3,4,6}` (with the cycle condition, vacuous for a two-vertex graph). **Section
  title verified** from the table of contents; the theorem itself is quoted from standard
  knowledge, not read in Humphreys (see "Sources" line at the end).

Under this dictionary the statement is the crystallographic rank-two instance of the standard
fact, for every representative `(a,b)` of the three products.

## 2. What the proposition actually asserts (and its exact instance set)

`step a b` has matrix `!![a*b - 1, -a; b, -1]` in the standard basis: determinant `1`,
trace `a*b - 2`, characteristic polynomial `λ² − (a b − 2)λ + 1`.

`HasExactPeriod f n` says `f^n = id` and no smaller positive power is `id`. For a self-map
`f^n = id` already forces `f` bijective, so this is precisely "the order of `f` in the symmetric
group of `ℤ × ℤ`" — the right notion for this claim.

**Exhaustiveness.** With `a, b : ℕ` and `1 ≤ a, 1 ≤ b, a*b ≤ 3` the pair `(a,b)` is one of
`(1,1), (1,2), (2,1), (1,3), (3,1)` and nothing else; I machine-checked this case split
(lemma `key` in `verify.lean`). The three implications are therefore exhaustive over the stated
hypotheses: this is a statement about *every* representative on the finite side, not a sample.
The general warning that "a conjunction of implications is not a statement about all products"
does **not** bite here. What is outside is `a*b = 0` (period 2 only for `(0,0)`; infinite order
as soon as one partner is nonzero) and `a*b ≥ 4` (no positive period); none of that is claimed,
and it is the subject of statements 3, 5, 7, 8.

**Arithmetic** (`check.py`, `check2.py`, sympy, exact integer matrices):

| (a,b) | ab | matrix | det | tr | exact order | claimed |
|---|---|---|---|---|---|---|
| (1,1) | 1 | `[[0,-1],[1,-1]]` | 1 | −1 | 3 | 3 ✓ |
| (1,2) | 2 | `[[1,-1],[2,-1]]` | 1 | 0 | 4 | 4 ✓ |
| (2,1) | 2 | `[[1,-2],[1,-1]]` | 1 | 0 | 4 | 4 ✓ |
| (1,3) | 3 | `[[2,-1],[3,-1]]` | 1 | 1 | 6 | 6 ✓ |
| (3,1) | 3 | `[[2,-3],[1,-1]]` | 1 | 1 | 6 | 6 ✓ |

All powers `M^k` for `0 < k < n` were enumerated and none is the identity, so the period is
exact, not merely "divides". Structural reason: Cayley–Hamilton gives
`M² = (a b − 2) M − I`, with `a b − 2 = 2cos(2π/m) ∈ {−1, 0, 1}`, whence `M³ = I`, `M⁴ = I`,
`M⁶ = I` in the three cases, and `tr(M^k) = 2cos(2πk/m) ≠ 2` for `0 < k < m`.

**Machine check.** `verify.lean` copies the five frozen definitions verbatim from
`RankTwoCertificate.lean` and proves all five exact-period facts and then the statement itself,
under the same hypotheses. `#print axioms OperatorFirst.CoxeterRankTwo.finite_exact_period`
reports `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no project axioms. So the
statement is **true as stated** and is provable from the frozen definitions.

## 3. Verdict

| statement | standard fact | verdict | evidence | correction needed |
|---|---|---|---|---|
| 2, `finite_exact_period` | In `I₂(m)` the product `s₁s₂` is a rotation through `2π/m`, of exact order `m`; for the crystallographic finite cases `ab = 4cos²(π/m) = 1, 2, 3` this is `A₂, B₂/C₂, G₂` with `m = 3, 4, 6` | **matches** — for the finite crystallographic side, stated for every representative `(a,b)`, at the level of the integral reflection model on `ℤ × ℤ`, with the two qualifications in §4 | Humphreys Ch. 1 §1.1 pp. 3–5 (verified); Bourbaki Ch. V §4 no. 1 Prop. 2 (verified); Humphreys §2.3 p. 31, §6.6 p. 135 (section titles verified, statements standard); exact matrix computation (§2); machine-checked proof of the statement itself (`verify.lean`) | none mathematically. Optional: state the dictionary `ab = 4cos²(π/m)` in the docstring; note that `ha, hb, hab` are logically inert (§4c); note that `s1 a, s2 b` are the simple reflections of `cartan b a`, not `cartan a b` (§4d) |

Not `false as stated`: I have a checked proof. Not `stronger`: every clause is a five-pair
computation on the finite side. Not vacuous: each of the five cases has nonempty content (a
universal period plus witnesses for every smaller `m`). Not `misleading as named or documented`
in the repository's own terms, because `LIMITATIONS.md` states the limitation
("These are statements about the reflection model…", "does not prove that those reflections
generate a Coxeter group, nor that the model is faithful") — but that limitation is *not*
visible in the frozen statement or its docstring, so a reader meeting the docstring alone could
take "the Coxeter element" at group level. That is the substance of the two qualifications
below, and the reason I record `matches` rather than `matches` without comment.

## 4. True but not quite what it says

**(a) Carrier.** The proposition is about a self-map of `ℤ × ℤ`; the docstring's "the Coxeter
element" is a modelling identification. For *this* conclusion the loss is smaller than it looks:
`s1 a` and `s2 b` are involutions (`RankTwoCertificate.s1_involution`, `s2_involution`) and
their product has exact order `m`, so `s_i ↦ s_i` is a homomorphism `I₂(m) → GL₂(ℤ)`, and
`ord(image) | ord(s₁s₂) | m` together with `ord(image) = m` gives `ord(s₁s₂) = m`. So
faithfulness of the representation is **not** needed to pin down the order of the Coxeter
element — only the dictionary `ab = 4cos²(π/m)`, which the dictionary supplies. What the file
does not contain is that dictionary: nothing in `swarm/Statements.lean`, `swarm/Targets.lean` or
`RankTwoCertificate.lean` connects `ab` with `m`, with `titsForm`, or with any Coxeter matrix,
and the frozen definitions contain no group. So the statement certifies a numerical fact about
five matrices; the group-level sentence needs two further steps (dictionary; homomorphism and
exact-order argument) that are available but unrecorded.

**(b) Scope.** It is the finite crystallographic slice: the five pairs with `0 < a b ≤ 3`. It
says nothing about `H₂ = I₂(5)` (no integral representative), nothing about `ab ≥ 4`, nothing
about `ab = 0`, and nothing about the angle of the rotation — although, since `det = 1` and
`trace = 2cos(2π/m)`, each of the five maps is conjugate over `ℝ` to the rotation through
`±2π/m`, so the numerical content is exactly the rotation's order. `LIMITATIONS.md` states the
five-pair scope accurately; the docstring's parenthetical "`3` for `A₂`, `4` for `B₂`, `6` for
`G₂`" is correct but relies on the unformalized dictionary.

**(c) The hypotheses are logically inert.** `finite_exact_period` is true with `ha, hb, hab`
deleted: each antecedent `a*b = k` with `k ∈ {1,2,3}` and `a b : ℕ` already forces `a, b ≥ 1`
(`Nat.mul_eq_one` for `k = 1`; for `k = 2,3` a zero factor contradicts `k ≠ 0`), so the same
five-case analysis proves the hypothesis-free version, and `hab` is never used by any implicand
weakening it (e.g. to `a*b ≤ 4`) leaves the theorem true. So `1 ≤ a, 1 ≤ b` is *not* what
excludes `ab = 0` — the shape of the conjunction is — and the repository's prose ("that is why
the finite statement carries `1 ≤ a, 1 ≤ b`", `LIMITATIONS.md`) overstates their role. The
hypotheses are harmless and document intent, but they are not needed and they are certainly not
too weak: nothing is missing.

**(d) A convention mismatch.** Computed (`check2.py`): `s1 a = [[-1,a],[0,1]]` and
`s2 b = [[1,0],[b,-1]]` are the simple reflections `s_i(α_j) = α_j − a_{ji} α_i` of the Cartan
matrix `!![2,-b;-a,2]`, i.e. of `cartan b a`, not of `cartan a b = !![2,-a;-b,2]`. The pair in
this statement is therefore transposed relative to the repository's own `cartan`. Immaterial for
this statement (only `a*b` enters, and `(1,2)`/`(2,1)` are the same Coxeter group `I₂(4)`), but
it means the docstring's type labels are attached to the transposed matrix and a reader matching
`finite_exact_period` against `cartan a b` is matching the transposed pair.

## 5. Blindness

I did **not** open `RankTwoClassification.lean`, `swarm/Classification.lean`,
`swarm/selftest/`, `swarm/submissions/`, `swarm/RESULT.md`, `swarm/AUDIT.md`,
`swarm/REVIEW-PACKET.md`, any file under `swarm/review/` other than `AUDIT-BRIEF.md`, or
anything under `$REPO/.ultramath/` outside my own directory. Two disclosures: (i) I ran `ls -a`
and one `rg --files -g '*.olean'` at the repository root, which displayed the *names* of files on
the blindness list (and returned no olean files); no listed file was opened. (ii) I read only
`swarm/review/AUDIT-BRIEF.md`, `swarm/Statements.lean`, `swarm/Targets.lean`,
`RankTwoCertificate.lean`, `README.md` and `LIMITATIONS.md`, plus the printed table of contents
of Humphreys and the web excerpts cited above.

## 6. Sources: verified versus recalled

Verified in full text: Humphreys Ch. 1 §1.1 pp. 3–5 (the `I₂(m)` example and the rotation
through `2θ = 2π/m`); Bourbaki Ch. V §4 no. 2, Prop. 1 and its proof, Prop. 2 and Prop. 4(c)
(rotation of angle `2π/m`, order `m`, dihedral group of order `2m`, and `g_s g_{s'}` of order
`m(s,s')`); the section/page numbering of Humphreys (Ch. 1 §1.1; Ch. 2 §2.3 p. 31; Ch. 6 §6.4
p. 132, §6.6 p. 135; Ch. 3 §3.16–3.18 "Coxeter elements", "Action on a plane", "The Coxeter
number") and of Bourbaki (Ch. IV §1 no. 2 "Dihedral groups"; Ch. V §4).

Recalled rather than read in the book: the statement of Humphreys §6.6 (crystallographic ⇔
`m(s,t) ∈ {2,3,4,6}`), the content of Humphreys §3.18 (the Coxeter number `h` is the order of a
Coxeter element), and the formula `a_ij a_ji = 4cos²(π/m_ij)` obtained from the form
`B(α_s,α_t) = −cos(π/m(s,t))` in §2.3 (Bourbaki's §4 no. 1 gives the same form
`B_M(e_s,e_{s'}) = −cos(π/m(s,s'))`, which I did read). Both are standard; the numerical consequences
(`4cos²(π/3)=1`, `4cos²(π/4)=2`, `4cos²(π/6)=3`, `4cos²(π/2)=0`, `4cos² → 4` as `m → ∞`) I
computed rather than recalled.

Verification status by claim: the rotation/order statement (Humphreys §1.1, Bourbaki V §4 no. 1
Prop. 2) — verified. The crystallographic restriction `m ∈ {2,3,4,6}` — recalled, standard. The
matrix orders, traces, determinants, the case split and the truth of the statement — computed
and machine-checked here, not recalled.

## 7. Repository untouched

I did not modify `$REPO`. All files I created are in `.ultramath/smwbdn3dn/m1/`
(`audit-report.md`, `verify.lean`, `check.py`, `check2.py`, plus Lean build output). A read-only
`git --no-optional-locks status --porcelain` at the repository root returns no entries.
I audited no statement other than number 2; the arithmetic I ran on other targets (e.g.
`titsForm a b (a,2) = −2a(ab−4)`) is not a verdict on them.
