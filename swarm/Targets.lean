import Mathlib
import RankTwoCertificate

/-!
# Frozen definitions for the rank-two classification targets

A submission imports this module (never redefines it), so the objects the target
statements talk about are fixed by the repository and not by whoever writes the proof.
`swarm/Statements.lean` states the targets; `scripts/gate.py` compiles both.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- The rank-two Cartan matrix with off-diagonal magnitudes `a`, `b`. It is a generalised
Cartan matrix in Kac's sense (`a_ij ≤ 0` for `i ≠ j`, and `a_ij = 0 ⟺ a_ji = 0`) only when
`a, b ≥ 0` and `a = 0 ⟺ b = 0`; the determinant identity below holds for all `a, b : ℤ`. -/
def cartan (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, -a; -b, 2]

/-- The symmetrised Tits form of `cartan a b`, symmetriser `diag b a`. What the targets prove is
positive definiteness for `1 ≤ a, b` with `a*b ≤ 3`, vanishing at `(a, 2)` for `a*b = 4`, and
negativity at `(a, 2)` above. That `(a, 2)` spans the radical at `a*b = 4`
(`B((a,2),(x,y)) = a*y*(4 - a*b)`) and that the form is indefinite above are true but are *not*
formalized here; `LIMITATIONS.md` says so. -/
def titsForm (a b : ℤ) (x y : ℝ) : ℝ :=
  2 * b * x ^ 2 - 2 * ((a * b : ℤ) : ℝ) * x * y + 2 * a * y ^ 2

end OperatorFirst.CoxeterRankTwo
