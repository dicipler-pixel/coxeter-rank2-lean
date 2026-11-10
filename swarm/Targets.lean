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

/-- The rank-two Cartan matrix with off-diagonal magnitudes `a`, `b`. -/
def cartan (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, -a; -b, 2]

/-- The symmetrised Tits form of `cartan a b`. For positive `a, b` the form is positive
definite exactly on `0 < a*b < 4`, has a one-dimensional radical at `a*b = 4`, and is
indefinite above. -/
def titsForm (a b : ℤ) (x y : ℝ) : ℝ :=
  2 * b * x ^ 2 - 2 * ((a * b : ℤ) : ℝ) * x * y + 2 * a * y ^ 2

end OperatorFirst.CoxeterRankTwo
