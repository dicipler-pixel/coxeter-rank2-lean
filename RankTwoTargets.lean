import Mathlib
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The objects the rank-two statements are about

Single source for `cartan`, `titsForm` and `titsBilin`. `swarm/Targets.lean` imports this module
and `RankTwoClassification.lean` too, so a submission cannot redefine the objects under a frozen
statement, and the two files that used to carry independent copies cannot drift apart.

`cartan a b = !![2, -a; -b, 2]` is the rank-two Cartan matrix with off-diagonal magnitudes `a`,
`b`; `titsForm` is the quadratic form of the symmetrised matrix `diag(b, a) * cartan a b`, and
`titsBilin` is its polar form.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- The rank-two Cartan matrix with off-diagonal magnitudes `a`, `b`. It is a generalised
Cartan matrix in Kac's sense (`a_ij ≤ 0` for `i ≠ j`, and `a_ij = 0 ⟺ a_ji = 0`) only when
`a, b ≥ 0` and `a = 0 ⟺ b = 0`; the determinant identity holds for all `a, b : ℤ`.

One convention to keep straight: the reflection pair of `RankTwoCertificate` (`s1 a`, `s2 b`)
satisfies `s_i(α_j) = α_j - a_{ji} α_i` for the matrix `cartan b a`, i.e. the transpose of the
matrix named here. Nothing in the statements is affected — they all depend on `a*b` alone, and
`titsForm a b x y = titsForm b a y x` — but the two writings should not be confused. -/
def cartan (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, -a; -b, 2]

/-- The symmetrised Tits form of `cartan a b`: the Gram matrix is `diag(b, a) * cartan a b`, that
is `!![2b, -ab; -ab, 2a]`, giving `2 b x² - 2 (a b) x y + 2 a y²`.

For `1 ≤ a, b` the library proves the whole trichotomy: positive definite when `a*b ≤ 3`,
nonnegative when `a*b = 4` with `(a, 2)` in the radical of `titsBilin`, hence degenerate there, and
indefinite when `4 < a*b`.

At `(a, b) = (0, 0)` the symmetriser degenerates and the form is identically zero, which is why the
statements carry `1 ≤ a, b`. The converses — that positive definiteness forces `a*b ≤ 3` and
semidefiniteness `a*b ≤ 4` — are not stated here. -/
def titsForm (a b : ℤ) (x y : ℝ) : ℝ :=
  2 * b * x ^ 2 - 2 * ((a * b : ℤ) : ℝ) * x * y + 2 * a * y ^ 2

/-- The polar form of `titsForm`: `titsBilin a b v v = titsForm a b v.1 v.2`, and
`titsBilin a b u v = (Q(u+v) - Q(u) - Q(v))/2`. This is the form whose radical carries the
degeneracy statement: at `a * b = 4` its value at `((a, 2), (x, y))` is `a y (4 - a b)`. -/
def titsBilin (a b : ℤ) (u v : ℝ × ℝ) : ℝ :=
  2 * b * u.1 * v.1 - ((a * b : ℤ) : ℝ) * (u.1 * v.2 + u.2 * v.1) + 2 * a * u.2 * v.2

/-- `titsForm` as a genuine `QuadraticForm` on `ℝ²`, so that Mathlib's signature theory applies:
the matrix `!![2b, -ab; -ab, 2a]` sent through `Matrix.toQuadraticForm'`. -/
noncomputable def titsQF (a b : ℤ) : QuadraticForm ℝ (Fin 2 → ℝ) :=
  (!![2 * (b : ℝ), -((a : ℝ) * (b : ℝ)); -((a : ℝ) * (b : ℝ)), 2 * (a : ℝ)] :
    Matrix (Fin 2) (Fin 2) ℝ).toQuadraticForm'

/-- The `QuadraticForm` and the packaged form agree. -/
@[simp] lemma titsQF_apply (a b : ℤ) (v : Fin 2 → ℝ) :
    titsQF a b v = titsForm a b (v 0) (v 1) := by
  simp only [titsQF, titsForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val']
  push_cast
  ring

end OperatorFirst.CoxeterRankTwo
