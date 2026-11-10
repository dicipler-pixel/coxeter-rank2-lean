import Targets

/-! Deliberately false: at `a*b = 5` the vector `(1, 2)` gives `2*5 - 2*5*2 + 2*4 = -2`,
so it is not in the radical; `a*b = 4` is the only degenerate product. -/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

example : titsForm 1 5 (1 : ℝ) 2 = 0 := by
  norm_num [titsForm]

end OperatorFirst.CoxeterRankTwo
