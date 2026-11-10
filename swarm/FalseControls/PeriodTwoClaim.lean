import Targets

/-! Deliberately false: `step 1 1` has exact period `3`, so its square is not the
identity. A gate that accepts this file is not checking anything. -/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

example : iter (step 1 1) 2 (1, 0) = (1, 0) := by
  norm_num [iter, step, s1, s2]

end OperatorFirst.CoxeterRankTwo
