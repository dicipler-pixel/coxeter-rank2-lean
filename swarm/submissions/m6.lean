import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

theorem step_two_one_exact : HasExactPeriod (step 2 1) 4 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y⟩
    ext <;> simp [iter, step, s1, s2] <;> ring
  · intro m hm hlt
    refine ⟨(1, 0), ?_⟩
    interval_cases m <;> norm_num [iter, step, s1, s2] at *

theorem step_three_one_exact : HasExactPeriod (step 3 1) 6 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, y⟩
    ext <;> simp [iter, step, s1, s2] <;> ring
  · intro m hm hlt
    refine ⟨(1, 0), ?_⟩
    interval_cases m <;> norm_num [iter, step, s1, s2] at *

/-- For every `a, b ≥ 1` with `a*b ≤ 3`, the Coxeter element has the exact period the
finite type prescribes: `3` for `A₂`, `4` for `B₂`, `6` for `G₂`. -/
theorem finite_exact_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    (a * b = 1 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 3) ∧
      (a * b = 2 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 4) ∧
        (a * b = 3 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 6) := by
  have ha3 : a ≤ 3 := by
    calc
      a = a * 1 := by simp
      _ ≤ a * b := Nat.mul_le_mul_left a hb
      _ ≤ 3 := hab
  have hb3 : b ≤ 3 := by
    calc
      b = 1 * b := by simp
      _ ≤ a * b := Nat.mul_le_mul_right b ha
      _ ≤ 3 := hab
  interval_cases a <;> interval_cases b
  all_goals first
    | (exfalso; omega)
    | norm_num at ⊢
  all_goals first
    | exact U3_exact
    | exact U4_exact
    | exact step_two_one_exact
    | exact U6_exact
    | exact step_three_one_exact

end OperatorFirst.CoxeterRankTwo
