import Targets

/-!
# Period five in the rank-two reflection model

`step a b` is the Coxeter element `s₁ a ∘ s₂ b` on `V = ℤ × ℤ`.  Writing `t = ab - 2`, the
characteristic relation is

  `step a b (step a b v) = t • step a b v - v`,

and five applications of it give

  `iter (step a b) 5 v = (t⁴ - 3t² + 1) • step a b v - (t³ - 2t) • v`.

If the step has exact period five the left side is `v`, so `c • step a b v = (d + 1) • v`
with `c = t⁴ - 3t² + 1` and `d = t³ - 2t`.  Reading the two coordinates of that identity at
the basis vectors `(1, 0)` and `(0, 1)` gives `c * a = 0` and `c * b = 0`, so `c = 0` unless
`a = b = 0`, and `c = 0` together with `d = -1` forces `t² + t - 1 = 0`, i.e.
`(ab)² - 3(ab) + 1 = 0`.  The residual case `a = b = 0` is the negation `-id`, whose period
is two, not five.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-! ## The step, its square, and its fifth iterate -/

/-- Coordinate formula for the Coxeter step. -/
theorem step_formula (a b : ℤ) (x y : ℤ) :
    step a b (x, y) = ((a * b - 1) * x - a * y, b * x - y) := by
  simp only [step, s1, s2]
  refine Prod.ext ?_ ?_ <;> simp <;> ring

/-- The characteristic relation: `T² v = (ab - 2) • T v - v`. -/
theorem step_sq_char (a b : ℤ) (v : V) :
    step a b (step a b v) = (a * b - 2) • step a b v - v := by
  obtain ⟨x, y⟩ := v
  simp only [step_formula, Prod.smul_mk, Prod.mk_sub_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> ring

/-- The coefficient of `step a b v` in `T⁵ v = c • T v - d • v`, with `t = ab - 2`. -/
def c5 (a b : ℤ) : ℤ := (a * b - 2) ^ 4 - 3 * (a * b - 2) ^ 2 + 1

/-- The coefficient of `v` in `T⁵ v = c • T v - d • v`, with `t = ab - 2`. -/
def d5 (a b : ℤ) : ℤ := (a * b - 2) ^ 3 - 2 * (a * b - 2)

/-- First coordinate of the fifth iterate. -/
theorem iter5_fst (a b : ℤ) (x y : ℤ) :
    (iter (step a b) 5 (x, y)).1 = c5 a b * ((a * b - 1) * x - a * y) - d5 a b * x := by
  simp only [iter, step_formula, c5, d5]
  ring

/-- Second coordinate of the fifth iterate. -/
theorem iter5_snd (a b : ℤ) (x y : ℤ) :
    (iter (step a b) 5 (x, y)).2 = c5 a b * (b * x - y) - d5 a b * y := by
  simp only [iter, step_formula, c5, d5]
  ring

/-! ## T1: exact order five forces the golden trace -/

theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  have h10f : (iter (step (a : ℤ) (b : ℤ)) 5 (1, 0)).1 = 1 := by
    have hh := congrArg Prod.fst (h.1 (1, 0))
    simpa using hh
  have h10s : (iter (step (a : ℤ) (b : ℤ)) 5 (1, 0)).2 = 0 := by
    have hh := congrArg Prod.snd (h.1 (1, 0))
    simpa using hh
  have h01f : (iter (step (a : ℤ) (b : ℤ)) 5 (0, 1)).1 = 0 := by
    have hh := congrArg Prod.fst (h.1 (0, 1))
    simpa using hh
  have h01s : (iter (step (a : ℤ) (b : ℤ)) 5 (0, 1)).2 = 1 := by
    have hh := congrArg Prod.snd (h.1 (0, 1))
    simpa using hh
  have keyA : (1 : ℤ) = c5 (a : ℤ) (b : ℤ) * ((a : ℤ) * (b : ℤ) - 1) - d5 (a : ℤ) (b : ℤ) := by
    have hh := iter5_fst (a : ℤ) (b : ℤ) 1 0
    rw [h10f] at hh
    simpa using hh
  have keyB : c5 (a : ℤ) (b : ℤ) * (b : ℤ) = 0 := by
    have hh := iter5_snd (a : ℤ) (b : ℤ) 1 0
    rw [h10s] at hh
    simp only [mul_one, sub_zero, mul_zero] at hh
    linarith
  have keyC : c5 (a : ℤ) (b : ℤ) * (a : ℤ) = 0 := by
    have hh := iter5_fst (a : ℤ) (b : ℤ) 0 1
    rw [h01f] at hh
    simp only [mul_zero, zero_sub, mul_one, mul_neg] at hh
    linarith
  have keyD : (1 : ℤ) = -c5 (a : ℤ) (b : ℤ) - d5 (a : ℤ) (b : ℤ) := by
    have hh := iter5_snd (a : ℤ) (b : ℤ) 0 1
    rw [h01s] at hh
    simp only [mul_zero, zero_sub, mul_one, mul_neg] at hh
    simpa using hh
  by_cases hz : a = 0 ∧ b = 0
  · obtain ⟨ha0, hb0⟩ := hz
    obtain ⟨x, hx⟩ := h.2 2 (by norm_num) (by norm_num)
    obtain ⟨p, q⟩ := x
    have hcon : iter (step (a : ℤ) (b : ℤ)) 2 (p, q) = (p, q) := by
      have ha' : (a : ℤ) = 0 := by simp [ha0]
      have hb' : (b : ℤ) = 0 := by simp [hb0]
      rw [ha', hb']
      simp [iter, step_formula]
    exact absurd hcon hx
  · have hne : (a : ℤ) ≠ 0 ∨ (b : ℤ) ≠ 0 := by
      rcases eq_or_ne a 0 with ha0 | ha0
      · rcases eq_or_ne b 0 with hb0 | hb0
        · exact absurd ⟨ha0, hb0⟩ hz
        · exact Or.inr (by intro hh; exact hb0 (by exact_mod_cast hh))
      · exact Or.inl (by intro hh; exact ha0 (by exact_mod_cast hh))
    have hC : c5 (a : ℤ) (b : ℤ) = 0 := by
      rcases hne with ha | hb
      · exact (mul_eq_zero.mp keyC).resolve_right ha
      · exact (mul_eq_zero.mp keyB).resolve_right hb
    have hD' : d5 (a : ℤ) (b : ℤ) + 1 = 0 := by
      rw [hC] at keyD
      linarith
    have ht : ((a : ℤ) * (b : ℤ) - 2) ^ 2 + ((a : ℤ) * (b : ℤ) - 2) - 1 = 0 := by
      rw [c5] at hC
      rw [d5] at hD'
      linear_combination ((a : ℤ) * (b : ℤ) - 2) * hD' - hC
    have hgoal : ((a : ℤ) * (b : ℤ)) ^ 2 - 3 * ((a : ℤ) * (b : ℤ)) + 1 = 0 := by
      linear_combination ht
    have hcast : ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact hgoal

/-! ## T2: no integral pair has exact order five -/

theorem no_integral_period_five (a b : ℕ) :
    ¬ HasExactPeriod (step (a : ℤ) (b : ℤ)) 5 := by
  intro h
  have hgold := order_five_forces_golden_trace a b h
  have hmod : ((a * b : ℕ) : ZMod 2) ^ 2 - 3 * ((a * b : ℕ) : ZMod 2) + 1 = 0 := by
    have hz : (((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 : ℤ) = 0 := hgold
    have hh := congrArg (fun z : ℤ => (z : ZMod 2)) hz
    push_cast at hh
    simpa using hh
  have hfin : ∀ n : ZMod 2, n ^ 2 - 3 * n + 1 ≠ 0 := by
    intro n
    fin_cases n <;> decide
  exact hfin _ hmod

end OperatorFirst.CoxeterRankTwo
