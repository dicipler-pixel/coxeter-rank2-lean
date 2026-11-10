import Targets

/-!
# Gate self-test: the targets that are already proved

Four of the twelve frozen statements, proved. Used to check the gate's pass path:
`python3 scripts/gate.py --submission swarm/selftest/Good.lean --partial` must PASS,
and it must FAIL on any of the twelve `sorry` bodies.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

theorem cartan_det (a b : ℤ) : (cartan a b).det = 4 - a * b := by
  simp [cartan, Matrix.det_fin_two]

theorem tits_vanishes_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 = 0 := by
  have key : titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2
      = 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) := by
    simp only [titsForm]
    push_cast
    ring
  rw [key]
  have h : (a : ℝ) * (b : ℝ) = 4 := by
    have h4 : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
    push_cast at h4
    linarith
  rw [h]
  ring

theorem tits_negative_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 < 0 := by
  have key : titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2
      = 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) := by
    simp only [titsForm]
    push_cast
    ring
  rw [key]
  have ha' : (0 : ℝ) < (a : ℝ) := by
    have : (0 : ℕ) < a := by omega
    exact_mod_cast this
  have hab' : (4 : ℝ) < (a : ℝ) * (b : ℝ) := by
    have h : ((4 : ℕ) : ℝ) < ((a * b : ℕ) : ℝ) := by exact_mod_cast hab
    push_cast at h
    linarith
  nlinarith

theorem golden_product_eq_four_cos_sq :
    4 * Real.cos (Real.pi / 5) ^ 2 = (3 + Real.sqrt 5) / 2 := by
  rw [Real.cos_pi_div_five]
  have hs : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

end OperatorFirst.CoxeterRankTwo
