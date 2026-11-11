import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- The characteristic-polynomial identity for the rank-two step: trace `a*b - 2`, determinant 1. -/
lemma step_sq_char (a b : ℤ) (v : V) :
    step a b (step a b v) = (a * b - 2) • step a b v - v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

/-- The fifth iterate, in coordinates: with `t = a*b-2` one has
`T⁵ = (t⁴-3t²+1)·T - (t³-2t)·1` as an operator on `ℤ × ℤ`.  Proved by unfolding the
five applications and normalising the resulting polynomials. -/
lemma step_iter_five (a b : ℤ) (x y : ℤ) :
    iter (step a b) 5 (x, y) =
      (((a * b - 2) ^ 4 - 3 * (a * b - 2) ^ 2 + 1) * ((a * b - 1) * x - a * y)
          - ((a * b - 2) ^ 3 - 2 * (a * b - 2)) * x,
        ((a * b - 2) ^ 4 - 3 * (a * b - 2) ^ 2 + 1) * (b * x - y)
          - ((a * b - 2) ^ 3 - 2 * (a * b - 2)) * y) := by
  simp only [iter, step, s1, s2, Prod.mk.injEq]
  constructor <;> ring

theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  set t : ℤ := (a : ℤ) * (b : ℤ) - 2 with ht
  set s : ℤ := t ^ 4 - 3 * t ^ 2 + 1 with hs
  set u : ℤ := t ^ 3 - 2 * t with hu
  -- the operator identity `T⁵ = s·T - u·1` in coordinates, with `a*b - 1` written as `t + 1`
  have key : ∀ x y : ℤ, iter (step (a : ℤ) (b : ℤ)) 5 (x, y) =
      (s * ((t + 1) * x - (a : ℤ) * y) - u * x, s * ((b : ℤ) * x - y) - u * y) := by
    intro x y
    have h' := step_iter_five (a : ℤ) (b : ℤ) x y
    rw [← ht, ← hs, ← hu] at h'
    rw [show (a : ℤ) * (b : ℤ) - 1 = t + 1 from by rw [ht]; ring] at h'
    exact h'
  -- second coordinate at `(0,1)`, where `T (0,1) = (-a,-1)`
  have hC : s + u = -1 := by
    have e := key 0 1
    rw [h.1 (0, 1)] at e
    have e2 := congrArg Prod.snd e
    simp at e2
    linarith
  -- first coordinate at `(1,0)`, where `T (1,0) = (t+1,b)`
  have hB : s * (t + 1) = 1 + u := by
    have e := key 1 0
    rw [h.1 (1, 0)] at e
    have e1 := congrArg Prod.fst e
    simp at e1
    linarith
  -- hence `s * (t + 2) = 0`
  have hs2 : s * (t + 2) = 0 := by nlinarith
  have hs0 : s = 0 := by
    rcases mul_eq_zero.mp hs2 with h1 | h1
    · exact h1
    · exfalso
      have ht2 : t = -2 := by linarith
      have hs5 : s = 5 := by rw [hs, ht2]; norm_num
      have hu4 : u = -4 := by rw [hu, ht2]; norm_num
      linarith
  -- and then `u = -1`, so that `s - t*u = -t²+1` gives `t² + t - 1 = 0`
  have hu1 : u = -1 := by linarith
  have hpoly : t ^ 2 + t - 1 = 0 := by
    have hid : s - t * u = -t ^ 2 + 1 := by rw [hs, hu]; ring
    rw [hs0, hu1] at hid
    linarith
  have hN : ((a * b : ℕ) : ℤ) = t + 2 := by
    rw [ht]
    push_cast
    ring
  rw [hN]
  nlinarith

/-- `n² - 3n + 1` never vanishes on the integers: it equals `n(n-1) - 2n + 1`, and `n(n-1)` is
even, so the value is odd. -/
lemma int_sq_sub_three_mul_add_one_ne_zero (N : ℤ) : N ^ 2 - 3 * N + 1 ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self N
  have htwo : N * (N - 1) = 2 * k := by
    rw [hk]; ring
  have hodd : N ^ 2 - 3 * N + 1 = 2 * (k - N) + 1 := by
    nlinarith [htwo]
  rw [hzero] at hodd
  omega

theorem no_integral_period_five (a b : ℕ) :
    ¬ HasExactPeriod (step (a : ℤ) (b : ℤ)) 5 := fun h =>
  int_sq_sub_three_mul_add_one_ne_zero (((a * b : ℕ) : ℤ))
    (order_five_forces_golden_trace a b h)

end OperatorFirst.CoxeterRankTwo
