import Targets

set_option autoImplicit false

/-!
# Period five in the rank-two reflection model

Route: `step A B` satisfies the *quadratic* relation `T² = t·T - 1` with `t = A*B - 2`
(one coordinate computation).  From it, the geometric sum collapses:

    T⁴ + T³ + T² + T + 1 = T² · (t² + t - 1),

which is the factorisation of `X⁵ - 1 = (X - 1)(X⁴ + X³ + X² + X + 1)` pushed through the
relation.  A universal period `T⁵ = 1` makes that sum a fixed vector, so
`(t² + t - 1) · (T²v)` is fixed.  `T` is invertible (`T(t - T) = 1`), so `T²` is onto, and

    (t² + t - 1) · (Tw - w) = 0   for all `w`.

Exactness at `m = 1` supplies `w` with `Tw ≠ w`; `ℤ × ℤ` is torsion free, hence
`t² + t - 1 = 0`, i.e. `(A B)² - 3 (A B) + 1 = 0`.
-/

namespace OperatorFirst.CoxeterRankTwo

/-! ## Coordinate and linearity facts for `step` -/

private lemma step_apply (A B x y : ℤ) :
    step A B (x, y) = ((A * B - 1) * x - A * y, B * x - y) := by
  ext <;> simp [step, s1, s2] <;> ring

private lemma step_add (A B : ℤ) (u v : V) :
    step A B (u + v) = step A B u + step A B v := by
  rcases u with ⟨x₁, y₁⟩
  rcases v with ⟨x₂, y₂⟩
  ext <;> simp [step, s1, s2] <;> ring

private lemma step_smul (A B : ℤ) (c : ℤ) (v : V) :
    step A B (c • v) = c • step A B v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

private lemma step_sub (A B : ℤ) (u v : V) :
    step A B (u - v) = step A B u - step A B v := by
  rcases u with ⟨x₁, y₁⟩
  rcases v with ⟨x₂, y₂⟩
  ext <;> simp [step, s1, s2] <;> ring

/-- The characteristic relation of the Coxeter step: `T² = t·T - 1` with `t = A*B - 2`. -/
private lemma step_sq (A B : ℤ) (v : V) :
    step A B (step A B v) = (A * B - 2) • step A B v - v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

/-- Iterating `step` advances the natural index.  Holds by definition of `iter`. -/
private lemma step_iter (A B : ℤ) (k : ℕ) (v : V) :
    step A B (iter (step A B) k v) = iter (step A B) (k + 1) v := rfl

/-! ## Target one -/

private theorem golden_of_period_five (A B : ℤ) (h : HasExactPeriod (step A B) 5) :
    (A * B) ^ 2 - 3 * (A * B) + 1 = 0 := by
  obtain ⟨hper, hmin⟩ := h
  set t : ℤ := A * B - 2 with ht
  have hsq : ∀ v : V, step A B (step A B v) = t • step A B v - v := by
    intro v
    rw [ht]
    exact step_sq A B v
  -- the geometric sum as a five-term `iter` sum
  have hG : ∀ v : V,
      iter (step A B) 4 v + iter (step A B) 3 v + iter (step A B) 2 v
          + iter (step A B) 1 v + iter (step A B) 0 v
        = (t ^ 2 + t - 1) • (iter (step A B) 2 v) := by
    intro v
    rcases v with ⟨x, y⟩
    ext <;> simp [iter, step, s1, s2, ht] <;> ring
  -- `step` fixes the geometric sum
  have hfix_sum : ∀ v : V,
      step A B (iter (step A B) 4 v + iter (step A B) 3 v + iter (step A B) 2 v
          + iter (step A B) 1 v + iter (step A B) 0 v)
        = iter (step A B) 4 v + iter (step A B) 3 v + iter (step A B) 2 v
          + iter (step A B) 1 v + iter (step A B) 0 v := by
    intro v
    rw [step_add, step_add, step_add, step_add]
    rw [step_iter, step_iter, step_iter, step_iter, step_iter]
    rw [hper v]
    simp only [iter]
    abel
  -- hence `(t²+t-1) • T²v` is a fixed vector
  have hfix : ∀ v : V,
      step A B ((t ^ 2 + t - 1) • iter (step A B) 2 v) =
        (t ^ 2 + t - 1) • iter (step A B) 2 v := by
    intro v
    have h1 := hfix_sum v
    rw [hG v] at h1
    exact h1
  -- `step` is onto
  have hsurj : ∀ u : V, ∃ w : V, step A B w = u := by
    intro u
    refine ⟨t • u - step A B u, ?_⟩
    rw [step_sub, step_smul, hsq u]
    abel
  -- so `(t²+t-1)·(Tw - w) = 0` for every `w`
  have key : ∀ w : V, (t ^ 2 + t - 1) • (step A B w - w) = 0 := by
    intro w
    obtain ⟨u, hu⟩ := hsurj w
    obtain ⟨v, hv⟩ := hsurj u
    have h1 := hfix v
    have hiter2 : iter (step A B) 2 v = w := by
      show step A B (step A B v) = w
      rw [hv, hu]
    rw [hiter2, step_smul] at h1
    rw [smul_sub, h1, sub_self]
  -- exactness at `m = 1` gives a witness that `step` moves
  obtain ⟨u, hu⟩ := hmin 1 (by norm_num) (by norm_num)
  have humove : step A B u - u ≠ 0 := by
    intro h0
    exact hu (sub_eq_zero.mp h0)
  have hc : t ^ 2 + t - 1 = 0 := by
    have h0 := key u
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 humove
  rw [ht] at hc
  linear_combination hc

theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  have h1 := golden_of_period_five (a : ℤ) (b : ℤ) h
  have hcast : ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := by push_cast; ring
  rw [hcast]
  exact h1

/-! ## Target two: no integral period five -/

theorem no_integral_period_five (a b : ℕ) :
    ¬ HasExactPeriod (step (a : ℤ) (b : ℤ)) 5 := by
  intro h
  have h1 := order_five_forces_golden_trace a b h
  have key : ∀ n : ℤ, n ^ 2 - 3 * n + 1 = 0 → False := by
    intro n hn
    have h2 : ((n : ZMod 2)) ^ 2 - 3 * (n : ZMod 2) + 1 = 0 := by
      have h3 : ((n ^ 2 - 3 * n + 1 : ℤ) : ZMod 2) = 0 := by rw [hn]; norm_num
      simpa using h3
    have huniv : ∀ x : ZMod 2, x ^ 2 - 3 * x + 1 ≠ 0 := by
      intro x
      fin_cases x <;> decide
    exact huniv (n : ZMod 2) h2
  exact key _ h1

end OperatorFirst.CoxeterRankTwo
