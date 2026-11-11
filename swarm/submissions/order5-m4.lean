import Targets

set_option autoImplicit false

/-!
# Period five in the rank-two reflection model

The Coxeter step `T = step A B` satisfies `T²v = t • T v - v` with `t = A*B - 2`, so the fifth
iterate is `T⁵v = (t⁴ - 3t² + 1) • T v - (t³ - 2t) • v`.  Here everything is computed in
coordinates: `T` is linear, so the fifth iterate is a polynomial map whose coefficients are
computed by one `ring` call.  Evaluating the period-five identity `T⁵ v = v` at `(0,1)` and
`(1,0)` yields `(t⁴-3t²+1) • T v = (t³-2t+1) • v`, hence
`(t⁴-3t²+1) * A = 0`, `(t⁴-3t²+1) * B = 0`, and the second coordinate at `(0,1)` gives
`(t³-2t+1) = -(t⁴-3t²+1)`.  Either `t⁴-3t²+1 = 0`, and then `t² + t - 1 = 0` because
`t*(t³-2t+1) - (t⁴-3t²+1) = t²+t-1`; or it is nonzero, the two products force `A = B = 0`,
and then `T = -id` has period two, contradicting exact period five.
-/

namespace OperatorFirst.CoxeterRankTwo

/-! ## Coordinate computations -/

/-- The step in coordinates. -/
lemma step_apply (A B x y : ℤ) :
    step A B (x, y) = ((A * B - 1) * x - A * y, B * x - y) := by
  simp only [step, s1, s2]
  ext <;> ring

/-- At `A = B = 0` the step is the negation. -/
@[simp] lemma step_zero_zero (v : V) : step 0 0 v = -v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step_apply]

/-- The fifth iterate of the step, in coordinates.  Obtained by unfolding the recursion and
normalising; the two coefficients are the Chebyshev-type polynomials `f₅ = t⁴ - 3t² + 1` and
`f₄ = t³ - 2t` at `t = A*B - 2`. -/
lemma iter_five_coord (A B x y : ℤ) :
    iter (step A B) 5 (x, y) =
      (((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * ((A * B - 1) * x - A * y)
          - ((A * B - 2) ^ 3 - 2 * (A * B - 2)) * x,
        ((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * (B * x - y)
          - ((A * B - 2) ^ 3 - 2 * (A * B - 2)) * y) := by
  ext <;> simp only [iter, step, s1, s2] <;> ring

/-- First coordinate of the fifth iterate at `(0,1)`. -/
lemma iter_five_fst_zero_one (A B : ℤ) :
    (iter (step A B) 5 (0, 1)).1 =
      -(((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * A) := by
  rw [iter_five_coord]
  ring

/-- Second coordinate of the fifth iterate at `(0,1)`. -/
lemma iter_five_snd_zero_one (A B : ℤ) :
    (iter (step A B) 5 (0, 1)).2 =
      -((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) - ((A * B - 2) ^ 3 - 2 * (A * B - 2)) := by
  rw [iter_five_coord]
  ring

/-- Second coordinate of the fifth iterate at `(1,0)`. -/
lemma iter_five_snd_one_zero (A B : ℤ) :
    (iter (step A B) 5 (1, 0)).2 = ((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * B := by
  rw [iter_five_coord]
  ring

/-! ## The integral form of the statement -/

/-- Period five forces the golden relation on the product `A*B`, for integral `A`, `B`. -/
lemma golden_of_period_five (A B : ℤ) (h : HasExactPeriod (step A B) 5) :
    (A * B) ^ 2 - 3 * (A * B) + 1 = 0 := by
  obtain ⟨hper, hexact⟩ := h
  -- the second coordinate at `(0,1)`: `-(F₅) - F₄ = 1`
  have hsnd : -((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1)
      - ((A * B - 2) ^ 3 - 2 * (A * B - 2)) = 1 := by
    have h0 := congrArg Prod.snd (hper (0, 1))
    rw [iter_five_snd_zero_one] at h0
    simpa using h0
  -- the first coordinate at `(0,1)`: `F₅ * A = 0`
  have hA : ((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * A = 0 := by
    have h0 := congrArg Prod.fst (hper (0, 1))
    rw [iter_five_fst_zero_one] at h0
    exact neg_eq_zero.mp h0
  -- the second coordinate at `(1,0)`: `F₅ * B = 0`
  have hB : ((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) * B = 0 := by
    have h0 := congrArg Prod.snd (hper (1, 0))
    rw [iter_five_snd_one_zero] at h0
    simpa using h0
  -- `F₅ = -(F₄ + 1)`, i.e. `t³ - 2t + 1 = -(t⁴ - 3t² + 1)`
  have hkey : ((A * B - 2) ^ 3 - 2 * (A * B - 2)) + 1
      = -((A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1) := by
    linarith
  by_cases hF : (A * B - 2) ^ 4 - 3 * (A * B - 2) ^ 2 + 1 = 0
  · -- `F₅ = 0` also gives `F₄ + 1 = 0`, and `t*(t³-2t+1) - (t⁴-3t²+1) = t² + t - 1`
    have h4 : (A * B - 2) ^ 3 - 2 * (A * B - 2) + 1 = 0 := by
      rw [hF] at hkey
      linarith
    have h5 : (A * B - 2) ^ 2 + (A * B - 2) - 1 = 0 := by
      linear_combination (A * B - 2) * h4 - hF
    have hAB : A * B = (A * B - 2) + 2 := by ring
    rw [hAB]
    linear_combination h5
  · -- otherwise `A = B = 0`, and then the step is `-id`, of period two
    have hA0 : A = 0 := (mul_eq_zero.mp hA).resolve_left hF
    have hB0 : B = 0 := (mul_eq_zero.mp hB).resolve_left hF
    exfalso
    have htwo : ∀ v : V, iter (step A B) 2 v = v := by
      intro v
      rw [hA0, hB0]
      have e : iter (step 0 0) 2 v = step 0 0 (step 0 0 v) := rfl
      rw [e, step_zero_zero, step_zero_zero, neg_neg]
    obtain ⟨x, hx⟩ := hexact 2 (by norm_num) (by norm_num)
    exact hx (htwo x)

/-! ## The frozen targets -/

theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  have key := golden_of_period_five (a : ℤ) (b : ℤ) h
  have hcast : ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := Nat.cast_mul ..
  rw [hcast]
  exact key

theorem no_integral_period_five (a b : ℕ) :
    ¬ HasExactPeriod (step (a : ℤ) (b : ℤ)) 5 := by
  intro h
  have h1 := order_five_forces_golden_trace a b h
  have h2 : (((a * b : ℕ) : ℤ) : ZMod 2) ^ 2 - 3 * (((a * b : ℕ) : ℤ) : ZMod 2) + 1 = 0 := by
    have h0 := congrArg (fun z : ℤ => (z : ZMod 2)) h1
    simpa using h0
  have h3 : ∀ x : ZMod 2, x ^ 2 - 3 * x + 1 = 1 := by decide
  have h4 : (1 : ZMod 2) = 0 := by
    rw [← h3 ((((a * b : ℕ) : ℤ)) : ZMod 2)]
    exact h2
  exact one_ne_zero h4

end OperatorFirst.CoxeterRankTwo
