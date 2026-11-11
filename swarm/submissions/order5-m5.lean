import Targets

/-!
# Period five in the rank-two reflection model, by explicit matrix powers

`step a b` is the Coxeter element `s₁ a ∘ s₂ b` on `V = ℤ × ℤ`.  This file records it as the
`2 × 2` integer matrix `M a b = !![ab - 1, -a; b, -1]` (trace `ab - 2`, determinant `1`), shows
that iterating the step is multiplying by powers of that matrix, and computes the fifth power
entrywise:

  `(M a b)⁵ = (t⁴ - 3t² + 1) • M a b - (t³ - 2t) • 1`,  `t = ab - 2`.

Exact period five says `(M a b)⁵ = 1`.  Comparing the entries `(0,1)`, `(1,0)` and `(1,1)` of
that identity gives `c * a = 0`, `c * b = 0` and `-c - d = 1`, where `c = t⁴ - 3t² + 1` and
`d = t³ - 2t`; hence `c = 0` unless `a = b = 0`, and then `t² + t - 1 = 0`, i.e.
`(ab)² - 3(ab) + 1 = 0`.  The residual case `a = b = 0` is `-id`, period two.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

open Matrix

/-! ## The matrix of the step -/

/-- The matrix of `step a b`: `trace = ab - 2`, `det = 1`. -/
def M (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![a * b - 1, -a; b, -1]

/-- The column vector of a pair. -/
def toVec (v : V) : Fin 2 → ℤ := ![v.1, v.2]

/-- The pair of a column vector. -/
def ofVec (w : Fin 2 → ℤ) : V := (w 0, w 1)

/-- The coefficient of `M a b` in `M⁵ = c • M - d • 1`, with `t = ab - 2`. -/
def c5 (a b : ℤ) : ℤ := (a * b - 2) ^ 4 - 3 * (a * b - 2) ^ 2 + 1

/-- The coefficient of `1` in `M⁵ = c • M - d • 1`, with `t = ab - 2`. -/
def d5 (a b : ℤ) : ℤ := (a * b - 2) ^ 3 - 2 * (a * b - 2)

theorem toVec_ofVec (w : Fin 2 → ℤ) : toVec (ofVec w) = w := by
  funext i
  fin_cases i <;> simp [toVec, ofVec]

/-- The two entries of a matrix-vector product. -/
theorem mulVec_two (P : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ) :
    P *ᵥ ![x, y] = ![P 0 0 * x + P 0 1 * y, P 1 0 * x + P 1 1 * y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The step is multiplication by `M a b`. -/
theorem step_eq_mulVec (a b : ℤ) (v : V) :
    step a b v = ofVec (M a b *ᵥ toVec v) := by
  obtain ⟨x, y⟩ := v
  simp only [toVec, ofVec, mulVec_two, M]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  simp only [step, s1, s2, Prod.mk.injEq]
  constructor <;> ring

/-- Iterating the step `n` times is multiplying by the `n`-th power of `M a b`. -/
theorem iter_eq_pow (a b : ℤ) (n : ℕ) (v : V) :
    iter (step a b) n v = ofVec ((M a b) ^ n *ᵥ toVec v) := by
  induction n generalizing v with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      obtain ⟨x, y⟩ := v
      rfl
  | succ n ih =>
      show step a b (iter (step a b) n v) = ofVec ((M a b) ^ (Nat.succ n) *ᵥ toVec v)
      rw [ih, step_eq_mulVec, toVec_ofVec, Matrix.mulVec_mulVec, pow_succ']

/-- The fifth power of `M a b`, entrywise. -/
theorem M_five_apply (a b : ℤ) (i j : Fin 2) :
    ((M a b) ^ 5) i j
      = c5 a b * (M a b) i j - d5 a b * (if i = j then (1 : ℤ) else 0) := by
  rw [show (M a b) ^ 5 = M a b * M a b * M a b * M a b * M a b by
    simp [pow_succ, pow_zero, mul_assoc]]
  fin_cases i <;> fin_cases j <;>
    simp [M, c5, d5, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact period five forces the fifth power of the matrix to be the identity. -/
theorem pow_five_eq_one (a b : ℤ) (h : ∀ v : V, iter (step a b) 5 v = v) :
    (M a b) ^ 5 = 1 := by
  have hcol : ∀ x y : ℤ, (M a b) ^ 5 *ᵥ ![x, y] = ![x, y] := by
    intro x y
    have h1 : iter (step a b) 5 (x, y) = (x, y) := h (x, y)
    have h2 := iter_eq_pow a b 5 (x, y)
    rw [h1] at h2
    have h3 : toVec (x, y) = (M a b) ^ 5 *ᵥ toVec (x, y) := by
      nth_rewrite 1 [h2]
      rw [toVec_ofVec]
    simpa [toVec] using h3.symm
  ext i j
  fin_cases i <;> fin_cases j
  · have hh := congrFun (hcol 1 0) 0
    rw [mulVec_two] at hh
    simpa using hh
  · have hh := congrFun (hcol 0 1) 0
    rw [mulVec_two] at hh
    simpa using hh
  · have hh := congrFun (hcol 1 0) 1
    rw [mulVec_two] at hh
    simpa using hh
  · have hh := congrFun (hcol 0 1) 1
    rw [mulVec_two] at hh
    simpa using hh

/-! ## T1: exact order five forces the golden trace -/

theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  have hM5 : (M (a : ℤ) (b : ℤ)) ^ 5 = 1 := pow_five_eq_one (a : ℤ) (b : ℤ) h.1
  -- three entries of `M⁵ = c • M - d • 1`
  have keyB : c5 (a : ℤ) (b : ℤ) * (b : ℤ) = 0 := by
    have hh := M_five_apply (a : ℤ) (b : ℤ) 1 0
    rw [hM5] at hh
    simpa [M, Matrix.one_apply] using hh.symm
  have keyC : c5 (a : ℤ) (b : ℤ) * (a : ℤ) = 0 := by
    have hh := M_five_apply (a : ℤ) (b : ℤ) 0 1
    rw [hM5] at hh
    simpa [M, Matrix.one_apply] using hh.symm
  have keyD : (1 : ℤ) = -c5 (a : ℤ) (b : ℤ) - d5 (a : ℤ) (b : ℤ) := by
    have hh := M_five_apply (a : ℤ) (b : ℤ) 1 1
    rw [hM5] at hh
    simpa [M, Matrix.one_apply] using hh
  by_cases hz : a = 0 ∧ b = 0
  · obtain ⟨ha0, hb0⟩ := hz
    obtain ⟨x, hx⟩ := h.2 2 (by norm_num) (by norm_num)
    obtain ⟨p, q⟩ := x
    have hcon : iter (step (a : ℤ) (b : ℤ)) 2 (p, q) = (p, q) := by
      have ha' : (a : ℤ) = 0 := by simp [ha0]
      have hb' : (b : ℤ) = 0 := by simp [hb0]
      rw [ha', hb']
      simp [iter, step_eq_mulVec, M, ofVec, toVec]
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
