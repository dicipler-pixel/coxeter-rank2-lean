import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- The characteristic-polynomial identity for the rank-two step, written without
matrices: the trace is `a*b - 2` and the determinant is one. -/
lemma step_sq_char (a b : ℤ) (v : V) :
    step a b (step a b v) = (a * b - 2) • step a b v - v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

lemma step_add (a b : ℤ) (u v : V) :
    step a b (u + v) = step a b u + step a b v := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  ext <;> simp [step, s1, s2] <;> ring

lemma step_smul (a b : ℤ) (c : ℤ) (v : V) :
    step a b (c • v) = c • step a b v := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

lemma step_sub (a b : ℤ) (u v : V) :
    step a b (u - v) = step a b u - step a b v := by
  rcases u with ⟨x, y⟩
  rcases v with ⟨z, w⟩
  ext <;> simp [step, s1, s2] <;> ring

/-- For every `a, b ≥ 1` with `a*b ≤ 3`, the Coxeter element has the exact period the
finite type prescribes: `3` for `A₂`, `4` for `B₂`, `6` for `G₂`. -/
theorem finite_exact_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    (a * b = 1 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 3) ∧
      (a * b = 2 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 4) ∧
        (a * b = 3 → HasExactPeriod (step (a : ℤ) (b : ℤ)) 6) := by
  have ha3 : a ≤ 3 := by
    calc
      a = a * 1 := by simp
      _ ≤ a * b := by gcongr
      _ ≤ 3 := hab
  have hb3 : b ≤ 3 := by
    calc
      b = 1 * b := by simp
      _ ≤ a * b := by gcongr
      _ ≤ 3 := hab
  interval_cases a <;> interval_cases b <;> norm_num at *
  all_goals
    constructor
    · rintro ⟨x, y⟩
      ext <;> simp [iter, step, s1, s2] <;> ring
    · intro m hm hlt
      refine ⟨(1, 0), ?_⟩
      interval_cases m <;> norm_num [iter, step, s1, s2] at *

/-- Every rank-two representative with `a*b = 4` is unipotent: `(T - 1)² = 0`. -/
theorem affine_unipotent (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) (v : V) :
    step (a : ℤ) (b : ℤ) (step (a : ℤ) (b : ℤ) v) = 2 • step (a : ℤ) (b : ℤ) v - v := by
  have hab' : (a : ℤ) * (b : ℤ) = 4 := by exact_mod_cast hab
  simpa [hab'] using step_sq_char (a : ℤ) (b : ℤ) v

/-- Unipotence turned into the iterate: `Tⁿ v = v + n(T v - v)`, linear drift. -/
theorem affine_iterate (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (v : V) :
    iter (step (a : ℤ) (b : ℤ)) n v = v + (n : ℤ) • (step (a : ℤ) (b : ℤ) v - v) := by
  have hd : step (a : ℤ) (b : ℤ) (step (a : ℤ) (b : ℤ) v - v) =
      step (a : ℤ) (b : ℤ) v - v := by
    rw [step_sub, affine_unipotent a b ha hb hab]
    module
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      change step (a : ℤ) (b : ℤ) (iter (step (a : ℤ) (b : ℤ)) n v) = _
      rw [ih, step_add, step_smul, hd]
      push_cast
      module

/-- Hence no positive power of an affine representative is the identity. -/
theorem affine_no_positive_period (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (n : ℕ) (hn : 0 < n) : iter (step (a : ℤ) (b : ℤ)) n (1, 0) ≠ (1, 0) := by
  rw [affine_iterate a b ha hb hab]
  intro h
  have h1 := congrArg Prod.fst h
  have hab' : (a : ℤ) * (b : ℤ) = 4 := by exact_mod_cast hab
  have hn' : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  norm_num [step, s1, s2, hab'] at h1
  omega

/-- Finite side: the Tits form is positive definite. -/
theorem tits_positive_definite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3)
    (x y : ℝ) (h : (x, y) ≠ 0) : 0 < titsForm (a : ℤ) (b : ℤ) x y := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR0 : (0 : ℝ) < (a : ℝ) * (b : ℝ) := mul_pos haR hbR
  have habR3 : (a : ℝ) * (b : ℝ) ≤ 3 := by exact_mod_cast hab
  have hgap : (0 : ℝ) < 4 - (a : ℝ) * (b : ℝ) := by linarith
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hn
    push_neg at hn
    rcases hn with ⟨rfl, rfl⟩
    exact h rfl
  have key_y : 2 * (b : ℝ) * titsForm (a : ℤ) (b : ℤ) x y =
      (2 * (b : ℝ) * x - (a : ℝ) * (b : ℝ) * y) ^ 2 +
        (a : ℝ) * (b : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * y ^ 2 := by
    simp only [titsForm]
    push_cast
    ring
  have key_x : 2 * (a : ℝ) * titsForm (a : ℤ) (b : ℤ) x y =
      (2 * (a : ℝ) * y - (a : ℝ) * (b : ℝ) * x) ^ 2 +
        (a : ℝ) * (b : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * x ^ 2 := by
    simp only [titsForm]
    push_cast
    ring
  rcases hxy with hx | hy
  · have htail : 0 < (a : ℝ) * (b : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * x ^ 2 := by
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      positivity
    have hl : 0 < 2 * (a : ℝ) * titsForm (a : ℤ) (b : ℤ) x y := by
      rw [key_x]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) htail
    nlinarith
  · have htail : 0 < (a : ℝ) * (b : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * y ^ 2 := by
      have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      positivity
    have hl : 0 < 2 * (b : ℝ) * titsForm (a : ℤ) (b : ℤ) x y := by
      rw [key_y]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) htail
    nlinarith

theorem zero_partner_iterate (a : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step a 0) (2 * n) (x, y) = (x + 2 * (n : ℤ) * a * y, y) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      change step a 0 (step a 0 (iter (step a 0) (2 * n) (x, y))) = _
      rw [ih]
      simp only [Nat.cast_succ]
      ext <;> simp [step, s1, s2] <;> ring

theorem zero_product_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n) (x, y) = (x, y - 2 * (n : ℤ) * b * x) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      change step 0 b (step 0 b (iter (step 0 b) (2 * n) (x, y))) = _
      rw [ih]
      simp only [Nat.cast_succ]
      ext <;> simp [step, s1, s2] <;> ring

theorem zero_product_odd_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n + 1) (x, y) =
      (-x, (2 * (n : ℤ) + 1) * b * x - y) := by
  change step 0 b (iter (step 0 b) (2 * n) (x, y)) = _
  rw [zero_product_iterate]
  ext <;> simp [step, s1, s2] <;> ring

theorem zero_partner_odd_iterate (a : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step a 0) (2 * n + 1) (x, y) =
      (-x - (2 * (n : ℤ) + 1) * a * y, -y) := by
  change step a 0 (iter (step a 0) (2 * n) (x, y)) = _
  rw [zero_partner_iterate]
  ext <;> simp [step, s1, s2] <;> ring

theorem zero_product_no_positive_period (b : ℤ) (hb : b ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step 0 b) n (1, 0) ≠ (1, 0) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    rw [show k + k = 2 * k by omega, zero_product_iterate]
    intro h
    have h2 := congrArg Prod.snd h
    simp only [Prod.snd] at h2
    have hk' : (k : ℤ) ≠ 0 := by
      exact_mod_cast (show k ≠ 0 by omega)
    apply hk'
    have hmul : 2 * ((k : ℤ) * b) = 0 := by linear_combination -h2
    have : (k : ℤ) * b = 0 := (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    exact (mul_eq_zero.mp this).resolve_right hb
  · subst n
    rw [zero_product_odd_iterate]
    norm_num

theorem zero_partner_no_positive_period (a : ℤ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step a 0) n (0, 1) ≠ (0, 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst n
    rw [show k + k = 2 * k by omega, zero_partner_iterate]
    intro h
    have h1 := congrArg Prod.fst h
    simp only [Prod.fst] at h1
    have hk' : (k : ℤ) ≠ 0 := by
      exact_mod_cast (show k ≠ 0 by omega)
    apply hk'
    have hmul : 2 * ((k : ℤ) * a) = 0 := by linear_combination h1
    have : (k : ℤ) * a = 0 := (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    exact (mul_eq_zero.mp this).resolve_right ha
  · subst n
    rw [zero_partner_odd_iterate]
    norm_num

end OperatorFirst.CoxeterRankTwo
