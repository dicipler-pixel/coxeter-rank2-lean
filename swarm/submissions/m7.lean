import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- With `a = 0`, the even iterates are integral shears. -/
theorem zero_product_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n) (x, y) = (x, y - 2 * (n : ℤ) * b * x) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [iter]
      rw [ih]
      ext <;> simp [step, s1, s2] <;> ring

/-- So for `b ≠ 0` no positive power is the identity, although `a*b = 0 < 4`. -/
theorem zero_product_no_positive_period (b : ℤ) (hb : b ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step 0 b) n (1, 0) ≠ (1, 0) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
    refine ⟨n / 2, ?_⟩
    omega
  rcases hk with rfl | rfl
  · rw [zero_product_iterate]
    intro h
    have hs := congrArg Prod.snd h
    simp at hs
    have hkpos : 0 < k := by omega
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    rcases hs with hkz | hbz
    · exact hk0 (by exact_mod_cast hkz)
    · exact hb hbz
  · simp only [iter]
    rw [zero_product_iterate]
    intro h
    have hf := congrArg Prod.fst h
    norm_num [step, s1, s2] at hf

/-- The even iterates in the mirror case are also integral shears. -/
theorem zero_partner_iterate (a : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step a 0) (2 * n) (x, y) = (x + 2 * (n : ℤ) * a * y, y) := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp only [iter]
      rw [ih]
      ext <;> simp [step, s1, s2] <;> ring

/-- The mirror case `b = 0`, `a ≠ 0`, on the witness `(0, 1)`. -/
theorem zero_partner_no_positive_period (a : ℤ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    iter (step a 0) n (0, 1) ≠ (0, 1) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k ∨ n = 2 * k + 1 := by
    refine ⟨n / 2, ?_⟩
    omega
  rcases hk with rfl | rfl
  · rw [zero_partner_iterate]
    intro h
    have hf := congrArg Prod.fst h
    simp at hf
    have hkpos : 0 < k := by omega
    have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    rcases hf with hkz | haz
    · exact hk0 (by exact_mod_cast hkz)
    · exact ha haz
  · simp only [iter]
    rw [zero_partner_iterate]
    intro h
    have hs := congrArg Prod.snd h
    norm_num [step, s1, s2] at hs

/-- Finite side: the Tits form is positive definite. -/
theorem tits_positive_definite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3)
    (x y : ℝ) (h : (x, y) ≠ 0) : 0 < titsForm (a : ℤ) (b : ℤ) x y := by
  have ha3 : a ≤ 3 := (Nat.le_mul_of_pos_right a (show 0 < b by omega)).trans hab
  have hb3 : b ≤ 3 := (Nat.le_mul_of_pos_left b (show 0 < a by omega)).trans hab
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h (Prod.ext hn.1 hn.2)
  have hs : 0 < x ^ 2 + y ^ 2 := by
    rcases hxy with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg x]
  interval_cases a <;> interval_cases b <;>
    norm_num [titsForm] at * <;> nlinarith [sq_nonneg (x - y)]

end OperatorFirst.CoxeterRankTwo
