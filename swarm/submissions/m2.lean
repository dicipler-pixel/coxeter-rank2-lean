import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

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
