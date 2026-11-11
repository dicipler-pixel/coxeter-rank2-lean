import RankTwoCertificate

/-!
# Rank two: the finite/affine classification in the integral reflection model

The finite/affine boundary of rank-two Coxeter data, proved for **every** representative
`(a, b)` with `a, b ≥ 1`, in the integral reflection model of `RankTwoCertificate`:
`s₁(x, y) = (-x + a y, y)`, `s₂(x, y) = (x, b x - y)`, `step a b = s₁ ∘ s₂`, acting on `ℤ × ℤ`.

What is proved, and what it is about:

* `finite_exact_period` — for `1 ≤ a, b` with `a*b ≤ 3`, the step has exact period `3`
  (`a*b = 1`), `4` (`a*b = 2`) or `6` (`a*b = 3`). Since `a*b ≤ 3` leaves five pairs —
  `(1,1)`, `(1,2)`, `(2,1)`, `(1,3)`, `(3,1)` — this is a finite statement about those five,
  not a general theorem in `a` and `b`.
* `affine_unipotent`, `affine_iterate`, `affine_no_positive_period` — for `a*b = 4`, the step
  is unipotent and drifts linearly. These **are** general in `(a, b)`: they follow from the
  characteristic-polynomial identity `step² = (a b - 2) • step - 1`, not from a case split.
* `zero_product_iterate`, `zero_product_no_positive_period`,
  `zero_partner_no_positive_period` — with `a*b = 0` and a nonzero partner, the product has
  infinite order on an explicit vector, although `4 - a*b > 0`. So `4 - a*b > 0` alone does
  not make the product finite; the off-diagonal pair has to be nonzero.
* `tits_positive_definite`, `tits_vanishes_at_four`, `tits_negative_above_four` — the
  symmetrised Tits form of the Cartan matrix is positive definite for `a*b ≤ 3`, vanishes at
  `(a, 2)` for `a*b = 4`, and is negative at `(a, 2)` above. Semidefiniteness at `a*b = 4`
  and indefiniteness above are **not** formalized; see the note on `titsForm`.
* `golden_product_eq_four_cos_sq` — `4cos²(π/5) = (3+√5)/2`. The arithmetic only: that this
  number is the Cartan product of `I₂(5)`, and the `H₂` geometry, are not formalized.

This module does not prove the finite/affine classification for Coxeter groups in general,
and for rank ≥ 3 nothing is claimed. The dihedral isomorphism for rank two is in
`DihedralBridge.lean`; it does not transfer this reflection representation.

Attribution: `finite_exact_period`, `affine_unipotent`, `affine_iterate`,
`affine_no_positive_period`, `tits_positive_definite` and the charpoly/linearity lemmas were
proved by swarm member m1; the three `zero_*` statements and their parity lemmas by member
m2; `cartan_det`, `tits_vanishes_at_four`, `tits_negative_above_four` and
`golden_product_eq_four_cos_sq` by the coordinator. Member m6 independently proved
`finite_exact_period` by enumeration; that proof is kept under `swarm/` and is not included
here.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-! ## The objects -/

/-- The rank-two Cartan matrix with off-diagonal magnitudes `a`, `b`. It is a generalised
Cartan matrix in Kac's sense (`a_ij ≤ 0` for `i ≠ j`, and `a_ij = 0 ⟺ a_ji = 0`) only when
`a, b ≥ 0` and `a = 0 ⟺ b = 0`; the determinant identity below holds for all `a, b : ℤ`.

One convention to keep straight: the reflection pair of `RankTwoCertificate` (`s1 a`, `s2 b`)
satisfies `s_i(α_j) = α_j - a_{ji} α_i` for the matrix `cartan b a`, i.e. the transpose of the
matrix named here. Nothing below is affected — every statement depends on `a*b` alone, and
`titsForm a b x y = titsForm b a y x` — but the two writings should not be confused. -/
def cartan (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![2, -a; -b, 2]

/-- The symmetrised Tits form of `cartan a b`: the Gram matrix is `diag b 1 * A * diag 1 a`,
that is `2 b x² - 2 (a b) x y + 2 a y²`. For `1 ≤ a, b` what is proved here is that it is
positive definite when `a*b ≤ 3`, vanishes at `(a, 2)` when `a*b = 4`, and is negative at
`(a, 2)` when `4 < a*b`. At `a*b = 4` the vector `(a, 2)` is in fact in the radical of the
associated bilinear form, whose value is `B((a,2),(x,y)) = a y (4 - a b)`, and the form is
positive semidefinite there; neither of those two facts is formalized in this file. -/
def titsForm (a b : ℤ) (x y : ℝ) : ℝ :=
  2 * b * x ^ 2 - 2 * ((a * b : ℤ) : ℝ) * x * y + 2 * a * y ^ 2

/-! ## m1 — the charpoly identity, linearity, finite periods, affine side, Tits positivity -/


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

/-- Finite side: the Tits form is positive definite for `1 ≤ a, b` and `a*b ≤ 3`. -/
theorem tits_positive_definite (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3)
    (x y : ℝ) (h : (x, y) ≠ 0) : 0 < titsForm (a : ℤ) (b : ℤ) x y := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR0 : (0 : ℝ) < (a : ℝ) * (b : ℝ) := mul_pos haR hbR
  have habR3 : (a : ℝ) * (b : ℝ) ≤ 3 := by exact_mod_cast hab
  have hgap : (0 : ℝ) < 4 - (a : ℝ) * (b : ℝ) := by linarith
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hn
    push Not at hn
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

/-! ## m2 — the degenerate product `a*b = 0` -/


lemma zero_partner_iterate (a : ℤ) (n : ℕ) (x y : ℤ) :
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

lemma zero_product_odd_iterate (b : ℤ) (n : ℕ) (x y : ℤ) :
    iter (step 0 b) (2 * n + 1) (x, y) =
      (-x, (2 * (n : ℤ) + 1) * b * x - y) := by
  change step 0 b (iter (step 0 b) (2 * n) (x, y)) = _
  rw [zero_product_iterate]
  ext <;> simp [step, s1, s2] <;> ring

lemma zero_partner_odd_iterate (a : ℤ) (n : ℕ) (x y : ℤ) :
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

/-! ## coordinator — determinant, Tits sign at and above the boundary, the golden identity -/
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
