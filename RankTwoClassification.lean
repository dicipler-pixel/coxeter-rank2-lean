import RankTwoTargets
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

/-- Affine side, semidefinite: at `a*b = 4` the symmetrised form is nonnegative everywhere, which
together with its vanishing at `(a, 2)` makes it degenerate there. -/
theorem tits_semidefinite_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (x y : ℝ) : 0 ≤ titsForm (a : ℤ) (b : ℤ) x y := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR : (a : ℝ) * (b : ℝ) = 4 := by
    have h : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
    push_cast at h
    linarith
  have hsq : 2 * (b : ℝ) * titsForm (a : ℤ) (b : ℤ) x y
      = (2 * (b : ℝ) * x - ((a : ℝ) * (b : ℝ)) * y) ^ 2
        + ((a : ℝ) * (b : ℝ)) * (4 - (a : ℝ) * (b : ℝ)) * y ^ 2 := by
    simp only [titsForm]; push_cast; ring
  have key : 2 * (b : ℝ) * titsForm (a : ℤ) (b : ℤ) x y
      = (2 * (b : ℝ) * x - 4 * y) ^ 2 := by
    rw [hsq, habR]; ring
  have h : 0 ≤ 2 * (b : ℝ) * titsForm (a : ℤ) (b : ℤ) x y := by
    rw [key]; positivity
  nlinarith

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

/-- The polar form restricts to `titsForm` on the diagonal. -/
@[simp] lemma titsBilin_self (a b : ℤ) (u : ℝ × ℝ) :
    titsBilin a b u u = titsForm a b u.1 u.2 := by
  simp only [titsBilin, titsForm]
  ring

/-- Affine side: at `a*b = 4` the vector `(a, 2)` is in the radical of the bilinear form. -/
theorem tits_radical_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4)
    (x y : ℝ) : titsBilin (a : ℤ) (b : ℤ) (a, 2) (x, y) = 0 := by
  have h : (a : ℝ) * (b : ℝ) = 4 := by
    have h4 : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
    push_cast at h4
    linarith
  simp only [titsBilin]
  push_cast
  linear_combination (-((a : ℝ) * y)) * h

/-- Affine side, the standard statement: at `a*b = 4` the bilinear form is degenerate — some
nonzero vector pairs to zero with every vector. -/
theorem tits_degenerate_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    ∃ v : ℝ × ℝ, v ≠ 0 ∧ ∀ w : ℝ × ℝ, titsBilin (a : ℤ) (b : ℤ) v w = 0 := by
  refine ⟨((a : ℝ), 2), ?_, ?_⟩
  · intro h
    have ha0 : (a : ℝ) = 0 := by simpa using congrArg Prod.fst h
    have haR : (0 : ℝ) < (a : ℝ) := by
      have : (0 : ℕ) < a := by omega
      exact_mod_cast this
    linarith
  · rintro ⟨x, y⟩
    exact tits_radical_at_four a b ha hb hab x y

/-- Indefinite side: above the boundary the form takes both signs, so it is indefinite. -/
theorem tits_indefinite_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    (∃ x y : ℝ, 0 < titsForm (a : ℤ) (b : ℤ) x y) ∧
      ∃ x y : ℝ, titsForm (a : ℤ) (b : ℤ) x y < 0 := by
  refine ⟨⟨1, 0, ?_⟩, ⟨(a : ℝ), 2, tits_negative_above_four a b ha hb hab⟩⟩
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  simp only [titsForm]
  push_cast
  nlinarith

/-- The witness `(a, 2)` is not the origin, which is what makes it usable as a test vector. -/
lemma pair_a_two_ne_zero (a : ℕ) (ha : 1 ≤ a) : (((a : ℝ)), (2 : ℝ)) ≠ (0, 0) := by
  intro h
  have ha0 : (a : ℝ) = 0 := by simpa using congrArg Prod.fst h
  have haR : (0 : ℝ) < (a : ℝ) := by
    have : (0 : ℕ) < a := by omega
    exact_mod_cast this
  linarith

/-- The converse of positive definiteness: if the form is positive off the origin then `a*b ≤ 3`.
Both excluded cases are already proved — at `a*b = 4` the witness `(a, 2)` is a zero, above it a
negative value. -/
lemma tits_posDef_imp_le_three (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ x y : ℝ, (x, y) ≠ 0 → 0 < titsForm (a : ℤ) (b : ℤ) x y) : a * b ≤ 3 := by
  by_contra hcon
  have h4 : 4 ≤ a * b := by omega
  rcases Nat.lt_or_eq_of_le h4 with hlt | heq
  · have hneg := tits_negative_above_four a b ha hb hlt
    have hpos := h (a : ℝ) 2 (pair_a_two_ne_zero a ha)
    linarith
  · have hzero := tits_vanishes_at_four a b ha hb heq.symm
    have hpos := h (a : ℝ) 2 (pair_a_two_ne_zero a ha)
    linarith

/-- The converse of semidefiniteness: if the form is nonnegative everywhere then `a*b ≤ 4`. -/
lemma tits_semidef_imp_le_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : ∀ x y : ℝ, 0 ≤ titsForm (a : ℤ) (b : ℤ) x y) : a * b ≤ 4 := by
  by_contra hcon
  have hlt : 4 < a * b := by omega
  have hneg := tits_negative_above_four a b ha hb hlt
  have hnn := h (a : ℝ) 2
  linarith

/-- The finite side is exactly positive definiteness: the form is positive off the origin if and
only if `a*b ≤ 3`. -/
theorem tits_posDef_iff_le_three (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∀ x y : ℝ, (x, y) ≠ 0 → 0 < titsForm (a : ℤ) (b : ℤ) x y) ↔ a * b ≤ 3 :=
  ⟨tits_posDef_imp_le_three a b ha hb, fun h x y hxy =>
    tits_positive_definite a b ha hb h x y hxy⟩

/-- The affine side is exactly nonnegativity: the form is nonnegative everywhere if and only if
`a*b ≤ 4`. -/
theorem tits_semidef_iff_le_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∀ x y : ℝ, 0 ≤ titsForm (a : ℤ) (b : ℤ) x y) ↔ a * b ≤ 4 := by
  refine ⟨tits_semidef_imp_le_four a b ha hb, ?_⟩
  intro h x y
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · have h3 : a * b ≤ 3 := by omega
    rcases eq_or_ne (x, y) (0, 0) with hzero | hne
    · have hx : x = 0 := by simpa using congrArg Prod.fst hzero
      have hy : y = 0 := by simpa using congrArg Prod.snd hzero
      subst hx; subst hy
      simp [titsForm]
    · exact le_of_lt (tits_positive_definite a b ha hb h3 x y hne)
  · exact tits_semidefinite_at_four a b ha hb heq x y

open scoped Classical in
theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  have hne : titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 < 0 := tits_negative_above_four a b ha hb hab
  set Q : QuadraticForm ℝ (Fin 2 → ℝ) := titsQF (a : ℤ) (b : ℤ) with hQdef
  set e : Fin 2 → ℝ := ![1, 0] with he
  set w : Fin 2 → ℝ := ![(a : ℝ), 2] with hw
  have hQe : Q e = 2 * (b : ℝ) := by
    rw [hQdef]; simp [he, titsQF_apply, titsForm]
  have hQw : Q w < 0 := by
    rw [hQdef]; simpa [hw, titsQF_apply] using hne
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have he_ne : e ≠ 0 := by
    intro h; have : e 0 = 0 := by rw [h]; simp
    simp [he] at this
  have hw_ne : w ≠ 0 := by
    intro h; have : w 0 = 0 := by rw [h]; simp
    simp [hw] at this; linarith
  -- the two lines
  have hfr_e : Module.finrank ℝ ↥(ℝ ∙ e) = 1 := finrank_span_singleton he_ne
  have hfr_w : Module.finrank ℝ ↥(ℝ ∙ w) = 1 := finrank_span_singleton hw_ne
  have hfr_top : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  -- Q ≤ 0 on the line through w
  have hnonpos_w : ∀ x ∈ (ℝ ∙ w : Submodule ℝ (Fin 2 → ℝ)), Q x ≤ 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [QuadraticMap.map_smul]
    have : (c * c) * Q w ≤ 0 := by nlinarith [mul_self_nonneg c]
    simpa [smul_eq_mul] using this
  -- -Q ≤ 0 on the line through e, i.e. Q ≥ 0 there
  have hnonpos_e : ∀ x ∈ (ℝ ∙ e : Submodule ℝ (Fin 2 → ℝ)), (-Q) x ≤ 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hc, QuadraticMap.map_smul]
    simp only [neg_apply, smul_eq_mul, hQe]
    nlinarith [mul_self_nonneg c, hbR]
  -- positive definiteness on the line through e
  have hposDef_e : (QuadraticMap.restrict Q (ℝ ∙ e)).PosDef := by
    intro x hx
    rw [QuadraticMap.restrict_apply]
    have hxmem : (x : Fin 2 → ℝ) ∈ (ℝ ∙ e : Submodule ℝ (Fin 2 → ℝ)) := x.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
    have hc0 : c ≠ 0 := by
      intro h0
      apply hx
      ext
      rw [← hc, h0, zero_smul]
      rfl
    rw [← hc, QuadraticMap.map_smul, hQe]
    simp only [smul_eq_mul]
    have hcc : 0 < c * c := mul_self_pos.mpr hc0
    nlinarith [hbR]
  -- positive definiteness of -Q on the line through w
  have hposDef_w : (QuadraticMap.restrict (-Q) (ℝ ∙ w)).PosDef := by
    intro x hx
    rw [QuadraticMap.restrict_apply]
    have hxmem : (x : Fin 2 → ℝ) ∈ (ℝ ∙ w : Submodule ℝ (Fin 2 → ℝ)) := x.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
    have hc0 : c ≠ 0 := by
      intro h0
      apply hx
      ext
      rw [← hc, h0, zero_smul]
      rfl
    rw [← hc, QuadraticMap.map_smul]
    simp only [QuadraticMap.neg_apply, smul_eq_mul]
    have hcc : 0 < c * c := mul_self_pos.mpr hc0
    nlinarith [hQw, hcc]
  have hpos_ub := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) hnonpos_w
  have hpos_lb := le_sigPos_of_posDef Q hposDef_e
  have hneg_ub := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) hnonpos_e
  have hneg_lb := le_sigNeg_of_negDef Q hposDef_w
  rw [hfr_e] at hpos_lb
  rw [hfr_w] at hpos_ub
  rw [hfr_w] at hneg_lb
  rw [hfr_e] at hneg_ub
  rw [hfr_top] at hpos_ub hneg_ub
  simp only [sigNeg] at hneg_lb hneg_ub ⊢
  constructor <;> omega

private lemma pair_ne_zero_of_ne_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) : (v 0, v 1) ≠ 0 := by
  intro h
  apply hv
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa using congrArg Prod.fst h
  · intro j
    refine Fin.cases ?_ ?_ j
    · simpa using congrArg Prod.snd h
    · intro k
      exact absurd k.isLt (by omega)

private lemma posDef_on_top_iff (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    (QuadraticMap.restrict (titsQF (a : ℤ) (b : ℤ)) ⊤).PosDef := by
  intro v hv
  rw [QuadraticMap.restrict_apply]
  have hv' : (v : Fin 2 → ℝ) ≠ 0 := fun h => hv (Subtype.ext h)
  have hpair : ((v : Fin 2 → ℝ) 0, (v : Fin 2 → ℝ) 1) ≠ 0 := pair_ne_zero_of_ne_zero hv'
  simpa [titsQF_apply] using tits_positive_definite a b ha hb hab _ _ hpair

theorem tits_signature_below_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 3) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 2 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 0 := by
  set Q : QuadraticForm ℝ (Fin 2 → ℝ) := titsQF (a : ℤ) (b : ℤ) with hQ
  have hfr : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have htop : Module.finrank ℝ ↥(⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2 := by
    rw [finrank_top]; exact hfr
  have hpd := posDef_on_top_iff a b ha hb hab
  have hlb := le_sigPos_of_posDef Q hpd
  rw [htop] at hlb
  have hub := sigPos_le_finrank Q
  rw [hfr] at hub
  have hQ0 : Q 0 = 0 := by rw [hQ]; simp [titsQF_apply, titsForm]
  have hgeom : ∀ v : Fin 2 → ℝ, 0 ≤ Q v := by
    intro v
    rcases eq_or_ne v 0 with h | h
    · rw [h, hQ0]
    · exact le_of_lt (hpd ⟨v, trivial⟩ (fun hv0 => h (congrArg Subtype.val hv0)))
  have hneg : ∀ x ∈ (⊤ : Submodule ℝ (Fin 2 → ℝ)), (-Q) x ≤ 0 := by
    intro x _
    rw [QuadraticMap.neg_apply]
    linarith [hgeom x]
  have hbnd := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) hneg
  rw [htop, hfr] at hbnd
  simp only [sigNeg]
  constructor <;> omega

theorem tits_signature_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 0 := by
  set Q : QuadraticForm ℝ (Fin 2 → ℝ) := titsQF (a : ℤ) (b : ℤ) with hQ
  have hfr : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have hsem : ∀ v : Fin 2 → ℝ, 0 ≤ Q v := by
    intro v
    rw [hQ]; simpa [titsQF_apply] using tits_semidefinite_at_four a b ha hb hab (v 0) (v 1)
  -- sigNeg = 0
  have hneg : ∀ x ∈ (⊤ : Submodule ℝ (Fin 2 → ℝ)), (-Q) x ≤ 0 := by
    intro x _
    rw [QuadraticMap.neg_apply]; linarith [hsem x]
  have hbnd := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) hneg
  have htop : Module.finrank ℝ ↥(⊤ : Submodule ℝ (Fin 2 → ℝ)) = 2 := by
    rw [finrank_top]; exact hfr
  rw [htop, hfr] at hbnd
  -- sigPos ≥ 1 from the line through (1,0)
  set e : Fin 2 → ℝ := ![1, 0] with he
  have he_ne : e ≠ 0 := by
    intro h
    have h0 : e 0 = 0 := by rw [h]; simp
    simp [he] at h0
  have hQe : Q e = 2 * (b : ℝ) := by rw [hQ]; simp [he, titsQF_apply, titsForm]
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hpd_e : (QuadraticMap.restrict Q (ℝ ∙ e)).PosDef := by
    intro x hx
    rw [QuadraticMap.restrict_apply]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (x : ↥(ℝ ∙ e)).2
    have hc0 : c ≠ 0 := by
      intro h0; apply hx; ext; rw [← hc, h0, zero_smul]; rfl
    rw [← hc, QuadraticMap.map_smul, hQe]
    simp only [smul_eq_mul]
    have : 0 < c * c := mul_self_pos.mpr hc0
    nlinarith
  have hlb := le_sigPos_of_posDef Q hpd_e
  rw [finrank_span_singleton he_ne] at hlb
  -- sigPos ≤ 1 from the line through (a,2), where the form vanishes
  set w : Fin 2 → ℝ := ![(a : ℝ), 2] with hw
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hw_ne : w ≠ 0 := by
    intro h
    have h0 : w 0 = 0 := by
      rw [h]
      simp
    rw [hw] at h0
    simp at h0
    linarith
  have hQw : Q w = 0 := by rw [hQ]; simpa [hw, titsQF_apply] using tits_vanishes_at_four a b ha hb hab
  have hnonpos_w : ∀ x ∈ (ℝ ∙ w : Submodule ℝ (Fin 2 → ℝ)), Q x ≤ 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hc, QuadraticMap.map_smul, hQw]
    simp
  have hub := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) hnonpos_w
  rw [finrank_span_singleton hw_ne, hfr] at hub
  simp only [sigNeg] at hbnd ⊢
  constructor <;> omega

/-- Affine side: the radical is exactly one-dimensional at the boundary, so with `sigPos = 1` and
`sigNeg = 0` the signature is `(1, 0)` in the strong sense. -/
theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := titsQF (a : ℤ) (b : ℤ))
  rw [Module.finrank_fin_fun ℝ] at h
  obtain ⟨hp, hn⟩ := tits_signature_at_four a b ha hb hab
  omega

/-- Shifting the argument by `(a, 2)` changes `titsForm` by `2a(4 - ab)(1 + y)`. -/
lemma titsForm_shift (a b : ℤ) (x y : ℝ) :
    titsForm a b ((a : ℝ) + x) (2 + y)
      = titsForm a b x y + 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * (1 + y) := by
  simp only [titsForm]
  push_cast
  ring

lemma titsQF_shift (a b : ℤ) (h : (a : ℝ) * (b : ℝ) = 4) (v : Fin 2 → ℝ) :
    titsQF a b (![(a : ℝ), 2] + v) = titsQF a b v := by
  rw [titsQF_apply, titsQF_apply]
  have h0 : (![(a : ℝ), 2] + v) 0 = (a : ℝ) + v 0 := by simp
  have h1 : (![(a : ℝ), 2] + v) 1 = 2 + v 1 := by simp
  rw [h0, h1, titsForm_shift, h]
  ring

lemma mem_radical_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    (![(a : ℝ), 2] : Fin 2 → ℝ) ∈ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) := by
  have hcast : (a : ℝ) * (b : ℝ) = 4 := by
    have h : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
    push_cast at h
    linarith
  rw [QuadraticMap.mem_radical_iff']
  refine ⟨?_, fun n => titsQF_shift _ _ hcast n⟩
  simpa using tits_vanishes_at_four a b ha hb hab

-- Route found by swarm member m1 (second campaign, direction d3): a shift identity for the form
-- rather than a coordinate expansion.
theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have hle : ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) ≤ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) :=
    Submodule.span_singleton_le_iff_mem _ _ |>.mpr (mem_radical_at_four a b ha hb hab)
  have hne : (![(a : ℝ), 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have h1 : Module.finrank ℝ ↥(ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ)) = 1 := finrank_span_singleton hne
  have h2 := tits_radical_finrank_at_four a b ha hb hab
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])).symm


theorem golden_product_eq_four_cos_sq :
    4 * Real.cos (Real.pi / 5) ^ 2 = (3 + Real.sqrt 5) / 2 := by
  rw [Real.cos_pi_div_five]
  have hs : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

end OperatorFirst.CoxeterRankTwo
