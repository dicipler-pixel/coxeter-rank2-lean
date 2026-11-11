import Targets

/-!
# Signature `(1, 1)` of the rank-two Tits form above the affine boundary

For `a, b ≥ 1` with `a * b > 4` the symmetrised Tits form
`titsForm a b x y = 2b x² - 2ab xy + 2a y²` has signature `(1, 1)`.

Route: *null directions* (isotropic vectors) plus the hyperbolic coordinate change.
Since `ab(ab-4) > 0` the real number `s = √(ab(ab-4))` exists, and the two vectors
`(ab + s, 2b)`, `(ab - s, 2b)` are isotropic for the form.  The invertible triangular
coordinate change `(p, q) ↦ (ab·p + s·q, 2b·p)` (a shear with inverse
`(x, y) ↦ (y/(2b), (x - ab·y/(2b))/s)`) diagonalises the form:

`Q(ab·p + s·q, 2b·p) = W·p² - W·q²`,  `W = 2ab²(4 - ab) < 0`.

So `titsQF a b` is isometric to `weightedSumSquares ℝ ![W, -W]`, whose two weights have
opposite signs; Sylvester's law of inertia (`sigPos_of_equiv_weightedSumSquares`,
`sigNeg_of_equiv_weightedSumSquares`) counts one positive and one negative weight.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

open QuadraticMap

/-- The hyperbolic coordinate change `(p, q) ↦ (ab·p + s·q, 2b·p)`, an invertible shear with
inverse `(x, y) ↦ (y/(2b), (x - ab·y/(2b))/s)`. -/
private noncomputable def titsShear (A B s : ℝ) (hB : B ≠ 0) (hs : s ≠ 0) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![A * B * v 0 + s * v 1, 2 * B * v 0]
  invFun w := ![w 1 / (2 * B), (w 0 - A * B * (w 1 / (2 * B))) / s]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring
  left_inv v := by
    ext i
    fin_cases i <;> simp <;> field_simp <;> ring
  right_inv w := by
    ext i
    fin_cases i <;> simp <;> field_simp <;> ring

theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hb
  have habR : (4 : ℝ) < (a : ℝ) * (b : ℝ) := by exact_mod_cast hab
  -- the discriminant of the form, viewed as a quadratic in the first coordinate
  have hdisc : 0 < (a : ℝ) * (b : ℝ) * ((a : ℝ) * (b : ℝ) - 4) := by nlinarith
  obtain ⟨s, hs2, hs⟩ : ∃ s : ℝ, s ^ 2 = (a : ℝ) * (b : ℝ) * ((a : ℝ) * (b : ℝ) - 4) ∧ 0 < s :=
    ⟨Real.sqrt _, Real.sq_sqrt hdisc.le, Real.sqrt_pos.2 hdisc⟩
  have hsne : s ≠ 0 := ne_of_gt hs
  have hBne : (b : ℝ) ≠ 0 := ne_of_gt hbR
  -- the two diagonal weights, of opposite sign
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = 2 * (a : ℝ) * (b : ℝ) ^ 2 * (4 - (a : ℝ) * (b : ℝ)) :=
    ⟨_, rfl⟩
  have hW : W < 0 := by
    rw [hWdef]
    have h1 : (0 : ℝ) < 2 * (a : ℝ) * (b : ℝ) ^ 2 := by positivity
    nlinarith
  -- diagonal form in hyperbolic coordinates
  have hdiag : ∀ p q : ℝ,
      titsForm (a : ℤ) (b : ℤ) ((a : ℝ) * (b : ℝ) * p + s * q) (2 * (b : ℝ) * p)
        = W * p ^ 2 - W * q ^ 2 := by
    intro p q
    simp only [titsForm]
    push_cast
    rw [hWdef]
    ring_nf
    rw [hs2]
    ring
  -- the isometry from `weightedSumSquares ℝ ![W, -W]` to the Tits form
  have hiso : ∀ v : Fin 2 → ℝ,
      titsQF (a : ℤ) (b : ℤ) (titsShear (a : ℝ) (b : ℝ) s hBne hsne v)
        = weightedSumSquares ℝ ![W, -W] v := by
    intro v
    rw [titsQF_apply, weightedSumSquares_apply, Fin.sum_univ_two]
    have h0 : titsShear (a : ℝ) (b : ℝ) s hBne hsne v 0
        = (a : ℝ) * (b : ℝ) * v 0 + s * v 1 := rfl
    have h1 : titsShear (a : ℝ) (b : ℝ) s hBne hsne v 1 = 2 * (b : ℝ) * v 0 := rfl
    rw [h0, h1, hdiag]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    ring
  have hisom : QuadraticMap.IsometryEquiv (weightedSumSquares ℝ ![W, -W])
      (titsQF (a : ℤ) (b : ℤ)) :=
    QuadraticMap.IsometryEquiv.mk (titsShear (a : ℝ) (b : ℝ) s hBne hsne) hiso
  have hEq : QuadraticMap.Equivalent (titsQF (a : ℤ) (b : ℤ))
      (weightedSumSquares ℝ ![W, -W]) :=
    ⟨hisom.symm⟩
  constructor
  · rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hEq]
    have hset : {i : Fin 2 | 0 < ![W, -W] i} = {1} := by
      ext i
      fin_cases i <;> simp [hW] <;> linarith
    rw [hset, Set.ncard_singleton]
  · rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hEq]
    have hset : {i : Fin 2 | ![W, -W] i < 0} = {0} := by
      ext i
      fin_cases i <;> simp [hW] <;> linarith
    rw [hset, Set.ncard_singleton]

end OperatorFirst.CoxeterRankTwo
