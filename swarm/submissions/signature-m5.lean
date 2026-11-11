import Targets

/-!
# The rank-two Tits form has signature `(1,1)` above the affine boundary

For `a, b ≥ 1` with `4 < a * b`, the symmetrised Tits form
`titsForm a b x y = 2b x² - 2(ab) xy + 2a y²` is indefinite of rank two, hence its signature is
`(1,1)`. We prove this by an explicit Sylvester reduction: completing the square,

`titsForm a b x y = 2b * (x - (a/2) y)² + (a (4 - ab) / 2) * y²`,

so `titsQF a b` is isometric, via the shear `(x, y) ↦ (x - (a/2) y, y)`, to the weighted sum of
squares with weights `2b > 0` and `a (4 - ab)/2 < 0`. Sylvester's law of inertia
(`QuadraticForm.sigPos_of_equiv_weightedSumSquares` and its `sigNeg` twin) then counts one positive
and one negative weight.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

open QuadraticMap

/-- The shear `(x, y) ↦ (x - c y, y)` of the plane, as a linear equivalence. -/
noncomputable def shear (c : ℝ) : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0 - c * v 1, v 1]
  invFun v := ![v 0 + c * v 1, v 1]
  left_inv v := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  map_add' v w := by
    ext i
    fin_cases i
    · simp; ring
    · simp
  map_smul' r v := by
    ext i
    fin_cases i
    · simp; ring
    · simp

@[simp] lemma shear_apply (c : ℝ) (v : Fin 2 → ℝ) :
    shear c v = ![v 0 - c * v 1, v 1] := rfl

/-- The two weights of the completed-square form: `2b` and `a (4 - ab)/2`. -/
noncomputable def titsW (a b : ℤ) : Fin 2 → ℝ :=
  ![2 * (b : ℝ), (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) / 2]

lemma titsW_zero (a b : ℤ) : titsW a b 0 = 2 * (b : ℝ) := by
  simp [titsW]

lemma titsW_one (a b : ℤ) : titsW a b 1 = (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) / 2 := by
  simp [titsW]

/-- Completing the square: after the shear `x ↦ x - (a/2) y` the Tits form is the weighted sum of
squares with weights `2b` and `a (4 - ab)/2`. -/
lemma weightedSumSquares_shear_titsW (a b : ℤ) (v : Fin 2 → ℝ) :
    weightedSumSquares ℝ (titsW a b) (shear ((a : ℝ) / 2) v) = titsQF a b v := by
  simp only [shear_apply, titsQF_apply, titsForm, weightedSumSquares_apply, titsW_zero, titsW_one,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, smul_eq_mul]
  push_cast
  ring

/-- `titsQF a b` is isometric to the diagonal form with weights `2b`, `a (4 - ab)/2`. -/
lemma equivalent_weightedSumSquares_titsW (a b : ℤ) :
    QuadraticMap.Equivalent (titsQF a b) (weightedSumSquares ℝ (titsW a b)) :=
  ⟨{ toLinearEquiv := shear ((a : ℝ) / 2)
     map_app' := fun v => weightedSumSquares_shear_titsW a b v }⟩

/-- The signature of the rank-two Tits form when `a, b > 0` and `4 < a * b`. -/
theorem tits_signature_of (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hab : 4 < a * b) :
    sigPos (titsQF a b) = 1 ∧ sigNeg (titsQF a b) = 1 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR : (4 : ℝ) < (a : ℝ) * (b : ℝ) := by
    have h : ((4 : ℤ) : ℝ) < ((a * b : ℤ) : ℝ) := by exact_mod_cast hab
    push_cast at h
    linarith
  have hw0 : 0 < titsW a b 0 := by
    rw [titsW_zero]
    linarith
  have hw1 : titsW a b 1 < 0 := by
    rw [titsW_one]
    nlinarith
  have hP : {i : Fin 2 | 0 < titsW a b i} = {0} := by
    ext i
    fin_cases i <;> simp [hw0, le_of_lt hw1]
  have hN : {i : Fin 2 | titsW a b i < 0} = {1} := by
    ext i
    fin_cases i <;> simp [hw1, le_of_lt hw0]
  constructor
  · rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares
      (equivalent_weightedSumSquares_titsW a b), hP]
    simp
  · rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares
      (equivalent_weightedSumSquares_titsW a b), hN]
    simp

theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
  have hb' : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  have hab' : (4 : ℤ) < (a : ℤ) * (b : ℤ) := by exact_mod_cast hab
  exact tits_signature_of (a : ℤ) (b : ℤ) ha' hb' hab'

end OperatorFirst.CoxeterRankTwo
