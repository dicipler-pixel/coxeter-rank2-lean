import Targets

/-!
# Signature of the rank-two Tits form above the affine boundary

For `1 ≤ a, b` and `4 < a*b` the Tits form `2b x² - 2ab xy + 2a y²` is indefinite, and being a
binary form with a positive value at `(1, 0)` and a negative value at `(a, 2)`, its signature is
`(1, 1)`: one positive and one negative dimension.

The proof bounds `sigPos` from below by exhibiting a positive-definite line and from above by
exhibiting a line on which the form is nonpositive (`sigPos_add_finrank_le_of_nonpos`), and mirrors
the argument for `sigNeg` with the signs of the two witnesses exchanged.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-! ## Values of the Tits form at the two witness vectors -/

/-- The form at `(1, 0)`. -/
lemma titsForm_one_zero (a b : ℤ) : titsForm a b 1 0 = 2 * (b : ℝ) := by
  simp only [titsForm]
  push_cast
  ring

/-- The form at `(a, 2)`: `2a(4 - ab)`. -/
lemma titsForm_a_two (a b : ℤ) :
    titsForm a b (a : ℝ) 2 = 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) := by
  simp only [titsForm]
  push_cast
  ring

/-! ## Evaluation on a line -/

section Lines

variable {Q : QuadraticForm ℝ (Fin 2 → ℝ)} {v : Fin 2 → ℝ} {t : ℝ}

/-- If a nonzero vector is a positive-definite direction, the line it spans is positive definite
for the restricted form. -/
lemma posDef_restrict_span (hQv : Q v = t) (ht : 0 < t) :
    (Q.restrict (Submodule.span ℝ {v})).PosDef := by
  intro x hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
  have hval : (Q.restrict (Submodule.span ℝ {v})) x = c * c * t := by
    rw [QuadraticMap.restrict_apply, hc.symm, QuadraticMap.map_smul, hQv, smul_eq_mul]
  rw [hval]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (Subtype.ext (by rw [← hc]; simp))
  exact mul_pos (mul_self_pos.mpr hc0) ht

/-- If a nonzero vector is a negative-definite direction for `Q`, the line it spans is positive
definite for `-Q` (i.e. negative definite for `Q`). -/
lemma negDef_restrict_span (hQv : Q v = t) (ht : t < 0) :
    ((-Q).restrict (Submodule.span ℝ {v})).PosDef := by
  have hQ' : (-Q) v = -t := by rw [neg_apply, hQv]
  have ht' : (0 : ℝ) < -t := by linarith
  exact posDef_restrict_span (Q := -Q) (t := -t) hQ' ht'

/-- If the form is nonpositive at a spanning vector, it is nonpositive on the whole line. -/
lemma le_zero_on_span (hQv : Q v = t) (ht : t ≤ 0) :
    ∀ x ∈ Submodule.span ℝ {v}, Q x ≤ 0 := by
  intro x hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  rw [← hc, QuadraticMap.map_smul, hQv, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg c) ht

end Lines

/-! ## The signature -/

/-- The integer-indexed form of the target: above the affine boundary the rank-two Tits form has
signature `(1, 1)`. -/
lemma titsQF_sig_of_four_lt (A B : ℤ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : 4 < A * B) :
    sigPos (titsQF A B) = 1 ∧ sigNeg (titsQF A B) = 1 := by
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hBR : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hABR : (4 : ℝ) < (A : ℝ) * (B : ℝ) := by exact_mod_cast hAB
  have hApos : (0 : ℝ) < (A : ℝ) := by linarith
  -- the two witnesses
  set v1 : Fin 2 → ℝ := ![1, 0] with hv1
  set v2 : Fin 2 → ℝ := ![(A : ℝ), 2] with hv2
  have hv1ne : v1 ≠ 0 := by
    rw [hv1]
    intro h
    have h0 := congrFun h 0
    simp at h0
  have hv2ne : v2 ≠ 0 := by
    rw [hv2]
    intro h
    have h1 := congrFun h 1
    simp at h1
  have hQ1 : titsQF A B v1 = 2 * (B : ℝ) := by
    rw [hv1]
    simp [titsQF_apply, titsForm_one_zero]
  have hQ2 : titsQF A B v2 = 2 * (A : ℝ) * (4 - (A : ℝ) * (B : ℝ)) := by
    rw [hv2]
    simp [titsQF_apply, titsForm_a_two]
  have h1pos : (0 : ℝ) < 2 * (B : ℝ) := by linarith
  have h2neg : 2 * (A : ℝ) * (4 - (A : ℝ) * (B : ℝ)) < 0 := by nlinarith
  have hdim1 : Module.finrank ℝ (Submodule.span ℝ {v1}) = 1 := finrank_span_singleton hv1ne
  have hdim2 : Module.finrank ℝ (Submodule.span ℝ {v2}) = 1 := finrank_span_singleton hv2ne
  have hfin : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  constructor
  · refine le_antisymm ?_ ?_
    · have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := titsQF A B)
          (V := Submodule.span ℝ {v2}) (le_zero_on_span hQ2 h2neg.le)
      rw [hdim2, hfin] at h
      omega
    · have h := le_sigPos_of_posDef (titsQF A B) (posDef_restrict_span hQ1 h1pos)
      rw [hdim1] at h
      exact h
  · change sigPos (-(titsQF A B)) = 1
    refine le_antisymm ?_ ?_
    · have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -(titsQF A B))
          (V := Submodule.span ℝ {v1})
          (le_zero_on_span (Q := -(titsQF A B)) (by rw [neg_apply, hQ1])
            (by linarith : -(2 * (B : ℝ)) ≤ 0))
      rw [hdim1, hfin] at h
      omega
    · have h := le_sigNeg_of_negDef (titsQF A B) (negDef_restrict_span hQ2 h2neg)
      rw [hdim2] at h
      exact h

/-- Above the affine boundary (`4 < a*b`) the rank-two Tits form has signature `(1, 1)`:
one positive and one negative dimension. -/
theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  exact titsQF_sig_of_four_lt (a : ℤ) (b : ℤ) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hab)

end OperatorFirst.CoxeterRankTwo
