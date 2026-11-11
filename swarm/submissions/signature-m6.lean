import Targets
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Signature of the rank-two Tits form above the affine boundary

For `4 < a*b` the Tits form `2b x² - 2ab xy + 2a y²` is indefinite. We compute its
signature from Mathlib's inertia law
`QuadraticForm.sigPos_add_sigNeg_add_radical`:

* `sigPos ≥ 1`, because the form is positive on `(1, 0)` (`= 2b > 0`), so the line it spans
  is a positive-definite subspace (`le_sigPos_of_posDef`);
* `sigNeg ≥ 1`, because the form is negative on `(a, 2)` (`= 2a(4-ab) < 0`), so the line it
  spans is negative-definite (`le_sigNeg_of_negDef`);
* `sigPos + sigNeg + finrank radical = 2` over `ℝ²`.

Two positive integers whose sum is at most two are both one, which gives `(1, 1)` and, in
passing, that the radical is trivial.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

open QuadraticMap

/-- A form that is positive at a nonzero vector is positive definite on the line that vector
spans: on that line `Q (c • v) = c * c * Q v`, and `c = 0` would make the vector zero. -/
lemma posDef_restrict_span_singleton {Q : QuadraticForm ℝ (Fin 2 → ℝ)} {v : Fin 2 → ℝ}
    (hQv : 0 < Q v) :
    (Q.restrict (Submodule.span ℝ {v})).PosDef := by
  intro x hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.2
  have hx' : (x : Fin 2 → ℝ) = c • v := hc.symm
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hx (Subtype.ext (by rw [hx', zero_smul]; rfl))
  rw [QuadraticMap.restrict_apply, hx', QuadraticMap.map_smul, smul_eq_mul]
  exact mul_pos (mul_self_pos.mpr hc0) hQv

/-- The vector `(1, 0)` in `Fin 2 → ℝ`. -/
private def e₀ : Fin 2 → ℝ := ![1, 0]

@[simp] private lemma e₀_zero : e₀ 0 = 1 := rfl
@[simp] private lemma e₀_one : e₀ 1 = 0 := rfl

private lemma e₀_ne_zero : e₀ ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [e₀] at h0

/-- The sign computation at `(1, 0)`: the form is `2b` there. -/
lemma titsForm_one_zero (a b : ℕ) : titsForm (a : ℤ) (b : ℤ) 1 0 = 2 * (b : ℝ) := by
  simp [titsForm]

/-- The sign computation at `(a, 2)`: the form is `2a(4 - ab)` there. -/
lemma titsForm_a_two (a b : ℕ) :
    titsForm (a : ℤ) (b : ℤ) ((a : ℕ) : ℝ) 2 =
      2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) := by
  simp only [titsForm]
  push_cast
  ring

/-- Above the affine boundary the Tits form has signature `(1, 1)`. -/
theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have habR : (4 : ℝ) < (a : ℝ) * (b : ℝ) := by
    have h4 : ((4 : ℕ) : ℝ) < ((a * b : ℕ) : ℝ) := by exact_mod_cast hab
    simpa using h4
  -- the form is positive at `(1, 0)`
  have hpos : 0 < titsQF (a : ℤ) (b : ℤ) e₀ := by
    rw [titsQF_apply, e₀_zero, e₀_one, titsForm_one_zero]
    linarith
  -- the form is negative at `(a, 2)`
  have hnegv : (titsQF (a : ℤ) (b : ℤ)) ![((a : ℝ)), 2] < 0 := by
    rw [titsQF_apply]
    have h0 : (![((a : ℝ)), 2] : Fin 2 → ℝ) 0 = (a : ℝ) := rfl
    have h1 : (![((a : ℝ)), 2] : Fin 2 → ℝ) 1 = 2 := rfl
    rw [h0, h1, titsForm_a_two]
    have h4 : 4 - (a : ℝ) * (b : ℝ) < 0 := sub_neg.mpr habR
    nlinarith [haR, h4]
  have hne₂ : (![((a : ℝ)), 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
    linarith
  -- lower bounds on the two indices
  have hsP : 1 ≤ sigPos (titsQF (a : ℤ) (b : ℤ)) := by
    have hV : Module.finrank ℝ ↥(Submodule.span ℝ ({e₀} : Set (Fin 2 → ℝ))) = 1 :=
      finrank_span_singleton e₀_ne_zero
    have := le_sigPos_of_posDef (titsQF (a : ℤ) (b : ℤ))
      (posDef_restrict_span_singleton hpos)
    omega
  have hsN : 1 ≤ sigNeg (titsQF (a : ℤ) (b : ℤ)) := by
    have hV : Module.finrank ℝ
        ↥(Submodule.span ℝ ({![((a : ℝ)), 2]} : Set (Fin 2 → ℝ))) = 1 :=
      finrank_span_singleton hne₂
    have hP : ((-(titsQF (a : ℤ) (b : ℤ))).restrict
        (Submodule.span ℝ ({![((a : ℝ)), 2]} : Set (Fin 2 → ℝ)))).PosDef := by
      refine posDef_restrict_span_singleton ?_
      simpa using hnegv
    have := le_sigNeg_of_negDef (titsQF (a : ℤ) (b : ℤ)) hP
    omega
  -- the inertia identity
  have hid := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := titsQF (a : ℤ) (b : ℤ))
  rw [Module.finrank_fin_fun] at hid
  constructor
  · omega
  · omega

end OperatorFirst.CoxeterRankTwo
