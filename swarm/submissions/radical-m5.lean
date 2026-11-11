import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- `titsForm a b` with natural-number parameters, in pure real notation. -/
lemma titsForm_natCast (a b : ℕ) (x y : ℝ) :
    titsForm (a : ℤ) (b : ℤ) x y
      = 2 * (b : ℝ) * x ^ 2 - 2 * ((a : ℝ) * (b : ℝ)) * x * y + 2 * (a : ℝ) * y ^ 2 := by
  simp only [titsForm]
  push_cast
  ring

/-- `titsBilin a b` with natural-number parameters, in pure real notation. -/
lemma titsBilin_natCast (a b : ℕ) (x y x' y' : ℝ) :
    titsBilin (a : ℤ) (b : ℤ) (x, y) (x', y')
      = 2 * (b : ℝ) * x * x' - ((a : ℝ) * (b : ℝ)) * (x * y' + y * x')
        + 2 * (a : ℝ) * y * y' := by
  simp only [titsBilin]
  push_cast
  ring

/-- The polar form of `titsQF a b` in coordinates is twice `titsBilin`. -/
lemma polarBilin_titsQF (a b : ℕ) (u v : Fin 2 → ℝ) :
    QuadraticMap.polarBilin (titsQF (a : ℤ) (b : ℤ)) u v
      = 2 * titsBilin (a : ℤ) (b : ℤ) (u 0, u 1) (v 0, v 1) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, titsQF_apply, titsForm,
    titsBilin, Pi.add_apply]
  push_cast
  ring

/-- The boundary condition, as a real equation. -/
lemma cast_mul_eq_four (a b : ℕ) (hab : a * b = 4) : (a : ℝ) * (b : ℝ) = 4 := by
  have h : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
  push_cast at h ⊢
  linarith

/-- `(a, 2)` is a zero of the form at `a*b = 4`. -/
lemma titsForm_pair (a b : ℕ) (hab : a * b = 4) :
    titsForm (a : ℤ) (b : ℤ) (a : ℝ) 2 = 0 := by
  have hab' := cast_mul_eq_four a b hab
  rw [titsForm_natCast]
  nlinarith [hab']

/-- The polar form vanishes on `((a, 2), ·)` at `a*b = 4`. -/
lemma titsBilin_pair (a b : ℕ) (hab : a * b = 4) (x' y' : ℝ) :
    titsBilin (a : ℤ) (b : ℤ) (a, 2) (x', y') = 0 := by
  have hab' := cast_mul_eq_four a b hab
  rw [titsBilin_natCast]
  linear_combination (-((a : ℝ) * y')) * hab'

/-- `(a, 2)` lies in the radical at `a*b = 4`. -/
lemma mem_radical_pair (a b : ℕ) (hab : a * b = 4) :
    (![(a : ℝ), 2] : Fin 2 → ℝ) ∈ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) := by
  refine ⟨?_, ?_⟩
  · rw [titsQF_apply]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      using titsForm_pair a b hab
  · refine LinearMap.ext fun w => ?_
    rw [polarBilin_titsQF]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.zero_apply]
    rw [titsBilin_pair a b hab (w 0) (w 1)]
    ring

/-- A radical vector is proportional to `(a, 2)`: pairing against `(1, 0)` gives
`2 * v 0 = a * v 1`. -/
lemma radical_le_span (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) ≤ ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have ha' : (a : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    linarith
  have hb' : (b : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    linarith
  intro v hv
  have hzero : ∀ w : Fin 2 → ℝ, QuadraticMap.polarBilin (titsQF (a : ℤ) (b : ℤ)) v w = 0 :=
    fun w => by simpa using DFunLike.congr_fun hv.2 w
  have h0 := hzero (![1, 0] : Fin 2 → ℝ)
  rw [polarBilin_titsQF] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0
  rw [titsBilin_natCast] at h0
  have hlin : (b : ℝ) * (2 * v 0 - (a : ℝ) * v 1) = 0 := by
    linarith
  have h2 : 2 * v 0 = (a : ℝ) * v 1 := by
    rcases mul_eq_zero.mp hlin with h | h
    · exact absurd h hb'
    · linarith
  refine Submodule.mem_span_singleton.mpr ⟨v 0 / (a : ℝ), ?_⟩
  funext i
  fin_cases i
  · show (v 0 / (a : ℝ)) * (a : ℝ) = v 0
    field_simp
  · show (v 0 / (a : ℝ)) * 2 = v 1
    field_simp
    linarith

/-- The radical is exactly the line spanned by `(a, 2)` at `a*b = 4`. -/
lemma radical_eq_span (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) :=
  le_antisymm (radical_le_span a b ha hb)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (mem_radical_pair a b hab))

theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  rw [radical_eq_span a b ha hb hab]
  refine finrank_span_singleton ?_
  intro h
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_one, Pi.zero_apply] at h1
  norm_num at h1

theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) :=
  radical_eq_span a b ha hb hab

end OperatorFirst.CoxeterRankTwo
