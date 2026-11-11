import Targets

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

lemma polar_titsQF (a b : ℤ) (x y : Fin 2 → ℝ) :
    QuadraticMap.polar (titsQF a b) x y =
      titsBilin a b (x 0, x 1) (y 0, y 1) + titsBilin a b (y 0, y 1) (x 0, x 1) := by
  simp only [QuadraticMap.polar, titsQF_apply, titsForm, titsBilin, Pi.add_apply]
  push_cast
  ring

lemma mem_radical_iff_polar (a b : ℤ) (v : Fin 2 → ℝ) :
    v ∈ QuadraticMap.radical (titsQF a b) ↔
      ∀ n : Fin 2 → ℝ, QuadraticMap.polar (titsQF a b) v n = 0 := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  rw [QuadraticMap.radical_eq_ker_polarBilin]
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply]

lemma radical_eq_span_at_four (a b : ℤ) (ha : (a : ℝ) ≠ 0)
    (hab : (a : ℝ) * (b : ℝ) = 4) :
    QuadraticMap.radical (titsQF a b) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have hb : (b : ℝ) ≠ 0 := by
    intro hb0
    rw [hb0, mul_zero] at hab
    norm_num at hab
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_radical_iff_polar] at hv
    have h0 := hv ![1, 0]
    rw [polar_titsQF] at h0
    simp only [titsBilin] at h0
    push_cast at h0
    ring_nf at h0
    have hkey : (b : ℝ) * (4 * v 0 - 2 * (a : ℝ) * v 1) = 0 := by linarith [h0]
    have hfac : 4 * v 0 - 2 * (a : ℝ) * v 1 = 0 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact absurd h hb
      · exact h
    have hy : (a : ℝ) * v 1 = 2 * v 0 := by linarith
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0 / (a : ℝ), ?_⟩
    funext i
    fin_cases i <;> simp <;> field_simp <;> linarith
  · intro v hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [mem_radical_iff_polar]
    intro n
    rw [polar_titsQF]
    simp only [Pi.smul_apply, smul_eq_mul, titsBilin, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.cons_val]
    push_cast
    ring_nf
    linear_combination (-(2 * c * n 1 * (a : ℝ))) * hab

theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  have haR : (((a : ℤ)) : ℝ) ≠ 0 := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have h2 : (0 : ℝ) < (((a : ℤ)) : ℝ) := by exact_mod_cast h1
    exact ne_of_gt h2
  have habR : (((a : ℤ)) : ℝ) * (((b : ℤ)) : ℝ) = 4 := by
    have h : ((a * b : ℕ) : ℝ) = 4 := by rw [hab]; norm_num
    push_cast at h
    push_cast
    linarith
  rw [radical_eq_span_at_four (a : ℤ) (b : ℤ) haR habR]
  have hne : (![(a : ℝ), 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h2 := congrFun h 1
    simp at h2
  exact finrank_span_singleton hne

theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have haR : (((a : ℤ)) : ℝ) ≠ 0 := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
    have h2 : (0 : ℝ) < (((a : ℤ)) : ℝ) := by exact_mod_cast h1
    exact ne_of_gt h2
  have habR : (((a : ℤ)) : ℝ) * (((b : ℤ)) : ℝ) = 4 := by
    have h : ((a * b : ℕ) : ℝ) = 4 := by rw [hab]; norm_num
    push_cast at h
    push_cast
    linarith
  exact radical_eq_span_at_four (a : ℤ) (b : ℤ) haR habR

end OperatorFirst.CoxeterRankTwo
