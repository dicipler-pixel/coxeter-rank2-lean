import Targets

/-!
# The radical of the rank-two Tits form at the affine boundary `a * b = 4`

Route: completing the square.  At `a * b = 4` the Tits form is a positive multiple of the
square of a single linear form:

`b * Q(x,y) = 2 * (b*x - 2*y)^2`   (because `a*b = 4` turns `-2*a*b^2` into `-8*b`
and `2*a*b` into `8`).

So `b * Q v = 2 * (φ_b v)^2` for the functional `φ_b (x,y) = b x - 2 y`, and since `b ≠ 0` the
radical of `Q` is exactly the kernel of `φ_b`: `Q v = 0` forces `φ_b v = 0`, and `φ_b v = 0`
gives `Q (v + n) = Q n` for every `n`.  The kernel is the line `ℝ ∙ (a,2)` because `(a,2)` lies in
it and a nonzero functional out of `ℝ²` has one-dimensional kernel (rank-nullity).

No inertia identity, no determinant, no solving of two equations in two unknowns.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-- The linear functional `φ_b (x, y) = b * x - 2 * y`. -/
noncomputable def covec (b : ℕ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  (b : ℝ) • LinearMap.proj (0 : Fin 2) - 2 • LinearMap.proj (1 : Fin 2)

@[simp]
lemma covec_apply (b : ℕ) (v : Fin 2 → ℝ) : covec b v = (b : ℝ) * v 0 - 2 * v 1 := by
  simp [covec]

/-- Casting the hypothesis `a * b = 4` to `ℝ`. -/
lemma hab_real {a b : ℕ} (hab : a * b = 4) : (a : ℝ) * (b : ℝ) = 4 := by
  have h : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
  push_cast at h
  linarith

/-- Positivity of `b` as a real number, from `1 ≤ b`. -/
lemma pos_of_one_le {b : ℕ} (hb : 1 ≤ b) : (0 : ℝ) < (b : ℝ) := by
  have h : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  linarith

/-- The square-completion identity: `b * Q v = 2 * (φ_b v)^2` when `a * b = 4`. -/
lemma titsQF_mul_eq_sq {a b : ℕ} (hab : a * b = 4) (v : Fin 2 → ℝ) :
    (b : ℝ) * titsQF (a : ℤ) (b : ℤ) v = 2 * (covec b v) ^ 2 := by
  have habR := hab_real hab
  rw [titsQF_apply, titsForm, covec_apply]
  push_cast
  linear_combination (2 * v 1 ^ 2 - 2 * (b : ℝ) * v 0 * v 1) * habR

/-- At `a * b = 4` the radical of the Tits form is the kernel of `φ_b`. -/
lemma radical_eq_ker_covec {a b : ℕ} (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = LinearMap.ker (covec b) := by
  have hbR : (b : ℝ) ≠ 0 := ne_of_gt (pos_of_one_le hb)
  ext v
  rw [QuadraticMap.mem_radical_iff', LinearMap.mem_ker]
  constructor
  · rintro ⟨h0, -⟩
    have h := titsQF_mul_eq_sq (a := a) (b := b) hab v
    rw [h0, mul_zero] at h
    have h2 : (covec b v) ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  · intro hv
    refine ⟨?_, ?_⟩
    · have h := titsQF_mul_eq_sq (a := a) (b := b) hab v
      rw [hv] at h
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hbR
    · intro n
      have h1 := titsQF_mul_eq_sq (a := a) (b := b) hab (v + n)
      have h2 := titsQF_mul_eq_sq (a := a) (b := b) hab n
      simp only [map_add, hv, zero_add] at h1
      exact mul_left_cancel₀ hbR (h1.trans h2.symm)

/-- The functional `φ_b` is onto `ℝ` when `b ≠ 0`. -/
lemma covec_surjective {b : ℕ} (hb : 1 ≤ b) : Function.Surjective (covec b) := by
  have hbR : (b : ℝ) ≠ 0 := ne_of_gt (pos_of_one_le hb)
  intro r
  refine ⟨![(r / (b : ℝ)), 0], ?_⟩
  rw [covec_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, sub_zero]
  rw [mul_comm]
  exact div_mul_cancel₀ r hbR

/-- The kernel of `φ_b` is one-dimensional: rank-nullity for a nonzero functional. -/
lemma finrank_ker_covec {b : ℕ} (hb : 1 ≤ b) :
    Module.finrank ℝ (LinearMap.ker (covec b)) = 1 := by
  have htop : (covec b).range = ⊤ := LinearMap.range_eq_top.mpr (covec_surjective hb)
  have h := LinearMap.finrank_range_add_finrank_ker (covec b)
  rw [htop, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

/-- `(a, 2)` lies in the kernel of `φ_b` when `a * b = 4`. -/
lemma covec_apply_vec {a b : ℕ} (hab : a * b = 4) :
    covec b (![(a : ℝ), 2] : Fin 2 → ℝ) = 0 := by
  have habR := hab_real hab
  rw [covec_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

/-- The vector `(a, 2)` is nonzero because `1 ≤ a`. -/
lemma vec_ne_zero {a : ℕ} (ha : 1 ≤ a) : (![(a : ℝ), 2] : Fin 2 → ℝ) ≠ 0 := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Pi.zero_apply] at h0
  linarith

/-- At `a * b = 4` the kernel of `φ_b` is spanned by `(a, 2)`. -/
lemma ker_covec_eq_span {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    LinearMap.ker (covec b) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  set v : Fin 2 → ℝ := ![(a : ℝ), 2] with hv_def
  have hv0 : covec b v = 0 := by
    rw [hv_def]
    exact covec_apply_vec hab
  have hvne : v ≠ 0 := by
    rw [hv_def]
    exact vec_ne_zero ha
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact hv0
  · rw [finrank_ker_covec hb, finrank_span_singleton hvne]

/-- Affine side: the radical of the Tits form is one-dimensional at `a * b = 4`. -/
theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  rw [radical_eq_ker_covec hb hab]
  exact finrank_ker_covec hb

/-- Affine side, sharpest form: the radical is spanned by the vector `(a, 2)`. -/
theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))
      = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  rw [radical_eq_ker_covec hb hab]
  exact ker_covec_eq_span ha hb hab

end OperatorFirst.CoxeterRankTwo
