import Targets

/-!
# The radical of the rank-two Tits form at the affine boundary `a * b = 4`

An independent, coordinate-level proof of the two frozen statements
`tits_radical_eq_span_at_four` and `tits_radical_finrank_at_four`.

Nothing here uses the inertia identity; everything is computed on the Gram matrix
`!![2b, -ab; -ab, 2a]` and on the bilinear form `titsBilin`.

The two ingredients are

* `polarBilin_titsQF`: the polar form of `titsQF a b` is **twice** `titsBilin` (the library's
  `titsBilin` is the bilinear form in `Q(u+v) = Qu + Qv + B(u,v)`, not half of the polar form),
  so, `2` being invertible in `ℝ`, the radical of `titsQF a b` is the kernel of the polar map
  (`QuadraticMap.radical_eq_ker_polarBilin`);
* `titsBilin_witness`: `titsBilin a b ((a,2), (x,y)) = a * y * (4 - a*b)`, so at `a * b = 4`
  the vector `(a, 2)` is orthogonal to everything.

For the reverse inclusion `radical ≤ span{(a,2)}` only one of the two coordinate equations is
used: the radical condition says `v = (x, y)` pairs to zero with `(1, 0)`, which reads
`b * (2*x - a*y) = 0`; since `b ≥ 1` we get `2*x = a*y`, hence `x = (y/2) * a` and
`y = (y/2) * 2`, i.e. `v = (y/2) • (a, 2)`. This step does not use `a * b = 4`. The dimension
statement is then `finrank_span_singleton` applied to the nonzero vector `(a, 2)` (its second
coordinate is `2 ≠ 0`, so no hypothesis on `a` is needed).
-/

namespace OperatorFirst.CoxeterRankTwo

/-! ## The polar form in coordinates -/

/-- The polar form of the Tits quadratic form is twice the Tits bilinear form. -/
lemma polarBilin_titsQF (a b : ℤ) (u v : Fin 2 → ℝ) :
    QuadraticMap.polarBilin (titsQF a b) u v = 2 * titsBilin a b (u 0, u 1) (v 0, v 1) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, titsQF_apply, Pi.add_apply,
    titsForm, titsBilin]
  push_cast
  ring

/-- Over `ℝ`, where `2` is invertible, the radical of a quadratic map is the kernel of its polar
bilinear form. -/
lemma radical_eq_ker_polarBilin_real {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticMap ℝ M ℝ) : Q.radical = LinearMap.ker Q.polarBilin := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact QuadraticMap.radical_eq_ker_polarBilin

/-! ## Pairing against the witness `(a, 2)` -/

/-- The product `a * b` is `4` as a real number at the affine boundary. -/
lemma cast_mul_eq_four (a b : ℕ) (hab : a * b = 4) : ((a : ℤ) * (b : ℤ) : ℝ) = 4 := by
  have h : ((a * b : ℕ) : ℝ) = 4 := by rw [hab]; norm_num
  push_cast at h ⊢
  exact h

/-- `(a, 2)` pairs with `(x, y)` to `a * y * (4 - a * b)`. -/
lemma titsBilin_witness_factored (a b : ℤ) (x y : ℝ) :
    titsBilin a b ((a : ℝ), 2) (x, y) = (a : ℝ) * y * (4 - ((a * b : ℤ) : ℝ)) := by
  simp only [titsBilin]
  push_cast
  ring

/-- At `a * b = 4` the witness `(a, 2)` is orthogonal to every vector. -/
lemma titsBilin_witness (a b : ℕ) (hab : a * b = 4) (x y : ℝ) :
    titsBilin (a : ℤ) (b : ℤ) ((a : ℝ), 2) (x, y) = 0 := by
  have habR : ((a : ℤ) * (b : ℤ) : ℝ) = 4 := cast_mul_eq_four a b hab
  simp only [titsBilin]
  push_cast at habR ⊢
  linear_combination (-((a : ℝ) * y)) * habR

/-! ## The radical at `a * b = 4` -/

/-- The radical of the Tits form at the affine boundary is exactly the line spanned by `(a, 2)`. -/
lemma tits_radical_eq_span_aux (a b : ℕ) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have hbR : (b : ℝ) ≠ 0 := by
    have hb0 : (0 : ℕ) < b := Nat.lt_of_lt_of_le Nat.zero_lt_one hb
    exact_mod_cast hb0.ne'
  refine le_antisymm ?_ ?_
  · -- a radical vector is orthogonal to everything, hence to `(1, 0)`, giving `2 * x = a * y`
    intro v hv
    have hker : QuadraticMap.polarBilin (titsQF (a : ℤ) (b : ℤ)) v = 0 :=
      LinearMap.mem_ker.mp (QuadraticMap.radical_le_ker_polarBilin hv)
    have horth : ∀ w : Fin 2 → ℝ, titsBilin (a : ℤ) (b : ℤ) (v 0, v 1) (w 0, w 1) = 0 := by
      intro w
      have hw := DFunLike.congr_fun hker w
      rw [polarBilin_titsQF] at hw
      simp only [LinearMap.zero_apply] at hw
      linarith
    have h1 : titsBilin (a : ℤ) (b : ℤ) (v 0, v 1) ((1 : ℝ), 0) = 0 := by
      simpa using horth (![(1 : ℝ), 0] : Fin 2 → ℝ)
    have hfac : (b : ℝ) * (2 * v 0 - (a : ℝ) * v 1) = 0 := by
      simp only [titsBilin] at h1
      push_cast at h1
      linear_combination h1
    have h2 : 2 * v 0 = (a : ℝ) * v 1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hbR
      · linarith
    refine Submodule.mem_span_singleton.mpr ⟨v 1 / 2, ?_⟩
    funext i
    fin_cases i <;> simp
    linear_combination (-1 / 2) * h2
  · -- `(a, 2)` lies in the radical, so the line it spans does too
    rw [Submodule.span_singleton_le_iff_mem, radical_eq_ker_polarBilin_real, LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    have h0 : titsBilin (a : ℤ) (b : ℤ) ((a : ℝ), 2) (w 0, w 1) = 0 :=
      titsBilin_witness a b hab (w 0) (w 1)
    rw [polarBilin_titsQF]
    simpa using h0

/-! ## The frozen targets -/

theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  rw [tits_radical_eq_span_aux a b hb hab]
  refine finrank_span_singleton (v := (![(a : ℝ), 2] : Fin 2 → ℝ)) ?_
  intro h
  have h1 := congrFun h 1
  simp at h1

theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))
      = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) :=
  tits_radical_eq_span_aux a b hb hab

end OperatorFirst.CoxeterRankTwo
