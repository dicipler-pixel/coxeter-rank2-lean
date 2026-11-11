import Targets

/-!
# The radical of the rank-two Tits form at the affine boundary `a*b = 4`

Route: inertia / signature theory.  The two structural inputs are

* `Q(e₀) = 2b > 0`, so `Q` is positive definite on the line spanned by `e₀`, whence `1 ≤ sigPos Q`;
* `Q(a,2) = 0`, so `Q ≤ 0` on the line spanned by `(a,2)`, whence `sigPos Q + 1 ≤ finrank = 2`.

So `sigPos Q = 1`, and the inertia identity `sigPos + sigNeg + finrank (radical Q) = finrank`
together with the nontriviality of the radical (it contains the nonzero vector `(a, 2)`) forces
`sigNeg Q = 0` and `finrank (radical Q) = 1`.  The span statement is then containment plus
equality of finranks.
-/

set_option autoImplicit false

namespace OperatorFirst.CoxeterRankTwo

/-! ## Scalar identities for `titsForm` -/

lemma titsForm_one_zero (a b : ℤ) : titsForm a b 1 0 = 2 * (b : ℝ) := by
  simp [titsForm]

/-- Shifting the argument by `(a, 2)` changes `titsForm` by `2a(4 - ab)(1 + y)`. -/
lemma titsForm_shift (a b : ℤ) (x y : ℝ) :
    titsForm a b ((a : ℝ) + x) (2 + y)
      = titsForm a b x y + 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) * (1 + y) := by
  simp only [titsForm]
  push_cast
  ring

lemma titsForm_at_ab (a b : ℤ) (h : (a : ℝ) * (b : ℝ) = 4) :
    titsForm a b (a : ℝ) 2 = 0 := by
  rw [show (a : ℝ) = (a : ℝ) + 0 by ring, show (2 : ℝ) = 2 + 0 by ring, titsForm_shift, h]
  norm_num [titsForm]

/-! ## The common notation: `(a,2)` as a vector of `Fin 2 → ℝ` -/

/-- The integer product cast to `ℝ`. -/
lemma cast_mul_eq {a b : ℕ} (hab : a * b = 4) : (a : ℝ) * (b : ℝ) = 4 := by
  have h : ((a * b : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by rw [hab]
  push_cast at h
  exact h

lemma titsQF_shift (a b : ℤ) (h : (a : ℝ) * (b : ℝ) = 4) (v : Fin 2 → ℝ) :
    titsQF a b (![(a : ℝ), 2] + v) = titsQF a b v := by
  rw [titsQF_apply, titsQF_apply]
  have h0 : (![(a : ℝ), 2] + v) 0 = (a : ℝ) + v 0 := by simp
  have h1 : (![(a : ℝ), 2] + v) 1 = 2 + v 1 := by simp
  rw [h0, h1, titsForm_shift, h]
  ring

/-! ## `(a,2)` lies in the radical at `a*b = 4` -/

lemma titsQF_at_ab (a b : ℕ) (hab : a * b = 4) :
    titsQF (a : ℤ) (b : ℤ) ![(a : ℝ), 2] = 0 := by
  have h := titsForm_at_ab (a : ℤ) (b : ℤ) (cast_mul_eq hab)
  simpa using h

lemma mem_radical_at_four (a b : ℕ) (hab : a * b = 4) :
    ![(a : ℝ), 2] ∈ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) := by
  rw [QuadraticMap.mem_radical_iff']
  exact ⟨titsQF_at_ab a b hab, fun n => titsQF_shift _ _ (cast_mul_eq hab) n⟩

/-! ## Positive/negative definiteness on lines, from the sign of the value at a point -/

lemma posDef_span_of_pos (Q : QuadraticForm ℝ (Fin 2 → ℝ)) (w : Fin 2 → ℝ) (hw : 0 < Q w) :
    (Q.restrict (ℝ ∙ w)).PosDef := by
  intro x hx
  have hxE : (x : Fin 2 → ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [QuadraticMap.restrict_apply]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp x.2
  have hxt : (x : Fin 2 → ℝ) = t • w := ht.symm
  have htne : t ≠ 0 := by
    rintro rfl
    exact hxE (by rw [hxt]; simp)
  rw [hxt, QuadraticMap.map_smul, smul_eq_mul]
  exact mul_pos (mul_self_pos.mpr htne) hw

lemma nonpos_span_of_nonpos (Q : QuadraticForm ℝ (Fin 2 → ℝ)) (w : Fin 2 → ℝ) (hw : Q w ≤ 0) :
    ∀ x ∈ (ℝ ∙ w : Submodule ℝ (Fin 2 → ℝ)), Q x ≤ 0 := by
  intro x hx
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
  rw [← ht, QuadraticMap.map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg t) hw

/-! ## The two bounds on `sigPos` -/

lemma one_le_sigPos (a b : ℕ) (hb : 1 ≤ b) : 1 ≤ sigPos (titsQF (a : ℤ) (b : ℤ)) := by
  have hval : titsQF (a : ℤ) (b : ℤ) ![(1 : ℝ), 0] = 2 * (b : ℝ) := by
    simpa using titsForm_one_zero (a : ℤ) (b : ℤ)
  have hpos : 0 < titsQF (a : ℤ) (b : ℤ) ![(1 : ℝ), 0] := by
    rw [hval]
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    linarith
  have h := le_sigPos_of_posDef (titsQF (a : ℤ) (b : ℤ))
    (V := ℝ ∙ (![(1 : ℝ), 0] : Fin 2 → ℝ)) (posDef_span_of_pos _ _ hpos)
  rwa [finrank_span_singleton (by simpa using ne_zero_e0)] at h
where
  ne_zero_e0 : (![(1 : ℝ), 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this

lemma sigPos_le_one (a b : ℕ) (hab : a * b = 4) : sigPos (titsQF (a : ℤ) (b : ℤ)) ≤ 1 := by
  have hQ := titsQF_at_ab a b hab
  have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := titsQF (a : ℤ) (b : ℤ)) (V := ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ))
    (nonpos_span_of_nonpos _ _ hQ.le)
  rw [finrank_span_singleton (by simpa using ne_zero_pair_a a), Module.finrank_fin_fun] at h
  omega
where
  ne_zero_pair_a (a : ℕ) : (![(a : ℝ), 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this

/-! ## The radical is nonzero, so its finrank is positive -/

lemma finrank_radical_pos (a b : ℕ) (hab : a * b = 4) :
    0 < Module.finrank ℝ ↥(QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) := by
  have hmem := mem_radical_at_four a b hab
  have hne : (⟨![(a : ℝ), 2], hmem⟩ : ↥(QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)))) ≠ 0 := by
    intro h
    have h' : (![(a : ℝ), 2] : Fin 2 → ℝ) = 0 := congrArg Subtype.val h
    have := congrFun h' 1
    simp at this
  haveI : Nontrivial ↥(QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) := ⟨⟨_, 0, hne⟩⟩
  exact Module.finrank_pos

/-! ## A second, inertia-free proof of the finrank statement

The radical is neither `⊥` (it contains `(a,2) ≠ 0`) nor `⊤` (otherwise `Q = 0`, but
`Q(e₀) = 2b ≠ 0`); in a two-dimensional space that leaves one dimension. -/

lemma radical_ne_top (a b : ℕ) (hb : 1 ≤ b) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) ≠ ⊤ := by
  intro htop
  have hmem : (![(1 : ℝ), 0] : Fin 2 → ℝ) ∈ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) := by
    rw [htop]; exact Submodule.mem_top
  rw [QuadraticMap.mem_radical_iff'] at hmem
  have hval : titsQF (a : ℤ) (b : ℤ) ![(1 : ℝ), 0] = 2 * (b : ℝ) := by
    simpa using titsForm_one_zero (a : ℤ) (b : ℤ)
  rw [hval] at hmem
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  norm_num at hmem
  linarith [hmem.1]

theorem tits_radical_finrank_at_four_dimcount (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  have hlt : Module.finrank ℝ ↥(QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)))
      < Module.finrank ℝ (Fin 2 → ℝ) := Submodule.finrank_lt (radical_ne_top a b hb)
  rw [Module.finrank_fin_fun] at hlt
  have hpos := finrank_radical_pos a b hab
  omega

/-! ## The two targets -/

theorem tits_radical_finrank_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    Module.finrank ℝ (QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))) = 1 := by
  have hsp : sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 :=
    le_antisymm (sigPos_le_one a b hab) (one_le_sigPos a b hb)
  have hid := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := titsQF (a : ℤ) (b : ℤ))
  rw [hsp, Module.finrank_fin_fun] at hid
  have hpos := finrank_radical_pos a b hab
  omega

theorem tits_radical_eq_span_at_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b = 4) :
    QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ))
      = ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) := by
  have hle : ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ) ≤ QuadraticMap.radical (titsQF (a : ℤ) (b : ℤ)) :=
    Submodule.span_singleton_le_iff_mem _ _ |>.mpr (mem_radical_at_four a b hab)
  have hne : (![(a : ℝ), 2] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
  have h1 : Module.finrank ℝ ↥(ℝ ∙ (![(a : ℝ), 2] : Fin 2 → ℝ)) = 1 :=
    finrank_span_singleton hne
  have h2 := tits_radical_finrank_at_four a b ha hb hab
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])).symm

end OperatorFirst.CoxeterRankTwo
