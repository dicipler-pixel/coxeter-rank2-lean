import Targets

/-!
# Signature of the rank-two Tits form above the affine boundary

For `a, b ≥ 1` with `4 < a * b` the Tits form `titsQF a b` on `ℝ²` is indefinite:
`titsForm a b 1 0 = 2b > 0` and `titsForm a b a 2 = 2a(4 - ab) < 0`.
A quadratic form on a two-dimensional space taking both signs has signature `(1, 1)`.

The argument uses a diagonalisation of the form: by
`QuadraticForm.equivalent_weightedSumSquares` every real quadratic form on a finite-dimensional
space is equivalent to `weightedSumSquares ℝ w` for some weight vector `w`, and by Sylvester's law
of inertia (`sigPos_of_equiv_weightedSumSquares`) the signature of the form counts the positive and
negative weights. Since the index set has cardinality two, and `Q` cannot be nonpositive (it is
positive at `(1, 0)`) nor nonnegative (it is negative at `(a, 2)`), the weight vector has exactly
one positive and one negative entry.
-/

namespace OperatorFirst.CoxeterRankTwo

open Finset

/-- A real quadratic form on `ℝ²` that takes both a positive and a negative value has signature
`(1, 1)`. -/
theorem sigPos_sigNeg_of_pos_and_neg (Q : QuadraticForm ℝ (Fin 2 → ℝ))
    (hpos : ∃ v, 0 < Q v) (hneg : ∃ v, Q v < 0) :
    sigPos Q = 1 ∧ sigNeg Q = 1 := by
  classical
  -- diagonalise `Q`: some weight vector `w` and an isometry `e` with `Q x = ∑ i, w i * (e x i)^2`
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  obtain ⟨e⟩ := hw
  have hw' : QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares ℝ w) := ⟨e⟩
  have hval : ∀ x : Fin 2 → ℝ, Q x = ∑ i, w i * (e x i) ^ 2 := by
    intro x
    rw [← QuadraticMap.IsometryEquiv.map_app e x, QuadraticMap.weightedSumSquares_apply]
    simp [smul_eq_mul, sq]
  -- the weight vector has a positive entry, else `Q` would be nonpositive everywhere
  have hsome_pos : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := hpos
    have hle : Q v ≤ 0 := by
      rw [hval v]
      exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (h i) (sq_nonneg _)
    linarith
  -- and a negative entry, else `Q` would be nonnegative everywhere
  have hsome_neg : ∃ i, w i < 0 := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := hneg
    have hge : 0 ≤ Q v := by
      rw [hval v]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)
    linarith
  -- the index set has two elements, so each of the two sets of weights has cardinality one
  have hcard : Nat.card (Fin (Module.finrank ℝ (Fin 2 → ℝ))) = 2 := by
    rw [Nat.card_fin, Module.finrank_fin_fun ℝ]
  have hpos_card : {i | 0 < w i}.ncard = 1 := by
    have hsum : {i | 0 < w i}.ncard + ({i | 0 < w i}ᶜ).ncard
        = Nat.card (Fin (Module.finrank ℝ (Fin 2 → ℝ))) := Set.ncard_add_ncard_compl _
    rw [hcard] at hsum
    have h1 : 0 < {i | 0 < w i}.ncard := by
      rw [Set.ncard_pos]
      exact hsome_pos
    have h2 : 0 < ({i | 0 < w i}ᶜ).ncard := by
      rw [Set.ncard_pos]
      obtain ⟨i, hi⟩ := hsome_neg
      exact ⟨i, by simpa using (not_lt.mpr hi.le : ¬ (0 < w i))⟩
    omega
  have hneg_card : {i | w i < 0}.ncard = 1 := by
    have hsum : {i | w i < 0}.ncard + ({i | w i < 0}ᶜ).ncard
        = Nat.card (Fin (Module.finrank ℝ (Fin 2 → ℝ))) := Set.ncard_add_ncard_compl _
    rw [hcard] at hsum
    have h1 : 0 < {i | w i < 0}.ncard := by
      rw [Set.ncard_pos]
      exact hsome_neg
    have h2 : 0 < ({i | w i < 0}ᶜ).ncard := by
      rw [Set.ncard_pos]
      obtain ⟨i, hi⟩ := hsome_pos
      exact ⟨i, by simpa using (not_lt.mpr hi.le : ¬ (w i < 0))⟩
    omega
  exact ⟨by rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares hw']; exact hpos_card,
    by rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares hw']; exact hneg_card⟩

theorem tits_signature_above_four (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : 4 < a * b) :
    sigPos (titsQF (a : ℤ) (b : ℤ)) = 1 ∧ sigNeg (titsQF (a : ℤ) (b : ℤ)) = 1 := by
  refine sigPos_sigNeg_of_pos_and_neg (titsQF (a : ℤ) (b : ℤ)) ⟨![1, 0], ?_⟩ ⟨![(a : ℝ), 2], ?_⟩
  · have hv : titsQF (a : ℤ) (b : ℤ) ![1, 0] = 2 * (b : ℝ) := by
      rw [titsQF_apply]
      simp [titsForm]
    rw [hv]
    have hb' : (0 : ℝ) < (b : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
    linarith
  · have hv : titsQF (a : ℤ) (b : ℤ) ![((a : ℝ)), 2]
        = 2 * (a : ℝ) * (4 - (a : ℝ) * (b : ℝ)) := by
      rw [titsQF_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, titsForm]
      push_cast
      ring
    rw [hv]
    have ha' : (0 : ℝ) < (a : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha)
    have hab' : (4 : ℝ) < (a : ℝ) * (b : ℝ) := by exact_mod_cast hab
    nlinarith

end OperatorFirst.CoxeterRankTwo
