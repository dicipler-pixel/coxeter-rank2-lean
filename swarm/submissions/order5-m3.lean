import Targets

/-!
# `I₂(5) = H₂` is not crystallographic: a modulus-`4` obstruction

The Coxeter step `T = step a b` of the rank-two reflection model is the linear map

  `T (x, y) = ((a*b - 1) * x - a * y, b * x - y)`,

whose matrix `!![a*b - 1, -a; b, -1]` has determinant `1`.  Its characteristic
polynomial is `X² - (a*b - 2) X + 1`.

The argument below never computes the coefficients of a power of `T`.  Instead it
reduces the map mod `4`: if `T^5 = id` over `ℤ`, then the reduction of `T` has
`F^5 = id` on the `16`-element set `(ZMod 4)²`.  A finite verification over the
`16` residue pairs `(a, b)` shows that no such pair exists — over `ℤ/4` the
reduced step would have to satisfy `a ≡ b ≡ 0` and `a*b ≡ 2`, which is impossible.
Hence `T` has no period `5` at all, so the hypothesis of the golden-trace statement
is unsatisfiable and the trace identity holds vacuously; the second statement is the
same non-existence, directly.
-/

namespace OperatorFirst.CoxeterRankTwo

/-- Reduction of the lattice `ℤ × ℤ` to `(ZMod 4)²`. -/
def red (v : V) : ZMod 4 × ZMod 4 := ((v.1 : ZMod 4), (v.2 : ZMod 4))

/-- The Coxeter step in coordinates, reduced mod `4`. -/
def step4 (a b : ZMod 4) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  ((a * b - 1) * v.1 - a * v.2, b * v.1 - v.2)

/-- The coordinate formula for the Coxeter step. -/
theorem step_formula (a b : ℤ) (v : V) :
    step a b v = ((a * b - 1) * v.1 - a * v.2, b * v.1 - v.2) := by
  rcases v with ⟨x, y⟩
  ext <;> simp [step, s1, s2] <;> ring

/-- Reduction commutes with the step. -/
theorem red_step (a b : ℤ) (v : V) :
    red (step a b v) = step4 (a : ZMod 4) (b : ZMod 4) (red v) := by
  rcases v with ⟨x, y⟩
  simp only [red, step_formula, step4, Prod.mk.injEq]
  constructor <;> push_cast <;> ring

/-- Reduction commutes with iteration. -/
theorem red_iter (a b : ℤ) (n : ℕ) (v : V) :
    red (iter (step a b) n v) =
      iter (step4 (a : ZMod 4) (b : ZMod 4)) n (red v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      show red (step a b (iter (step a b) n v))
        = step4 (a : ZMod 4) (b : ZMod 4) (iter (step4 (a : ZMod 4) (b : ZMod 4)) n (red v))
      rw [red_step, ih]

/-- No residue pair mod `4` makes the Coxeter step the identity after five steps:
this is a finite check over the `16` pairs and the `16` residues of `(ZMod 4)²`. -/
theorem step4_not_five (a b : ZMod 4) :
    ¬ ∀ v : ZMod 4 × ZMod 4, iter (step4 a b) 5 v = v := by
  decide +revert

/-- Every residue vector mod `4` is the reduction of a lattice vector. -/
theorem red_surjective : ∀ w : ZMod 4 × ZMod 4, ∃ v : V, red v = w := by
  rintro ⟨x, y⟩
  refine ⟨((x.val : ℤ), (y.val : ℤ)), ?_⟩
  simp only [red, Prod.mk.injEq]
  constructor <;> (push_cast; exact ZMod.natCast_zmod_val _)

/-- **The integral Coxeter step has no period five.**  A single five-fold iterate
cannot be the identity: the reduction mod `4` of `T` would have order dividing `5`
in the finite set `(ZMod 4)²`, and no residue pair admits that. -/
theorem step_not_five (a b : ℤ) : ¬ ∀ v : V, iter (step a b) 5 v = v := by
  intro h5
  apply step4_not_five (a : ZMod 4) (b : ZMod 4)
  intro w
  obtain ⟨v, hv⟩ := red_surjective w
  rw [← hv, ← red_iter, h5]

/-- **`H₂` is not crystallographic** — in this model, exact period `5` forces the
golden trace identity; the hypothesis is in fact unsatisfiable (see
`step_not_five`), so the identity holds. -/
theorem order_five_forces_golden_trace (a b : ℕ)
    (h : HasExactPeriod (step (a : ℤ) (b : ℤ)) 5) :
    ((a * b : ℕ) : ℤ) ^ 2 - 3 * ((a * b : ℕ) : ℤ) + 1 = 0 := by
  exact absurd h.1 (step_not_five (a : ℤ) (b : ℤ))

/-- No integral representative has exact period five. -/
theorem no_integral_period_five (a b : ℕ) :
    ¬ HasExactPeriod (step (a : ℤ) (b : ℤ)) 5 :=
  fun h => step_not_five (a : ℤ) (b : ℤ) h.1

end OperatorFirst.CoxeterRankTwo
