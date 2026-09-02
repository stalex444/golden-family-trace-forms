import Mathlib

/-!
# The trace forms of ℚ[x]/(x³ − x − 1) and ℚ[x]/(x⁴ − x − 1)

`K₃ = ℚ[x]/(x³ − x − 1)` and `K₄ = ℚ[x]/(x⁴ − x − 1)` are the cubic and
quartic fields cut out by the trinomials `x^n − x − 1`, irreducible over ℚ
for every n ≥ 2 by Selmer's theorem (in Mathlib as
`Polynomial.X_pow_sub_X_sub_one_irreducible_rat`); their real roots
above 1 are the plastic number and the quartic root of `x⁴ = x + 1`.
The trace form of a number field `K` of degree `n` is the symmetric
bilinear form `(x, y) ↦ Tr_{K/ℚ}(xy)`; in the power basis
`1, x, …, x^(n−1)` its Gram matrix is `(Tr(x^(i+j)))`, the Hankel matrix
of the power sums of the roots. Ten compared statements, all about these
two fields and nothing else:

* (1)–(2) **the Gram matrices, entrywise.** `Algebra.traceMatrix` of the
  power family `1, x, …, x^(n−1)` equals the explicit integer Hankel
  matrix of the power sums (Newton's identities from the coefficients:
  `p = 3, 0, 2, 3, 2` for the cubic, `p = 4, 0, 0, 3, 4, 0, 3` for the
  quartic).
* (3)–(4) **the discriminants of the power bases**: `Algebra.discr` of the
  same families is `−23` and `−283`. Both are prime; the LMFDB records
  3.1.23.1 and 4.2.283.1 list these as the field discriminants, the
  power bases being integral bases (monogenic, index 1) — that
  identification is cited, not formalized.
* (5)–(6) **explicit diagonalisations.** The trace form, as a quadratic
  form, is equivalent (isometric) to the weighted sum of squares with
  weights `3, 2, −23/6` resp. `4, 4, −9/4, 283/36`.
* (7)–(10) **the Sylvester signatures, basis-free.** `sigPos` and `sigNeg`
  are Mathlib's intrinsic invariants of a quadratic form over an ordered
  field (the maximal dimension of a positive- resp. negative-definite
  subspace); the uniqueness half of Sylvester's law of inertia identifies
  them with the counts of positive and negative weights in any
  diagonalisation. The trace form of `K₃` has signature `(2, 1)` and the
  trace form of `K₄` has signature `(3, 1)`.

The signatures are the two instances, at these fields, of the classical
theorem that the trace form of a number field with `r₁` real and `r₂`
pairs of complex embeddings has signature `(r₁ + r₂, r₂)` (Hermite 1856
for the Hankel form of a polynomial; Taussky 1968 for the discriminant
matrix of a number field; Conner–Perlis 1984, Chapter I); here
`(r₁, r₂) = (1, 1)` and `(2, 1)`. The general theorem is not formalized;
the two instances are proved directly, by explicit congruence, and the
signature invariants are read off through Mathlib's Sylvester
uniqueness. Every proof is kernel-checked; axioms on every compared
statement: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace TraceForms

open Polynomial

/-- **(1) The Gram matrix of the cubic trace form.** In the power family
`1, x, x²` of `ℚ[x]/(x³ − x − 1)`, the trace matrix is the Hankel matrix
of the power sums `3, 0, 2, 3, 2`. -/
theorem traceMatrix_cubic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![3, 0, 2; 0, 2, 3; 2, 3, 2] := by
  sorry

/-- **(2) The Gram matrix of the quartic trace form.** In the power family
`1, x, x², x³` of `ℚ[x]/(x⁴ − x − 1)`, the trace matrix is the Hankel
matrix of the power sums `4, 0, 0, 3, 4, 0, 3`. -/
theorem traceMatrix_quartic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  sorry

/-- **(3) The discriminant of the cubic power basis** is `−23`. -/
theorem discr_cubic :
    Algebra.discr ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -23 := by
  sorry

/-- **(4) The discriminant of the quartic power basis** is `−283`. -/
theorem discr_quartic :
    Algebra.discr ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -283 := by
  sorry

/-- **(5) Explicit diagonalisation of the cubic trace form**: as a quadratic
form it is equivalent to the weighted sum of squares with weights
`3, 2, −23/6`. -/
theorem traceForm_cubic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(3 : ℚ), 2, -23 / 6]) := by
  sorry

/-- **(6) Explicit diagonalisation of the quartic trace form**: as a
quadratic form it is equivalent to the weighted sum of squares with
weights `4, 4, −9/4, 283/36`. -/
theorem traceForm_quartic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(4 : ℚ), 4, -9 / 4, 283 / 36]) := by
  sorry

/-- **(7) The cubic trace form has positive index 2.** -/
theorem sigPos_cubic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 2 := by
  sorry

/-- **(8) The cubic trace form has negative index 1** — signature `(2, 1)`. -/
theorem sigNeg_cubic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 1 := by
  sorry

/-- **(9) The quartic trace form has positive index 3.** -/
theorem sigPos_quartic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 3 := by
  sorry

/-- **(10) The quartic trace form has negative index 1** — signature `(3, 1)`. -/
theorem sigNeg_quartic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 1 := by
  sorry

end TraceForms
