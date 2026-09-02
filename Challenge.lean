import Mathlib

/-!
# The trace form of a tensor product of algebras, and the trace forms of
ℚ[x]/(x³ − x − 1), ℚ[x]/(x⁴ − x − 1) and their compositum

Twenty-three compared statements: seven GENERAL theorems (1)–(7), for
arbitrary finite free algebras over a commutative ring and arbitrary
quadratic forms over a linearly ordered field, followed by sixteen
INSTANCES (8)–(23) at the two golden-family fields `K₃ = ℚ[x]/(x³ − x − 1)`
and `K₄ = ℚ[x]/(x⁴ − x − 1)` and their compositum `K₃ ⊗[ℚ] K₄`.

## The general theorems (1)–(7)

Let `A`, `B` be finite free algebras over a commutative ring `R`. The trace
form of `A` is the symmetric bilinear form `(a, a') ↦ Tr_{A/R}(a a')`.

* (1)–(2) **the trace form of a tensor product is the tensor product of
  the trace forms, on pure tensors**: `Tr_{A ⊗ B}(a ⊗ b) = Tr_A(a) · Tr_B(b)`,
  and `⟨a ⊗ b, a' ⊗ b'⟩_{A ⊗ B} = ⟨a, a'⟩_A · ⟨b, b'⟩_B`.
* (3) **the Gram matrix of a tensor basis is the Kronecker product** of the
  two Gram matrices.
* (4) **the discriminant product formula**, with sign: for bases `bA`, `bB`
  indexed by finite types `ι`, `κ`,
  `disc(bA ⊗ bB) = disc(bA)^|κ| · disc(bB)^|ι|`.
* (5) **as quadratic forms**, when 2 is invertible in `R`: the trace
  quadratic form of `A ⊗ B` equals the tensor product (Mathlib's
  `QuadraticForm.tmul`) of the trace quadratic forms of `A` and `B`.
* (6)–(7) **the signature product rule**: over a linearly ordered field with
  2 invertible, for quadratic forms `Q₁`, `Q₂` on finite-dimensional spaces,
  with `sigPos`/`sigNeg` Mathlib's basis-free Sylvester invariants,
  `sigPos(Q₁ ⊗ Q₂) = p₁p₂ + n₁n₂` and `sigNeg(Q₁ ⊗ Q₂) = p₁n₂ + n₁p₂`.

None of (1)–(7) was in Mathlib at the pin; Mathlib supplies the trace of a
tensor product of endomorphisms, tensor bases, the determinant of a
Kronecker product, the tensor product of quadratic forms, orthogonal bases,
and the uniqueness half of Sylvester's law, from which they are proved.

## The instances (8)–(23)

`K₃` and `K₄` are the cubic and quartic fields cut out by the trinomials
`x^n − x − 1`, irreducible over ℚ for every n ≥ 2 by Selmer's theorem (in
Mathlib as `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`); their real
roots above 1 are the plastic number and the quartic root of `x⁴ = x + 1`.
In the power basis `1, x, …, x^(n−1)` the Gram matrix is `(Tr(x^(i+j)))`,
the Hankel matrix of the power sums of the roots.

* (8)–(9) **the Gram matrices, entrywise**: `Algebra.traceMatrix` of the
  power family equals the explicit integer Hankel matrix of the power sums
  (Newton's identities: `p = 3, 0, 2, 3, 2` for the cubic,
  `p = 4, 0, 0, 3, 4, 0, 3` for the quartic).
* (10)–(11) **the discriminants of the power bases**: `Algebra.discr` of the
  same families is `−23` and `−283`. Both are prime; the LMFDB records
  3.1.23.1 and 4.2.283.1 list these as the field discriminants, the power
  bases being integral bases (monogenic, index 1) — that identification is
  cited, not formalized.
* (12)–(13) **explicit diagonalisations**: the trace form, as a quadratic
  form, is equivalent (isometric) to the weighted sum of squares with
  weights `3, 2, −23/6` resp. `4, 4, −9/4, 283/36`.
* (14)–(17) **the Sylvester signatures, basis-free**: the trace form of `K₃`
  has signature `(2, 1)` and the trace form of `K₄` has signature `(3, 1)`.
* (18)–(23) **the compositum.** `K₃ ⊗[ℚ] K₄` is a field (23), the compositum
  `ℚ(ρ, Q)` of degree 12, since the degrees 3 and 4 are coprime; by the
  general theorems its trace form is the tensor product of the two: the
  trace of a pure tensor is the product of the traces (18), the Gram matrix
  of the tensor power family `xⁱ ⊗ yʲ` is the Kronecker product (19), the
  discriminant of that family is `(−23)⁴ · (−283)³` (20), and the Sylvester
  signature is `(7, 5)` (21)–(22) — the product rule (6)–(7) applied to
  `(2, 1)` and `(3, 1)`.

The signatures are three instances of the classical theorem that the trace
form of a number field with `r₁` real and `r₂` pairs of complex embeddings
has signature `(r₁ + r₂, r₂)` (Hermite 1856 for the Hankel form of a
polynomial; Taussky 1968 for the discriminant matrix of a number field;
Conner–Perlis 1984, Chapter I); here `(r₁, r₂) = (1, 1)`, `(2, 1)` and
`(2, 5)`. That general theorem is not formalized; the instances at the two
fields are proved by explicit congruence, and the compositum instance by the
general theorems (1)–(7). Every proof is kernel-checked; axioms on every
compared statement: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace TraceForms

open Polynomial
open scoped TensorProduct

/-! ## The general theorems -/

section General

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]

/-- **(1) The trace of a pure tensor is the product of the traces**, for finite
free algebras `A`, `B` over a commutative ring `R`. -/
theorem trace_tmul (a : A) (b : B) :
    Algebra.trace R (A ⊗[R] B) (a ⊗ₜ b) = Algebra.trace R A a * Algebra.trace R B b := by
  sorry

/-- **(2) The trace form of a tensor product, on pure tensors**, is the product
of the trace forms. -/
theorem traceForm_tmul (a a' : A) (b b' : B) :
    Algebra.traceForm R (A ⊗[R] B) (a ⊗ₜ b) (a' ⊗ₜ b') =
      Algebra.traceForm R A a a' * Algebra.traceForm R B b b' := by
  sorry

/-- **(3) The Gram matrix of a tensor basis is the Kronecker product** of the
Gram matrices of the factors. -/
theorem traceMatrix_tensorProduct {ι κ : Type*} (bA : Module.Basis ι R A)
    (bB : Module.Basis κ R B) :
    Algebra.traceMatrix R ⇑(bA.tensorProduct bB) =
      Matrix.kroneckerMap (· * ·) (Algebra.traceMatrix R ⇑bA) (Algebra.traceMatrix R ⇑bB) := by
  sorry

/-- **(4) The discriminant product formula**, with sign: the discriminant of a
tensor basis is `disc(bA)^|κ| · disc(bB)^|ι|`. -/
theorem discr_tensorProduct {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (bA : Module.Basis ι R A) (bB : Module.Basis κ R B) :
    Algebra.discr R ⇑(bA.tensorProduct bB) =
      Algebra.discr R ⇑bA ^ Fintype.card κ * Algebra.discr R ⇑bB ^ Fintype.card ι := by
  sorry

/-- **(5) The trace quadratic form of a tensor product is the tensor product of
the trace quadratic forms** (Mathlib's `QuadraticForm.tmul`), when 2 is
invertible in `R`. -/
theorem traceForm_toQuadraticMap_tensor [Invertible (2 : R)] :
    (Algebra.traceForm R (A ⊗[R] B)).toQuadraticMap =
      QuadraticForm.tmul (Algebra.traceForm R A).toQuadraticMap
        (Algebra.traceForm R B).toQuadraticMap := by
  sorry

end General

section Signature

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **(6) The signature product rule, positive part**: over a linearly ordered
field with 2 invertible, `sigPos (Q₁ ⊗ Q₂) = p₁ p₂ + n₁ n₂`. -/
theorem sigPos_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigPos (QuadraticForm.tmul Q₁ Q₂) = sigPos Q₁ * sigPos Q₂ + sigNeg Q₁ * sigNeg Q₂ := by
  sorry

/-- **(7) The signature product rule, negative part**:
`sigNeg (Q₁ ⊗ Q₂) = p₁ n₂ + n₁ p₂`. -/
theorem sigNeg_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigNeg (QuadraticForm.tmul Q₁ Q₂) = sigPos Q₁ * sigNeg Q₂ + sigNeg Q₁ * sigPos Q₂ := by
  sorry

end Signature

/-! ## The instances: the two golden-family fields -/

/-- **(8) The Gram matrix of the cubic trace form.** In the power family
`1, x, x²` of `ℚ[x]/(x³ − x − 1)`, the trace matrix is the Hankel matrix
of the power sums `3, 0, 2, 3, 2`. -/
theorem traceMatrix_cubic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![3, 0, 2; 0, 2, 3; 2, 3, 2] := by
  sorry

/-- **(9) The Gram matrix of the quartic trace form.** In the power family
`1, x, x², x³` of `ℚ[x]/(x⁴ − x − 1)`, the trace matrix is the Hankel
matrix of the power sums `4, 0, 0, 3, 4, 0, 3`. -/
theorem traceMatrix_quartic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  sorry

/-- **(10) The discriminant of the cubic power basis** is `−23`. -/
theorem discr_cubic :
    Algebra.discr ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -23 := by
  sorry

/-- **(11) The discriminant of the quartic power basis** is `−283`. -/
theorem discr_quartic :
    Algebra.discr ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -283 := by
  sorry

/-- **(12) Explicit diagonalisation of the cubic trace form**: as a quadratic
form it is equivalent to the weighted sum of squares with weights
`3, 2, −23/6`. -/
theorem traceForm_cubic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(3 : ℚ), 2, -23 / 6]) := by
  sorry

/-- **(13) Explicit diagonalisation of the quartic trace form**: as a
quadratic form it is equivalent to the weighted sum of squares with
weights `4, 4, −9/4, 283/36`. -/
theorem traceForm_quartic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(4 : ℚ), 4, -9 / 4, 283 / 36]) := by
  sorry

/-- **(14) The cubic trace form has positive index 2.** -/
theorem sigPos_cubic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 2 := by
  sorry

/-- **(15) The cubic trace form has negative index 1** — signature `(2, 1)`. -/
theorem sigNeg_cubic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 1 := by
  sorry

/-- **(16) The quartic trace form has positive index 3.** -/
theorem sigPos_quartic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 3 := by
  sorry

/-- **(17) The quartic trace form has negative index 1** — signature `(3, 1)`. -/
theorem sigNeg_quartic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 1 := by
  sorry

/-! ## The instances: the compositum

`K₃ ⊗[ℚ] K₄` is the compositum `ℚ(ρ, Q)`: the degrees 3 and 4 are coprime,
so the two fields are linearly disjoint and their tensor product is a field
(23). Statements (18)–(22) are the general theorems (1)–(7) at this pair:
Gram matrix the Kronecker product, discriminant `(−23)⁴ · (−283)³`, and
signature `(7, 5) = (2·3 + 1·1, 2·1 + 1·3)`, agreeing with the classical
`(r₁ + r₂, r₂)` for the compositum's two real and five complex places
(context, not compared). -/

/-- **(18) The trace of a pure tensor is the product of the traces**, at the
compositum. -/
theorem trace_tmul_compositum (x : AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))
    (y : AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) :
    Algebra.trace ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))
        (x ⊗ₜ y) =
      Algebra.trace ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X])) x *
        Algebra.trace ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) y := by
  sorry

/-- **(19) The Gram matrix of the compositum is the Kronecker product** of the
cubic and quartic Gram matrices, in the tensor power family `xⁱ ⊗ yʲ`
indexed by `Fin 3 × Fin 4`. -/
theorem traceMatrix_compositum :
    Algebra.traceMatrix ℚ
        (fun p : Fin 3 × Fin 4 =>
          (AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (p.1 : ℕ)) ⊗ₜ[ℚ]
            (AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (p.2 : ℕ))) =
      Matrix.kroneckerMap (· * ·) !![3, 0, 2; 0, 2, 3; 2, 3, 2]
        !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  sorry

/-- **(20) The discriminant of the tensor power family** of the compositum is
`(−23)⁴ · (−283)³`. -/
theorem discr_compositum :
    Algebra.discr ℚ
        (fun p : Fin 3 × Fin 4 =>
          (AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (p.1 : ℕ)) ⊗ₜ[ℚ]
            (AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (p.2 : ℕ))) =
      (-23) ^ 4 * (-283) ^ 3 := by
  sorry

/-- **(21) The compositum trace form has positive index 7.** -/
theorem sigPos_compositum :
    sigPos (Algebra.traceForm ℚ
        (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      = 7 := by
  sorry

/-- **(22) The compositum trace form has negative index 5** — signature `(7, 5)`. -/
theorem sigNeg_compositum :
    sigNeg (Algebra.traceForm ℚ
        (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      = 5 := by
  sorry

/-- **(23) The tensor product is a field**: the compositum `ℚ(ρ, Q)`, of
degree 12, since the degrees 3 and 4 are coprime. -/
theorem isField_compositum :
    IsField (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) := by
  sorry

end TraceForms
