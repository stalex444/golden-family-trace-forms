import Mathlib
import PdtSignature
import PdtSignatureRho
import PdtTraceLink
import PdtTraceSignature
import PdtTraceCompositum
import PdtTraceTensor

/-!
# Solution: proofs of the twenty-three compared statements

Each theorem of `Challenge.lean` is restated verbatim and proved by transfer
from the proof modules: the seven general theorems from `PdtTraceTensor`; the
two-field instances from `PdtTraceLink` and `PdtTraceSignature`; the
compositum instances from `PdtTraceCompositum` and `PdtTraceTensor` (the
discriminant and signature instances as corollaries of the general theorems).
The power families of the compared statements are identified with the proof
modules' bases by the two private lemmas `powρ_eq`, `powQ_eq`, and the tensor
power family with the tensor basis by `powL_eq`.
-/

namespace TraceForms

open Polynomial
open scoped TensorProduct

/-! ## The general theorems -/

section General

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]

theorem trace_tmul (a : A) (b : B) :
    Algebra.trace R (A ⊗[R] B) (a ⊗ₜ b) = Algebra.trace R A a * Algebra.trace R B b :=
  PDT.trace_tmul_general a b

theorem traceForm_tmul (a a' : A) (b b' : B) :
    Algebra.traceForm R (A ⊗[R] B) (a ⊗ₜ b) (a' ⊗ₜ b') =
      Algebra.traceForm R A a a' * Algebra.traceForm R B b b' :=
  PDT.traceForm_tmul_general a a' b b'

theorem traceMatrix_tensorProduct {ι κ : Type*} (bA : Module.Basis ι R A)
    (bB : Module.Basis κ R B) :
    Algebra.traceMatrix R ⇑(bA.tensorProduct bB) =
      Matrix.kroneckerMap (· * ·) (Algebra.traceMatrix R ⇑bA) (Algebra.traceMatrix R ⇑bB) :=
  PDT.traceMatrix_tensorProduct bA bB

theorem discr_tensorProduct {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (bA : Module.Basis ι R A) (bB : Module.Basis κ R B) :
    Algebra.discr R ⇑(bA.tensorProduct bB) =
      Algebra.discr R ⇑bA ^ Fintype.card κ * Algebra.discr R ⇑bB ^ Fintype.card ι :=
  PDT.discr_tensorProduct bA bB

theorem traceForm_toQuadraticMap_tensor [Invertible (2 : R)] :
    (Algebra.traceForm R (A ⊗[R] B)).toQuadraticMap =
      QuadraticForm.tmul (Algebra.traceForm R A).toQuadraticMap
        (Algebra.traceForm R B).toQuadraticMap :=
  PDT.qTrace_tensor

end General

section Signature

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem sigPos_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigPos (QuadraticForm.tmul Q₁ Q₂) = sigPos Q₁ * sigPos Q₂ + sigNeg Q₁ * sigNeg Q₂ :=
  PDT.sigPos_tmul Q₁ Q₂

theorem sigNeg_tmul (Q₁ : QuadraticForm K V) (Q₂ : QuadraticForm K W) :
    sigNeg (QuadraticForm.tmul Q₁ Q₂) = sigPos Q₁ * sigNeg Q₂ + sigNeg Q₁ * sigPos Q₂ :=
  PDT.sigNeg_tmul Q₁ Q₂

end Signature

/-! ## The instances: the two golden-family fields -/

/-- the power family of the compared statements is the basis `bρ` of the proof modules -/
private theorem powρ_eq :
    (fun i : Fin 3 => AdjoinRoot.root PDT.fρ ^ (i : ℕ)) = ⇑PDT.bρ := by
  funext i
  rw [PDT.bρ_apply]

/-- the power family of the compared statements is the basis `bQ` of the proof modules -/
private theorem powQ_eq :
    (fun i : Fin 4 => AdjoinRoot.root PDT.fQ ^ (i : ℕ)) = ⇑PDT.bQ := by
  funext i
  rw [PDT.bQ_apply]

theorem traceMatrix_cubic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![3, 0, 2; 0, 2, 3; 2, 3, 2] := by
  show Algebra.traceMatrix ℚ (fun i : Fin 3 => AdjoinRoot.root PDT.fρ ^ (i : ℕ)) = PDT.Mρ
  rw [powρ_eq]
  exact PDT.traceMatrix_bρ

theorem traceMatrix_quartic :
    Algebra.traceMatrix ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) =
      !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  show Algebra.traceMatrix ℚ (fun i : Fin 4 => AdjoinRoot.root PDT.fQ ^ (i : ℕ)) = PDT.M
  rw [powQ_eq]
  exact PDT.traceMatrix_bQ

theorem discr_cubic :
    Algebra.discr ℚ
        (fun i : Fin 3 => AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -23 := by
  have h : Algebra.discr ℚ (fun i : Fin 3 => AdjoinRoot.root PDT.fρ ^ (i : ℕ)) = -23 := by
    rw [powρ_eq, Algebra.discr_def]
    exact (congrArg Matrix.det PDT.traceMatrix_bρ).trans PDT.detMρ
  exact h

theorem discr_quartic :
    Algebra.discr ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -283 := by
  have h : Algebra.discr ℚ (fun i : Fin 4 => AdjoinRoot.root PDT.fQ ^ (i : ℕ)) = -283 := by
    rw [powQ_eq, Algebra.discr_def]
    exact (congrArg Matrix.det PDT.traceMatrix_bQ).trans PDT.det_M
  exact h

/-- the weight vector of the cubic diagonalisation is the diagonal of `Dρ` -/
private theorem wρ_eq : (fun i : Fin 3 => PDT.Dρ i i) = ![(3 : ℚ), 2, -23 / 6] := by
  funext i
  fin_cases i <;> simp [PDT.Dρ]

/-- the weight vector of the quartic diagonalisation is the diagonal of `D` -/
private theorem wQ_eq : (fun i : Fin 4 => PDT.D i i) = ![(4 : ℚ), 4, -9 / 4, 283 / 36] := by
  funext i
  fin_cases i <;> simp [PDT.D]

theorem traceForm_cubic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(3 : ℚ), 2, -23 / 6]) := by
  rw [← wρ_eq]
  exact PDT.qTraceρ_equiv

theorem traceForm_quartic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(4 : ℚ), 4, -9 / 4, 283 / 36]) := by
  rw [← wQ_eq]
  exact PDT.qTraceQ_equiv

theorem sigPos_cubic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 2 :=
  PDT.sigPos_traceρ

theorem sigNeg_cubic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap = 1 :=
  PDT.sigNeg_traceρ

theorem sigPos_quartic :
    sigPos (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 3 :=
  PDT.sigPos_traceQ

theorem sigNeg_quartic :
    sigNeg (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap = 1 :=
  PDT.sigNeg_traceQ

/-! ## The instances: the compositum, as corollaries of the general theorems -/

/-- the tensor power family is the tensor basis `bL` of the proof modules -/
private theorem powL_eq :
    (fun p : Fin 3 × Fin 4 =>
        (AdjoinRoot.root PDT.fρ ^ (p.1 : ℕ)) ⊗ₜ[ℚ] (AdjoinRoot.root PDT.fQ ^ (p.2 : ℕ))) =
      ⇑PDT.bL := by
  funext p
  rw [PDT.bL_apply, PDT.bρ_apply, PDT.bQ_apply]

theorem trace_tmul_compositum (x : AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))
    (y : AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) :
    Algebra.trace ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))
        (x ⊗ₜ y) =
      Algebra.trace ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X])) x *
        Algebra.trace ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) y :=
  PDT.trace_tmul x y

theorem traceMatrix_compositum :
    Algebra.traceMatrix ℚ
        (fun p : Fin 3 × Fin 4 =>
          (AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (p.1 : ℕ)) ⊗ₜ[ℚ]
            (AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (p.2 : ℕ))) =
      Matrix.kroneckerMap (· * ·) !![3, 0, 2; 0, 2, 3; 2, 3, 2]
        !![4, 0, 0, 3; 0, 0, 3, 4; 0, 3, 4, 0; 3, 4, 0, 3] := by
  show Algebra.traceMatrix ℚ
      (fun p : Fin 3 × Fin 4 =>
        (AdjoinRoot.root PDT.fρ ^ (p.1 : ℕ)) ⊗ₜ[ℚ] (AdjoinRoot.root PDT.fQ ^ (p.2 : ℕ))) =
    Matrix.kroneckerMap (· * ·) PDT.Mρ PDT.M
  rw [powL_eq]
  exact PDT.traceMatrix_bL

theorem discr_compositum :
    Algebra.discr ℚ
        (fun p : Fin 3 × Fin 4 =>
          (AdjoinRoot.root (X ^ 3 - X - 1 : ℚ[X]) ^ (p.1 : ℕ)) ⊗ₜ[ℚ]
            (AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (p.2 : ℕ))) =
      (-23) ^ 4 * (-283) ^ 3 := by
  show Algebra.discr ℚ
      (fun p : Fin 3 × Fin 4 =>
        (AdjoinRoot.root PDT.fρ ^ (p.1 : ℕ)) ⊗ₜ[ℚ] (AdjoinRoot.root PDT.fQ ^ (p.2 : ℕ))) =
    (-23) ^ 4 * (-283) ^ 3
  rw [powL_eq]
  exact PDT.discr_bL_of_general

theorem sigPos_compositum :
    sigPos (Algebra.traceForm ℚ
        (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      = 7 :=
  PDT.sigPos_traceL_of_general

theorem sigNeg_compositum :
    sigNeg (Algebra.traceForm ℚ
        (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      = 5 :=
  PDT.sigNeg_traceL_of_general

theorem isField_compositum :
    IsField (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]) ⊗[ℚ] AdjoinRoot (X ^ 4 - X - 1 : ℚ[X])) :=
  PDT.L_isField

end TraceForms
