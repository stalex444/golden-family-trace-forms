/-
Solution: proofs of the challenge statements, transferred from the proof
modules. `PdtSignature` and `PdtSignatureRho` hold the explicit integer
Gram matrices with their rational congruences to diagonal form;
`PdtTraceLink` proves that those matrices are `Algebra.traceMatrix` of the
power families (traces of the powers of the root, computed from
`r^4 = r + 1` resp. `r^3 = r + 1` through the left-multiplication
matrices) and derives the discriminants; `PdtTraceSignature` lifts the
congruences to isometries of the quadratic forms and reads off `sigPos`
and `sigNeg` through the uniqueness half of Sylvester's law of inertia.
-/
import PdtSignature
import PdtSignatureRho
import PdtTraceLink
import PdtTraceSignature

namespace TraceForms

open Polynomial

/-- the power family of the cubic root is the basis `bρ` of the proof module -/
private theorem powρ_eq :
    (fun i : Fin 3 => AdjoinRoot.root PDT.fρ ^ (i : ℕ)) = ⇑PDT.bρ :=
  (funext PDT.bρ_apply).symm

/-- the power family of the quartic root is the basis `bQ` of the proof module -/
private theorem powQ_eq :
    (fun i : Fin 4 => AdjoinRoot.root PDT.fQ ^ (i : ℕ)) = ⇑PDT.bQ :=
  (funext PDT.bQ_apply).symm

private theorem wρ_eq : (fun i : Fin 3 => PDT.Dρ i i) = ![(3 : ℚ), 2, -23 / 6] := by
  funext i
  fin_cases i <;>
    simp [PDT.Dρ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons]

private theorem wQ_eq : (fun i : Fin 4 => PDT.D i i) = ![(4 : ℚ), 4, -9 / 4, 283 / 36] := by
  funext i
  fin_cases i <;>
    simp [PDT.D, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons]

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
  rw [Algebra.discr_def]
  show (Algebra.traceMatrix ℚ (fun i : Fin 3 => AdjoinRoot.root PDT.fρ ^ (i : ℕ))).det = -23
  rw [powρ_eq, PDT.traceMatrix_bρ]
  exact PDT.detMρ

theorem discr_quartic :
    Algebra.discr ℚ
        (fun i : Fin 4 => AdjoinRoot.root (X ^ 4 - X - 1 : ℚ[X]) ^ (i : ℕ)) = -283 := by
  rw [Algebra.discr_def]
  show (Algebra.traceMatrix ℚ (fun i : Fin 4 => AdjoinRoot.root PDT.fQ ^ (i : ℕ))).det = -283
  rw [powQ_eq, PDT.traceMatrix_bQ]
  exact PDT.det_M

theorem traceForm_cubic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 3 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(3 : ℚ), 2, -23 / 6]) := by
  have h := PDT.qTraceρ_equiv
  rw [wρ_eq] at h
  exact h

theorem traceForm_quartic_equiv :
    QuadraticMap.Equivalent
      (Algebra.traceForm ℚ (AdjoinRoot (X ^ 4 - X - 1 : ℚ[X]))).toQuadraticMap
      (QuadraticMap.weightedSumSquares ℚ ![(4 : ℚ), 4, -9 / 4, 283 / 36]) := by
  have h := PDT.qTraceQ_equiv
  rw [wQ_eq] at h
  exact h

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

end TraceForms
