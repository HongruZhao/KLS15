import KLSConstantImprovement.ActualRealComplexMatrixOrder405
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Finite Schur/square-root comparison for a positive block Gram matrix.
The off-diagonal matrix is merely symmetric; it need not be positive.
This is the algebraic core of the tensor Gram square-root inequality.
-/
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualFiniteBlockGramComparison405
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open ActualRealComplexMatrixOrder405

private theorem hermitian_le_of_square_le (X B : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hB : B.PosSemidef) (hbound : X * X ≤ B * B) : X ≤ B := by
  have hself : IsSelfAdjoint X := hX
  have hab : 0 ≤ CFC.abs X - X := by
    rw [CFC.abs_sub_self X hself]
    exact nsmul_nonneg (CFC.negPart_nonneg X) 2
  have hlow : X ≤ CFC.sqrt (X * X) := by
    simpa only [CFC.abs, hself.star_eq] using (sub_nonneg.mp hab)
  have hmono := CFC.sqrt_le_sqrt (X * X) (B * B) hbound
  rw [CFC.sqrt_mul_self B hB.nonneg] at hmono
  exact hlow.trans hmono

theorem symmetric_le_of_square_le (X B : Matrix ι ι ℝ)
    (hX : X.IsSymm) (hB : B.PosSemidef) (hbound : X * X ≤ B * B) : X ≤ B := by
  have hXc : (complexMatrix X).IsHermitian := by
    change (complexMatrix X).conjTranspose = complexMatrix X
    rw [← complexMatrix_star, Matrix.conjTranspose_eq_transpose_of_trivial, hX.eq]
  have hb : complexMatrix X * complexMatrix X ≤ complexMatrix B * complexMatrix B := by
    have hc := (complexMatrix_le_iff (X * X) (B * B)).mpr hbound
    simpa only [map_mul] using hc
  exact (complexMatrix_le_iff X B).mp
    (hermitian_le_of_square_le _ _ hXc (complexMatrix_posSemidef hB) hb)

/-- A positive block Gram with diagonal A^2 has an upper off-diagonal
bound supplied by the positive square root of its Schur complement
normalization. No eigenvector or invertibility of the off-diagonal is
assumed. -/
theorem block_gram_upper (A S Q B : Matrix ι ι ℝ)
    (hA : A.PosDef) (hS : S.IsSymm) (hB : B.PosSemidef)
    (hBlock : (Matrix.fromBlocks (A * A) S S Q).PosSemidef)
    (hBsq : B * B = A⁻¹ * Q * A⁻¹) :
    S ≤ A * B * A := by
  letI : Invertible A := hA.isUnit.invertible
  have hA2ps : (A * A).PosSemidef := by
    simpa only [pow_two] using hA.posSemidef.pow 2
  have hA2 : (A * A).PosDef := hA2ps.posDef_iff_isUnit.mpr (hA.isUnit.mul hA.isUnit)
  letI : Invertible (A * A) := hA2.isUnit.invertible
  have hSstar : S.conjTranspose = S := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.eq
  have hSchur : (Q - S * (A * A)⁻¹ * S).PosSemidef := by
    have hb : (Matrix.fromBlocks (A * A) S S.conjTranspose Q).PosSemidef := by
      simpa only [hSstar] using hBlock
    simpa only [hSstar] using (Matrix.PosDef.fromBlocks₁₁ S Q hA2).mp hb
  let R := A⁻¹ * S * A⁻¹
  have hR : R.IsSymm := by
    change R.transpose = R
    simp only [R, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      hA.isHermitian.isSymm.eq, hS.eq, Matrix.mul_assoc]
  have hc := hSchur.conjTranspose_mul_mul_same A⁻¹
  have he : A⁻¹.conjTranspose * (Q - S * (A * A)⁻¹ * S) * A⁻¹ = B * B - R * R := by
    rw [Matrix.conjTranspose_nonsing_inv, hA.isHermitian.eq, Matrix.mul_inv_rev, hBsq]
    simp only [R, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  rw [he] at hc
  have hupper : R ≤ B := symmetric_le_of_square_le R B hR hB (Matrix.le_iff.mpr hc)
  have hcong := conjugate_le_conjugate_of_nonneg hupper hA.posSemidef.nonneg
  have hcancel : A * R * A = S := by
    dsimp only [R]
    simp only [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  rwa [hcancel] at hcong

end KLSConstantImprovement.ActualFiniteBlockGramComparison405

#print axioms KLSConstantImprovement.ActualFiniteBlockGramComparison405.symmetric_le_of_square_le
#print axioms KLSConstantImprovement.ActualFiniteBlockGramComparison405.block_gram_upper
