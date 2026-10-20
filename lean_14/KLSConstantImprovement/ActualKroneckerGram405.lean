import KLSConstantImprovement.ActualFiniteBlockGramComparison405
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! The actual finite block Gram of an arbitrary symmetric slice family,
and its square-root Loewner bound when the slice Gram is nonsingular. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualKroneckerGram405
open ActualFiniteBlockGramComparison405
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def sliceGram (T : κ → Matrix ι ι ℝ) : Matrix ι ι ℝ := ∑ i, T i * T i

def sliceKronecker (T : κ → Matrix ι ι ℝ) : Matrix (ι × ι) (ι × ι) ℝ := ∑ i, T i ⊗ₖ T i

theorem sliceGram_posSemidef (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm) :
    (sliceGram T).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, (hT i).eq] using
    Matrix.posSemidef_conjTranspose_mul_self (T i)

theorem sliceKronecker_symmetric (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm) :
    (sliceKronecker T).IsSymm := by
  change (∑ i, T i ⊗ₖ T i).transpose = ∑ i, T i ⊗ₖ T i
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.kroneckerMap_transpose, (hT i).eq]

/-- The block matrix is a literal sum of transpose-times-self matrices. -/
theorem slice_blockGram_posSemidef (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm) :
    (Matrix.fromBlocks (sliceGram T ⊗ₖ (1 : Matrix ι ι ℝ))
      (sliceKronecker T) (sliceKronecker T) ((1 : Matrix ι ι ℝ) ⊗ₖ sliceGram T)).PosSemidef := by
  let X (i : κ) := Matrix.fromCols (T i ⊗ₖ (1 : Matrix ι ι ℝ))
    ((1 : Matrix ι ι ℝ) ⊗ₖ T i)
  have hi (i : κ) : (X i).conjTranspose * X i =
      Matrix.fromBlocks ((T i * T i) ⊗ₖ (1 : Matrix ι ι ℝ))
        (T i ⊗ₖ T i) (T i ⊗ₖ T i) ((1 : Matrix ι ι ℝ) ⊗ₖ (T i * T i)) := by
    dsimp only [X]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, (hT i).eq,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hsum : (∑ i, (X i).conjTranspose * X i).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (X i))
  have he : (∑ i, (X i).conjTranspose * X i) =
      Matrix.fromBlocks (sliceGram T ⊗ₖ (1 : Matrix ι ι ℝ))
        (sliceKronecker T) (sliceKronecker T) ((1 : Matrix ι ι ℝ) ⊗ₖ sliceGram T) := by
    simp_rw [hi]
    ext a b
    cases a <;> cases b <;>
      simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, sliceGram, sliceKronecker,
        Matrix.kroneckerMap_apply, Finset.sum_mul, Finset.mul_sum, Matrix.sum_apply]
  rwa [he] at hsum

/-- Concrete Gram-half Loewner comparison on a nonsingular Gram. There is
no positivity assumption on any later test matrix and no tensor symmetry
beyond symmetry of the individual slices. -/
theorem sliceKronecker_le_sqrtGram_of_posDef [Nonempty ι]
    (T : κ → Matrix ι ι ℝ) (hT : ∀ i, (T i).IsSymm)
    (hG : (sliceGram T).PosDef) :
    sliceKronecker T ≤ CFC.sqrt (sliceGram T) ⊗ₖ CFC.sqrt (sliceGram T) := by
  let A := CFC.sqrt (sliceGram T)
  have hA : A.PosDef :=
    (CFC.sqrt_nonneg (sliceGram T)).posSemidef.posDef_iff_isUnit.mpr
      ((CFC.isUnit_sqrt_iff (sliceGram T) hG.posSemidef.nonneg).mpr hG.isUnit)
  letI : Invertible A := hA.isUnit.invertible
  have hAsq : A * A = sliceGram T := CFC.sqrt_mul_sqrt_self _ hG.posSemidef.nonneg
  let P : Matrix (ι × ι) (ι × ι) ℝ := A ⊗ₖ (1 : Matrix ι ι ℝ)
  let B : Matrix (ι × ι) (ι × ι) ℝ := A⁻¹ ⊗ₖ A
  let Q : Matrix (ι × ι) (ι × ι) ℝ := (1 : Matrix ι ι ℝ) ⊗ₖ sliceGram T
  have hP : P.PosDef := hA.kronecker Matrix.PosDef.one
  have hB : B.PosSemidef := hA.inv.posSemidef.kronecker hA.posSemidef
  have hblock : (Matrix.fromBlocks (P * P) (sliceKronecker T) (sliceKronecker T) Q).PosSemidef := by
    simpa only [P, Q, ← Matrix.mul_kronecker_mul, Matrix.one_mul, hAsq] using
      slice_blockGram_posSemidef T hT
  have hBsq : B * B = P⁻¹ * Q * P⁻¹ := by
    simp only [P, B, Q, Matrix.inv_kronecker, inv_one,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hAsq]
  have hu := block_gram_upper P (sliceKronecker T) Q B hP (sliceKronecker_symmetric T hT)
    hB hblock hBsq
  have hc : P * B * P = A ⊗ₖ A := by
    simp only [P, B, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_inv_of_invertible]
  rwa [hc] at hu

end KLSConstantImprovement.ActualKroneckerGram405

#print axioms KLSConstantImprovement.ActualKroneckerGram405.slice_blockGram_posSemidef
#print axioms KLSConstantImprovement.ActualKroneckerGram405.sliceKronecker_le_sqrtGram_of_posDef
