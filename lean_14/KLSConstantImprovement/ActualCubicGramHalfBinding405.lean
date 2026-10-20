import KLSConstantImprovement.ActualSourceGramHalfBudget405
import KLSConstantImprovement.ActualSourceMeanGramOrder405
import KLSConstantImprovement.ActualDeficitTensorBounds

/-! Full ordered cubic symmetry identifies the finite slice-square Gram
with the actual one-slot coefficient Gram. The actual Gram-half deficit
budget therefore uses exactly the same tensor norm and Gram as the
source moment/BL budget, without changing tensor slots. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualCubicGramHalfBinding405
open KLS ActualBoundedCanonicalSource ActualKroneckerGram405 ActualSourceGramHalfBudget405
open ActualSourceMeanGramOrder405 ActualDeficitTensorBounds
variable {n : ℕ} {μ : Measure (Space n)}

theorem fullSymmetric_sliceGram_eq_coefficientGram
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    sliceGram T = sourceCoefficientGram T := by
  ext i j
  simp only [sliceGram, sourceCoefficientGram, matrixTraceGram,
    Matrix.one_mul, Matrix.mul_one, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  have hs : T k a j = T j a k := by
    rw [hT23 k a j, hT12 k j a, hT23 j k a]
  rw [hT12 k i a, hs]

theorem actual_fullSymmetric_gram_half_deficit_budget (d : SourceData μ)
    (hiso : IsIsotropic μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    0 ≤ 2 * ActualDeficitTensorBounds.tensorSquare T -
      (∫ x, (CFC.sqrt (sourceCoefficientGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sourceCoefficientGram T) * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential) ∧
    2 * ActualDeficitTensorBounds.tensorSquare T -
      (∫ x, (CFC.sqrt (sourceCoefficientGram T) * coordinateHessian d.potential x *
        CFC.sqrt (sourceCoefficientGram T) * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential) ≤
      2 * ActualDeficitTensorBounds.tensorSquare T -
        (∫ x, ∑ i, (T i * coordinateHessian d.potential x * T i *
          coordinateHessian d.potential x).trace ∂potentialMeasure d.potential) := by
  have hT (i : Fin n) : (T i).IsSymm := by
    apply Matrix.IsSymm.ext
    intro j k
    exact hT23 i k j
  have hb := actual_gram_half_deficit_budget d hiso T hT
  rw [fullSymmetric_sliceGram_eq_coefficientGram T hT12 hT23] at hb
  have hN : ActualDeficitTensorBounds.tensorSquare T = ∑ i, KLS.matrixFrobeniusSq (T i) :=
    ActualDeficitTensorBounds.tensorSquare_eq_sum_slices T
  rw [hN]
  exact hb

end KLSConstantImprovement.ActualCubicGramHalfBinding405

#print axioms KLSConstantImprovement.ActualCubicGramHalfBinding405.fullSymmetric_sliceGram_eq_coefficientGram
#print axioms KLSConstantImprovement.ActualCubicGramHalfBinding405.actual_fullSymmetric_gram_half_deficit_budget
