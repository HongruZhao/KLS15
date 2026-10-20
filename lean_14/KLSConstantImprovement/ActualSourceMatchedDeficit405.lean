import KLSConstantImprovement.ActualSourceQuarticEnergy405
import KLSConstantImprovement.ActualSourceFamilyBLFilter405
import KLSConstantImprovement.ActualSourceMeanGramCongruence405

/-! An actual-source spectral cross bound. The two families are the
constructed Hessian congruence and literal tensor Gram forms, with all
domains and both BL-defect caps discharged. Choice of a matched constant
normalizing frame is deliberately separate finite matrix algebra. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceMatchedDeficit405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricResolvent ActualSourceBLFilter405
open ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405
open ActualSourceQuarticEnergy405 ActualSourceFamilyBLFilter405
open ActualSourceMeanGram405 ActualSourceMeanGramOrder405 ActualSourceMeanGramCongruence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

def actualMatrixFilterCross (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, inner ℝ
    (canonicalMetricValue d.potential (actualHessianCongruenceForm d R i j))
    (canonicalMetricValue d.potential (actualTensorGramForm d T i j) - (2 : ℝ) •
      canonicalResolvent d.potential (t := 1) zero_lt_one
        (canonicalMetricValue d.potential (actualTensorGramForm d T i j)))

theorem actual_matrix_filter_cross_deficit_cap (d : SourceData μ)
    (hiso : IsIsotropic μ) (R : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    actualMatrixFilterCross d R T ^ 2 ≤
      (((R.transpose * R) * (R.transpose * R)).trace - (1/2 : ℝ) *
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R.transpose * R)
          ∂potentialMeasure d.potential) * matrixFrobeniusSq (sourceMeanGram d T) / 4 := by
  have hc := actual_family_filter_cross_square d
    (fun p : Fin n × Fin n => actualHessianCongruenceForm d R p.1 p.2)
    (fun p : Fin n × Fin n => actualTensorGramForm d T p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have hA := actual_hessian_congruence_BL_deficit d hiso R
  have hB := actual_tensorGram_BL_deficit_cap d T hT
  have hm := mul_le_mul hA.2 hB.2 hB.1 (hA.1.trans hA.2)
  exact hc.trans (div_le_div_of_nonneg_right hm (by norm_num))

theorem actual_meanGram_square_trace_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    matrixFrobeniusSq (sourceMeanGram d T) ≤
      2 * (sourceMeanGram d T * sourceCoefficientGram T).trace := by
  simpa only [congruentMeanGram, congruentCoefficientGram, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one] using
    actual_congruent_meanGram_square_bound d hiso T hT 1

theorem actual_matrix_filter_cross_trace_cap (d : SourceData μ)
    (hiso : IsIsotropic μ) (R : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    actualMatrixFilterCross d R T ^ 2 ≤
      (((R.transpose * R) * (R.transpose * R)).trace - (1/2 : ℝ) *
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R.transpose * R)
          ∂potentialMeasure d.potential) *
        (2 * (sourceMeanGram d T * sourceCoefficientGram T).trace) / 4 := by
  have hA := actual_hessian_congruence_BL_deficit d hiso R
  have hm := mul_le_mul_of_nonneg_left (actual_meanGram_square_trace_cap d hiso T hT)
    (hA.1.trans hA.2)
  exact (actual_matrix_filter_cross_deficit_cap d hiso R T hT).trans
    (div_le_div_of_nonneg_right hm (by norm_num))

end KLSConstantImprovement.ActualSourceMatchedDeficit405
#print axioms KLSConstantImprovement.ActualSourceMatchedDeficit405.actual_matrix_filter_cross_deficit_cap
#print axioms KLSConstantImprovement.ActualSourceMatchedDeficit405.actual_meanGram_square_trace_cap
#print axioms KLSConstantImprovement.ActualSourceMatchedDeficit405.actual_matrix_filter_cross_trace_cap
