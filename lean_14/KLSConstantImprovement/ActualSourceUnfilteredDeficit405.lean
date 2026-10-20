import KLSConstantImprovement.ActualMatchedFrame405

/-! The unfiltered BL cross on the actual matched fields. This differs
from the shifted resolvent cross: there is no spectral half factor in
the unfiltered estimate. Both defect budgets are actual source theorems. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceUnfilteredDeficit405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceBLFilter405 ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405
open ActualSourceQuarticEnergy405 ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceMatchedDeficit405 ActualTensorRowCongruence405 ActualMatchedFrame405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_defect_family_cauchy {ι : Type*} [Fintype ι] (d : SourceData μ)
    (U V : ι → CanonicalMetricH1 d.potential) :
    (∑ i, sourceBLDefect d (U i) (V i)) ^ 2 ≤
      (∑ i, sourceBLDefect d (U i) (U i)) * (∑ i, sourceBLDefect d (V i) (V i)) := by
  have hp : ∀ t : ℝ, 0 ≤ (∑ i, sourceBLDefect d (V i) (V i)) * (t * t) +
      (2 * ∑ i, sourceBLDefect d (U i) (V i)) * t + ∑ i, sourceBLDefect d (U i) (U i) := by
    intro t
    have hn : 0 ≤ ∑ i, sourceBLDefect d (U i + t • V i) (U i + t • V i) :=
      Finset.sum_nonneg fun i _ => sourceBLDefect_nonnegative d _
    have he (i : ι) : sourceBLDefect d (U i + t • V i) (U i + t • V i) =
        sourceBLDefect d (U i) (U i) + 2 * t * sourceBLDefect d (U i) (V i) +
          t ^ 2 * sourceBLDefect d (V i) (V i) := by
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      rw [sourceBLDefect_symm d (V i) (U i)]
      ring
    simp_rw [he] at hn
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hn
    nlinarith
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith

def actualMatrixBLCross (d : SourceData μ) (R : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, sourceBLDefect d (actualHessianCongruenceForm d R i j) (actualTensorGramForm d T i j)

theorem actual_matrix_BL_cross_trace_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (R : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    actualMatrixBLCross d R T ^ 2 ≤
      (((R.transpose * R) * (R.transpose * R)).trace - (1/2 : ℝ) *
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R.transpose * R)
          ∂potentialMeasure d.potential) *
        (2 * (sourceMeanGram d T * sourceCoefficientGram T).trace) := by
  have hc := actual_defect_family_cauchy d
    (fun p : Fin n × Fin n => actualHessianCongruenceForm d R p.1 p.2)
    (fun p : Fin n × Fin n => actualTensorGramForm d T p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have hA := actual_hessian_congruence_BL_deficit d hiso R
  have hB := actual_tensorGram_BL_deficit_cap d T hT
  have hm := mul_le_mul hA.2
    (hB.2.trans (actual_meanGram_square_trace_cap d hiso T hT)) hB.1 (hA.1.trans hA.2)
  exact hc.trans hm

theorem actual_matched_BL_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : sourceCoefficientGram T = (R * R) * (R * R)) :
    actualMatrixBLCross d R (rowCongruentSlices T S) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (sourceCoefficientGram T).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R * R)
          ∂potentialMeasure d.potential) := by
  have hc := actual_matrix_BL_cross_trace_cap d hiso R (rowCongruentSlices T S)
    (rowCongruentSlices_symmetric T hT S)
  have hn : ((R.transpose * R) * (R.transpose * R)).trace = (sourceCoefficientGram T).trace := by
    rw [hR.eq, ← hQ]
  rw [actual_matched_meanGram_trace d T R S hS hRS hSR hQ, hn, hR.eq] at hc
  nlinarith

end KLSConstantImprovement.ActualSourceUnfilteredDeficit405
#print axioms KLSConstantImprovement.ActualSourceUnfilteredDeficit405.actual_defect_family_cauchy
#print axioms KLSConstantImprovement.ActualSourceUnfilteredDeficit405.actual_matrix_BL_cross_trace_cap
#print axioms KLSConstantImprovement.ActualSourceUnfilteredDeficit405.actual_matched_BL_cross_square
