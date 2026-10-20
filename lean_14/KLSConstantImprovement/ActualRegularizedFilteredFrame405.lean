import KLSConstantImprovement.ActualRegularizedMatchedFrame405

/-! The same fixed-source positive Gram regularization also pays the
shifted resolvent cross, retaining its spectral half factor. -/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualRegularizedFilteredFrame405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualTensorRowCongruence405 ActualSourceMatchedDeficit405 ActualSourceHessianCongruence405
open ActualRegularizedMatchedFrame405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actual_regularized_matched_filter_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 ≤ ε)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : regularizedCoefficientGram T ε = (R * R) * (R * R)) :
    (2 * actualMatrixFilterCross d R (rowCongruentSlices T S)) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R * R)
          ∂potentialMeasure d.potential) := by
  let U := rowCongruentSlices T S
  have hU : ∀ i, (U i).IsSymm := rowCongruentSlices_symmetric T hT S
  have hc := actual_matrix_filter_cross_deficit_cap d hiso R U hU
  have hA := actual_hessian_congruence_BL_deficit d hiso R
  have hM := actual_regularized_meanGram_square_bound d hiso T hT ε hε R S hS hRS hSR hQ
  have hm := mul_le_mul_of_nonneg_left hM (hA.1.trans hA.2)
  have hfinal := hc.trans (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 4))
  have hn : ((R.transpose * R) * (R.transpose * R)).trace = (regularizedCoefficientGram T ε).trace := by
    rw [hR.eq, ← hQ]
  rw [hn, hR.eq] at hfinal
  change (2 * actualMatrixFilterCross d R U) ^ 2 ≤ _
  nlinarith

theorem exists_actual_regularized_matched_filter_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 < ε) :
    ∃ R S : Matrix (Fin n) (Fin n) ℝ,
      R.IsSymm ∧ S.IsSymm ∧ R * S = 1 ∧ S * R = 1 ∧
      R * R = CFC.sqrt (regularizedCoefficientGram T ε) ∧
      (2 * actualMatrixFilterCross d R (rowCongruentSlices T S)) ^ 2 ≤
        (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
          ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
            (CFC.sqrt (regularizedCoefficientGram T ε)) ∂potentialMeasure d.potential) := by
  obtain ⟨R, S, hR, hS, hRS, hSR, hRR, hQ⟩ := exists_regularized_fourth_root_frame T hT ε hε
  refine ⟨R, S, hR, hS, hRS, hSR, hRR, ?_⟩
  have hc := actual_regularized_matched_filter_cross_square d hiso T hT ε hε.le R S hR hS hRS hSR hQ
  rwa [hRR] at hc

end KLSConstantImprovement.ActualRegularizedFilteredFrame405

#print axioms KLSConstantImprovement.ActualRegularizedFilteredFrame405.actual_regularized_matched_filter_cross_square
#print axioms KLSConstantImprovement.ActualRegularizedFilteredFrame405.exists_actual_regularized_matched_filter_cross_square
