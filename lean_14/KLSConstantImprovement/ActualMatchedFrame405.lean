import KLSConstantImprovement.ActualSourceMatchedDeficit405
import KLSConstantImprovement.ActualTensorRowCongruence405
import KLS.MatrixInverseSqrtLipschitz

/-! Matched fourth-root frames on the same source. Positive definite
coefficient Gram suffices; singular tensors will be handled by a numerical
tensor limit rather than changing the source generator or its coordinates. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualMatchedFrame405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceMeanGramCongruence405 ActualTensorRowCongruence405
open ActualSourceMatchedDeficit405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_matched_fourth_root_frame (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) : ∃ R S : Matrix (Fin n) (Fin n) ℝ,
      R.IsSymm ∧ S.IsSymm ∧ R * S = 1 ∧ S * R = 1 ∧ Q = (R * R) * (R * R) := by
  let D := CFC.sqrt Q
  let R := CFC.sqrt D
  let S := inverseSqrtMatrix D
  have hD : D.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hDu : IsUnit D := (CFC.isUnit_sqrt_iff Q hQ.posSemidef.nonneg).mpr hQ.isUnit
  have hRu : IsUnit R := (CFC.isUnit_sqrt_iff D hD.nonneg).mpr hDu
  have hdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hRu
  have hR : R.IsSymm := (CFC.sqrt_nonneg D).posSemidef.isHermitian.isSymm
  have hS : S.IsSymm := inverseSqrtMatrix_isSymm D
  have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D hD.nonneg
  refine ⟨R, S, hR, hS, Matrix.mul_nonsing_inv R hdet,
    Matrix.nonsing_inv_mul R hdet, ?_⟩
  rw [hRR]
  exact (CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg).symm

theorem matched_coefficientGram (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : sourceCoefficientGram T = (R * R) * (R * R)) :
    sourceCoefficientGram (rowCongruentSlices T S) = R * R := by
  rw [coefficientGram_rowCongruentSlices]
  change S.transpose * sourceCoefficientGram T * S = _
  rw [hS.eq, hQ]
  calc
    _ = (S * R) * R * R * (R * S) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hSR, hRS]; simp

theorem actual_matched_meanGram_trace (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsSymm) (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : sourceCoefficientGram T = (R * R) * (R * R)) :
    (sourceMeanGram d (rowCongruentSlices T S) *
      sourceCoefficientGram (rowCongruentSlices T S)).trace = (sourceMeanGram d T).trace := by
  rw [actual_meanGram_rowCongruentSlices, matched_coefficientGram T R S hS hRS hSR hQ]
  unfold congruentMeanGram
  rw [hS.eq]
  have hSS : S * (R * R) * S = 1 := by
    calc
      _ = (S * R) * (R * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSR, hRS]; simp
  calc
    _ = (sourceMeanGram d T * (S * (R * R) * S)).trace := by
      have he := Matrix.trace_mul_comm S (sourceMeanGram d T * S * (R * R))
      simpa only [Matrix.mul_assoc] using he
    _ = _ := by rw [hSS]; simp

theorem actual_matched_filter_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : sourceCoefficientGram T = (R * R) * (R * R)) :
    (2 * actualMatrixFilterCross d R (rowCongruentSlices T S)) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (sourceCoefficientGram T).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R * R)
          ∂potentialMeasure d.potential) := by
  have hc := actual_matrix_filter_cross_trace_cap d hiso R (rowCongruentSlices T S)
    (rowCongruentSlices_symmetric T hT S)
  have hn : ((R.transpose * R) * (R.transpose * R)).trace = (sourceCoefficientGram T).trace := by
    rw [hR.eq, ← hQ]
  rw [actual_matched_meanGram_trace d T R S hS hRS hSR hQ, hn, hR.eq] at hc
  nlinarith

theorem exists_actual_matched_filter_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (hQ : (sourceCoefficientGram T).PosDef) :
    ∃ R S : Matrix (Fin n) (Fin n) ℝ,
      R.IsSymm ∧ S.IsSymm ∧ R * S = 1 ∧ S * R = 1 ∧
      sourceCoefficientGram T = (R * R) * (R * R) ∧
      (2 * actualMatrixFilterCross d R (rowCongruentSlices T S)) ^ 2 ≤
        (sourceMeanGram d T).trace * (2 * (sourceCoefficientGram T).trace -
          ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R * R)
            ∂potentialMeasure d.potential) := by
  obtain ⟨R, S, hR, hS, hRS, hSR, he⟩ := exists_matched_fourth_root_frame _ hQ
  exact ⟨R, S, hR, hS, hRS, hSR, he,
    actual_matched_filter_cross_square d hiso T hT R S hR hS hRS hSR he⟩

end KLSConstantImprovement.ActualMatchedFrame405
#print axioms KLSConstantImprovement.ActualMatchedFrame405.exists_matched_fourth_root_frame
#print axioms KLSConstantImprovement.ActualMatchedFrame405.actual_matched_meanGram_trace
#print axioms KLSConstantImprovement.ActualMatchedFrame405.actual_matched_filter_cross_square
#print axioms KLSConstantImprovement.ActualMatchedFrame405.exists_actual_matched_filter_cross_square
