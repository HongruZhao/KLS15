import KLSConstantImprovement.ActualSourceUnfilteredDeficit405

/-! Positive regularization of the coefficient Gram on the fixed source
and fixed tensor. The exact row-coefficient gap pays the bottom defect
without changing source coordinates or supplying a positive-rank premise. -/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualRegularizedMatchedFrame405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceMeanGramCongruence405 ActualTensorRowCongruence405 ActualMatchedFrame405
open ActualSourceMatchedDeficit405 ActualSourceUnfilteredDeficit405
open ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405 ActualSourceQuarticEnergy405
open ActualSourceBLFilter405 ActualCanonicalMetricEnergyGraph
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def regularizedCoefficientGram (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := sourceCoefficientGram T + ε • 1

theorem regularizedCoefficientGram_posDef
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 < ε) :
    (regularizedCoefficientGram T ε).PosDef :=
  Matrix.PosDef.posSemidef_add (matrixTraceGram_posSemidef .one T hT)
    ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).smul hε)

theorem exists_regularized_fourth_root_frame
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 < ε) :
    ∃ R S : Matrix (Fin n) (Fin n) ℝ,
      R.IsSymm ∧ S.IsSymm ∧ R * S = 1 ∧ S * R = 1 ∧
      R * R = CFC.sqrt (regularizedCoefficientGram T ε) ∧
      regularizedCoefficientGram T ε = (R * R) * (R * R) := by
  let Q := regularizedCoefficientGram T ε
  have hQ : Q.PosDef := regularizedCoefficientGram_posDef T hT ε hε
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
    Matrix.nonsing_inv_mul R hdet, hRR, ?_⟩
  rw [hRR]
  exact (CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg).symm

theorem regularized_row_coefficient_gap
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : regularizedCoefficientGram T ε = (R * R) * (R * R)) :
    R * R - sourceCoefficientGram (rowCongruentSlices T S) = ε • (S * S) := by
  have he : S * regularizedCoefficientGram T ε * S = R * R := by
    rw [hQ]
    calc
      _ = (S * R) * R * R * (R * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSR, hRS]; simp only [Matrix.one_mul, Matrix.mul_one]
  rw [coefficientGram_rowCongruentSlices]
  change R * R - S.transpose * sourceCoefficientGram T * S = _
  rw [hS.eq, ← he, ← Matrix.sub_mul, ← Matrix.mul_sub]
  simp only [regularizedCoefficientGram, add_sub_cancel_left, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one]

theorem regularized_row_coefficient_domination
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : regularizedCoefficientGram T ε = (R * R) * (R * R)) :
    (R * R - sourceCoefficientGram (rowCongruentSlices T S)).PosSemidef := by
  rw [regularized_row_coefficient_gap T ε R S hS hRS hSR hQ]
  have hSS : (S * S).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hS.eq] using
      Matrix.posSemidef_conjTranspose_mul_self S
  exact hSS.smul hε

theorem actual_dual_frame_mean_trace (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsSymm) (hRS : R * S = 1) (hSR : S * R = 1) :
    (sourceMeanGram d (rowCongruentSlices T S) * (R * R)).trace = (sourceMeanGram d T).trace := by
  rw [actual_meanGram_rowCongruentSlices]
  unfold congruentMeanGram
  rw [hS.eq]
  have hSS : S * (R * R) * S = 1 := by
    calc
      _ = (S * R) * (R * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSR, hRS]; simp only [Matrix.one_mul]
  calc
    _ = (sourceMeanGram d T * (S * (R * R) * S)).trace := by
      have he := Matrix.trace_mul_comm S (sourceMeanGram d T * S * (R * R))
      simpa only [Matrix.mul_assoc] using he
    _ = _ := by rw [hSS, Matrix.mul_one]

theorem actual_regularized_meanGram_square_bound (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 ≤ ε)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : regularizedCoefficientGram T ε = (R * R) * (R * R)) :
    matrixFrobeniusSq (sourceMeanGram d (rowCongruentSlices T S)) ≤ 2 * (sourceMeanGram d T).trace := by
  have hrow := rowCongruentSlices_symmetric T hT S
  have hp := trace_mul_nonneg_of_posSemidef (actual_meanGram_posSemidef d _ hrow)
    (regularized_row_coefficient_domination T ε hε R S hS hRS hSR hQ)
  rw [Matrix.mul_sub, Matrix.trace_sub, actual_dual_frame_mean_trace d T R S hS hRS hSR] at hp
  have hm := actual_meanGram_square_trace_cap d hiso (rowCongruentSlices T S) hrow
  nlinarith

theorem actual_regularized_matched_BL_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 ≤ ε)
    (R S : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hS : S.IsSymm)
    (hRS : R * S = 1) (hSR : S * R = 1)
    (hQ : regularizedCoefficientGram T ε = (R * R) * (R * R)) :
    actualMatrixBLCross d R (rowCongruentSlices T S) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x) (R * R)
          ∂potentialMeasure d.potential) := by
  let U := rowCongruentSlices T S
  have hU : ∀ i, (U i).IsSymm := rowCongruentSlices_symmetric T hT S
  have hc := actual_defect_family_cauchy d
    (fun p : Fin n × Fin n => actualHessianCongruenceForm d R p.1 p.2)
    (fun p : Fin n × Fin n => actualTensorGramForm d U p.1 p.2)
  simp only [Fintype.sum_prod_type] at hc
  have hA := actual_hessian_congruence_BL_deficit d hiso R
  have hB := actual_tensorGram_BL_deficit_cap d U hU
  have hM := actual_regularized_meanGram_square_bound d hiso T hT ε hε R S hS hRS hSR hQ
  have hm := mul_le_mul hA.2 (hB.2.trans hM) hB.1 (hA.1.trans hA.2)
  have hn : ((R.transpose * R) * (R.transpose * R)).trace = (regularizedCoefficientGram T ε).trace := by
    rw [hR.eq, ← hQ]
  have hfinal := hc.trans hm
  change actualMatrixBLCross d R U ^ 2 ≤ _ at hfinal
  rw [hn, hR.eq] at hfinal
  nlinarith

theorem exists_actual_regularized_matched_BL_cross_square (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (ε : ℝ) (hε : 0 < ε) :
    ∃ R S : Matrix (Fin n) (Fin n) ℝ,
      R.IsSymm ∧ S.IsSymm ∧ R * S = 1 ∧ S * R = 1 ∧
      R * R = CFC.sqrt (regularizedCoefficientGram T ε) ∧
      actualMatrixBLCross d R (rowCongruentSlices T S) ^ 2 ≤
        (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
          ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
            (CFC.sqrt (regularizedCoefficientGram T ε)) ∂potentialMeasure d.potential) := by
  obtain ⟨R, S, hR, hS, hRS, hSR, hRR, hQ⟩ := exists_regularized_fourth_root_frame T hT ε hε
  refine ⟨R, S, hR, hS, hRS, hSR, hRR, ?_⟩
  have hc := actual_regularized_matched_BL_cross_square d hiso T hT ε hε.le R S hR hS hRS hSR hQ
  rwa [hRR] at hc

end KLSConstantImprovement.ActualRegularizedMatchedFrame405

#print axioms KLSConstantImprovement.ActualRegularizedMatchedFrame405.exists_regularized_fourth_root_frame
#print axioms KLSConstantImprovement.ActualRegularizedMatchedFrame405.regularized_row_coefficient_gap
#print axioms KLSConstantImprovement.ActualRegularizedMatchedFrame405.actual_regularized_meanGram_square_bound
#print axioms KLSConstantImprovement.ActualRegularizedMatchedFrame405.actual_regularized_matched_BL_cross_square
#print axioms KLSConstantImprovement.ActualRegularizedMatchedFrame405.exists_actual_regularized_matched_BL_cross_square
