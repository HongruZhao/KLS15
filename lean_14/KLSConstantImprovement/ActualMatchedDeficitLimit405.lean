import KLSConstantImprovement.ActualRegularizedMatchedFrame405
import KLSConstantImprovement.ActualMatchedFormInvariance405
import KLSConstantImprovement.ActualHessianSandwichContinuity405
import KLSConstantImprovement.ActualCubicGramHalfBinding405

/-! The literal unfiltered matched deficit estimate, including singular
coefficient Gram. Only constant matrices are regularized; the actual source,
tensor and base form pairing are fixed throughout the scalar limit. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualMatchedDeficitLimit405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceUnfilteredDeficit405 ActualRegularizedMatchedFrame405
open ActualMatchedFormInvariance405 ActualHessianSandwichContinuity405
open ActualCubicGramHalfBinding405 ActualDeficitTensorBounds
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_base_BL_cross_regularized_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (ε : ℝ) (hε : 0 < ε) :
    actualMatrixBLCross d 1 T ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (regularizedCoefficientGram T ε)) ∂potentialMeasure d.potential) := by
  obtain ⟨R, S, _, _, _, hSR, _, hb⟩ :=
    exists_actual_regularized_matched_BL_cross_square d hiso T hT ε hε
  rwa [actual_dual_frame_BL_cross_invariance d hiso T R S hSR] at hb

theorem actual_base_BL_cross_gram_half_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    actualMatrixBLCross d 1 T ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (sourceCoefficientGram T).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential) := by
  have hmoment := actual_regularized_gram_sandwich_tendsto d T hT
  have ht : Tendsto (fun k => regularizedCoefficientGram T (cutoffScale k)) atTop
      (𝓝 (sourceCoefficientGram T)) := by
    simpa only [regularizedCoefficientGram, zero_smul, add_zero] using
      tendsto_const_nhds.add (cutoffScale_tendsto_zero.smul_const (1 : Matrix (Fin n) (Fin n) ℝ))
  have htrace : Tendsto (fun k => (regularizedCoefficientGram T (cutoffScale k)).trace)
      atTop (𝓝 (sourceCoefficientGram T).trace) := by
    have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.trace) := by fun_prop
    exact hc.continuousAt.tendsto.comp ht
  have hmoment' : Tendsto (fun k => ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
      (CFC.sqrt (regularizedCoefficientGram T (cutoffScale k))) ∂potentialMeasure d.potential)
      atTop (𝓝 (∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
        (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential)) := by
    simpa only [regularizedCoefficientGram, add_comm] using hmoment
  exact ge_of_tendsto ((htrace.const_mul 2).sub hmoment' |>.const_mul (sourceMeanGram d T).trace)
    (Eventually.of_forall fun k => actual_base_BL_cross_regularized_cap d hiso T hT _ (cutoffScale_pos k))

theorem coefficientGram_trace_eq_tensorSquare
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (sourceCoefficientGram T).trace = tensorSquare T := by
  rw [tensorSquare_eq_sum_slices]
  simp only [sourceCoefficientGram, Matrix.trace, Matrix.diag, matrixTraceGram, Matrix.one_mul, Matrix.mul_one]
  exact Finset.sum_congr rfl fun i _ => (matrixFrobeniusSq_eq_trace_sq (hT i)).symm

theorem actual_fullSymmetric_base_BL_cross_deficit_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    actualMatrixBLCross d 1 T ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * tensorSquare T -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential) := by
  have hT (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hb := actual_base_BL_cross_gram_half_cap d hiso T hT
  rwa [coefficientGram_trace_eq_tensorSquare T hT] at hb

end KLSConstantImprovement.ActualMatchedDeficitLimit405
#print axioms KLSConstantImprovement.ActualMatchedDeficitLimit405.actual_base_BL_cross_regularized_cap
#print axioms KLSConstantImprovement.ActualMatchedDeficitLimit405.actual_base_BL_cross_gram_half_cap
#print axioms KLSConstantImprovement.ActualMatchedDeficitLimit405.coefficientGram_trace_eq_tensorSquare
#print axioms KLSConstantImprovement.ActualMatchedDeficitLimit405.actual_fullSymmetric_base_BL_cross_deficit_cap
