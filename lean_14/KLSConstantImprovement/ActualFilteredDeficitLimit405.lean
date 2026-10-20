import KLSConstantImprovement.ActualRegularizedFilteredFrame405
import KLSConstantImprovement.ActualFilteredFrameInvariance405
import KLSConstantImprovement.ActualMatchedDeficitLimit405

/-! The literal shifted-filter matched half estimate for arbitrary,
possibly singular, coefficient Gram. Only finite coefficient matrices
vary in the scalar limit; source, tensor and scalar resolvent stay fixed. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Topology MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualFilteredDeficitLimit405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
open ActualSourceMatchedDeficit405 ActualRegularizedMatchedFrame405 ActualRegularizedFilteredFrame405
open ActualFilteredFrameInvariance405 ActualHessianSandwichContinuity405 ActualMatchedDeficitLimit405
open ActualCubicGramHalfBinding405 ActualDeficitTensorBounds
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem actual_base_filter_cross_regularized_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (ε : ℝ) (hε : 0 < ε) :
    (2 * actualMatrixFilterCross d 1 T) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * (regularizedCoefficientGram T ε).trace -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (regularizedCoefficientGram T ε)) ∂potentialMeasure d.potential) := by
  obtain ⟨R, S, _, _, _, hSR, _, hb⟩ :=
    exists_actual_regularized_matched_filter_cross_square d hiso T hT ε hε
  rwa [actual_dual_frame_filter_cross_invariance d hiso T R S hSR] at hb

theorem actual_base_filter_cross_gram_half_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (2 * actualMatrixFilterCross d 1 T) ^ 2 ≤
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
    (Eventually.of_forall fun k => actual_base_filter_cross_regularized_cap d hiso T hT _ (cutoffScale_pos k))

theorem actual_fullSymmetric_base_filter_cross_deficit_cap (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    (2 * actualMatrixFilterCross d 1 T) ^ 2 ≤
      (sourceMeanGram d T).trace * (2 * tensorSquare T -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential) := by
  have hT (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hb := actual_base_filter_cross_gram_half_cap d hiso T hT
  rwa [coefficientGram_trace_eq_tensorSquare T hT] at hb

theorem actual_fullSymmetric_base_filter_cross_half (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j) :
    |actualMatrixFilterCross d 1 T| ≤
      Real.sqrt ((sourceMeanGram d T).trace * (2 * tensorSquare T -
        ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
          (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential)) / 2 := by
  have hT (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hsq := actual_fullSymmetric_base_filter_cross_deficit_cap d hiso T hT12 hT23
  have hr : 0 ≤ (sourceMeanGram d T).trace := (actual_meanGram_posSemidef d T hT).trace_nonneg
  have hdelta : 0 ≤ 2 * tensorSquare T -
      ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
        (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential := by
    simpa only [rawHessianTraceSquare] using (actual_fullSymmetric_gram_half_deficit_budget d hiso T hT12 hT23).1
  have hroot := Real.sq_sqrt (mul_nonneg hr hdelta)
  have hroot0 := Real.sqrt_nonneg ((sourceMeanGram d T).trace * (2 * tensorSquare T -
    ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
      (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential))
  nlinarith [abs_nonneg (actualMatrixFilterCross d 1 T), sq_abs (actualMatrixFilterCross d 1 T)]

end KLSConstantImprovement.ActualFilteredDeficitLimit405

#print axioms KLSConstantImprovement.ActualFilteredDeficitLimit405.actual_base_filter_cross_regularized_cap
#print axioms KLSConstantImprovement.ActualFilteredDeficitLimit405.actual_base_filter_cross_gram_half_cap
#print axioms KLSConstantImprovement.ActualFilteredDeficitLimit405.actual_fullSymmetric_base_filter_cross_deficit_cap
#print axioms KLSConstantImprovement.ActualFilteredDeficitLimit405.actual_fullSymmetric_base_filter_cross_half
