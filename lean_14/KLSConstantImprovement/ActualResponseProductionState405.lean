import KLSConstantImprovement.ActualResponseShiftedFilter405

/-! Exact actual-source response production state for the same original
law and fixed tensor. The shifted cross is the already constructed
scalar filter, with its conserved mean and nonnegative extra paid. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseProductionState405
open KLS ActualBoundedCanonicalSource ActualResponseGlobalR1Balance405 ActualResponseGlobalHBalance405
open ActualResponseShiftedFilter405 ActualResponseHessianPair405 ActualQuadraticRowCurvature405
open ActualQuadraticResponseField405 ActualAffineResponseHilbert405 ActualSourceDirectCubicBalance405
open ActualSourceMeanGram405 ActualSourceMatchedDeficit405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_response_paid_production_state (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    0 ≤ (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) ∧
      (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) +
        (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) =
          2 * (sourceMeanGram d T).trace - 2 * actualMatrixFilterCross d 1 T ∧
      (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) =
        (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) + (sourceMeanGram d T).trace -
          actualMatrixFilterCross d 1 T -
            ((∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential) +
              (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential)) / 2 := by
  have hfilter := actual_shifted_moment_filter_identity d hiso T
  have hθ := actual_response_curvature_extra_identity d hn hμ T h12 h23 hC hM
  have hH := actual_response_global_H_balance d hn hμ T h12 h23 hC hM
  have hnonneg := integral_nonneg_of_ae (actualResponseExtra_nonnegative_ae d hn hμ T h12 h23)
  refine ⟨hnonneg, ?_, ?_⟩
  · linarith only [hfilter, hθ]
  · linarith only [hfilter, hθ, hH]

end KLSConstantImprovement.ActualResponseProductionState405

#print axioms KLSConstantImprovement.ActualResponseProductionState405.actual_response_paid_production_state
