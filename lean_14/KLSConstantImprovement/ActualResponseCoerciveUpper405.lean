import KLSConstantImprovement.ActualResponseFullSymCoercivity405
import KLSConstantImprovement.ActualResponseProductionState405
import KLSConstantImprovement.ActualFilteredDeficitLimit405

/-! The finite full-three-slot production estimate is instantiated on
the actual source third tensor, actual response and actual chosen weak
Jacobian. Its integrated consequence and the paid shifted filter give
the literal response-matrix bound used in the cubic variance assembly. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualResponseCoerciveUpper405
open KLS ActualBoundedCanonicalSource ActualResponseFullSymCoercivity405 ActualResponseProductionState405
open ActualResponseGlobalR1Balance405 ActualResponseGlobalHBalance405 ActualResponseHessianPair405
open ActualSourceResponseProduction405 ActualQuadraticResponseField405 ActualQuadraticResponseMetricFlux405
open ActualQuadraticRowCurvature405 ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualAffineResponseHilbert405 ActualSourceDirectCubicBalance405 ActualSourceMeanGram405
open ActualSourceMatchedDeficit405 ActualSourceMeanGramOrder405 ActualFilteredDeficitLimit405 ActualDeficitTensorBounds
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_response_fullSym_production_lower_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      4 * actualDirectMoment d T x / 3 ≤ actualResponseXi d hn hμ T x +
        actualRowCurvature d (quadraticResponseMatrix d T) x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le,
    ae_all_iff.mpr (actual_quadratic_response_compatible_ae d hn hμ T h12 h23)] with x hx hN hD
  have hV := coordinateHessian_posSemidef_of_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  exact response_fullSym_coarse (coordinateHessian d.potential x) (sourceTargetCurvature d x)
    (quadraticResponseMatrix d T x) hx.1 hP (sourceThirdMatrix d x)
    (fun i => responseRowJacobian d hn hμ T i x) T
    (fun i j k => (hN i j k).1) (fun i j k => (hN i j k).2) h12 h23 hD

theorem actual_response_fullSym_production_lower (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    4 * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) / 3 ≤
      (∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential) +
        ∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential := by
  have hXi := actualResponseXi_integrable d hn hμ T h12 h23 hC hM
  have hθ := actual_response_row_curvature_integrable d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM
  have hW := actual_direct_moment_integrable d T
  have hp : ∀ᵐ x ∂potentialMeasure d.potential,
      (4 / 3 : ℝ) * actualDirectMoment d T x ≤ actualResponseXi d hn hμ T x +
        actualRowCurvature d (quadraticResponseMatrix d T) x := by
    filter_upwards [actual_response_fullSym_production_lower_ae d hn hμ T h12 h23] with x hx
    linarith only [hx]
  have hi := integral_mono_ae (hW.const_mul (4 / 3 : ℝ)) (hXi.add hθ) hp
  rw [integral_const_mul] at hi
  change (4 / 3 : ℝ) * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) ≤
    ∫ x, actualResponseXi d hn hμ T x +
      actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential at hi
  rw [integral_add hXi hθ] at hi
  linarith only [hi]

theorem actual_response_matrix_upper_with_extra (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) / 3 +
        2 * (sourceMeanGram d T).trace - 2 * actualMatrixFilterCross d 1 T -
          ∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential := by
  have hs := actual_response_paid_production_state d hn hμ hiso T h12 h23 hC hM
  have hc := actual_response_fullSym_production_lower d hn hμ T h12 h23 hC hM
  linarith only [hs.2.1, hs.2.2, hc]

theorem actual_response_curvature_upper_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) ≤
      2 * (sourceMeanGram d T).trace +
        Real.sqrt ((sourceMeanGram d T).trace * (2 * tensorSquare T -
          ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
            (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential)) -
              ∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential := by
  have hs := actual_response_paid_production_state d hn hμ hiso T h12 h23 hC hM
  have hf := actual_fullSymmetric_base_filter_cross_half d hiso T h12 h23
  have hn := neg_le_abs (actualMatrixFilterCross d 1 T)
  linarith only [hs.2.1, hf, hn]

theorem actual_response_main_upper_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) ≤
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) / 3 +
        2 * (sourceMeanGram d T).trace +
          Real.sqrt ((sourceMeanGram d T).trace * (2 * tensorSquare T -
            ∫ x, rawHessianTraceSquare (coordinateHessian d.potential x)
              (CFC.sqrt (sourceCoefficientGram T)) ∂potentialMeasure d.potential)) -
                ∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential := by
  have hm := actual_response_matrix_upper_with_extra d hn hμ hiso T h12 h23 hC hM
  have hf := actual_fullSymmetric_base_filter_cross_half d hiso T h12 h23
  have hn := neg_le_abs (actualMatrixFilterCross d 1 T)
  linarith only [hm, hf, hn]

end KLSConstantImprovement.ActualResponseCoerciveUpper405

#print axioms KLSConstantImprovement.ActualResponseCoerciveUpper405.actual_response_fullSym_production_lower_ae
#print axioms KLSConstantImprovement.ActualResponseCoerciveUpper405.actual_response_fullSym_production_lower
#print axioms KLSConstantImprovement.ActualResponseCoerciveUpper405.actual_response_curvature_upper_of_mass_bound
#print axioms KLSConstantImprovement.ActualResponseCoerciveUpper405.actual_response_main_upper_of_mass_bound
