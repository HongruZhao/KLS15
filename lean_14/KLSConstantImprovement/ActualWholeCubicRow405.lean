import KLSConstantImprovement.ActualQuadraticGlobalHBalance405
import KLSConstantImprovement.ActualQuadraticCompletedLoss405
import KLSConstantImprovement.ActualQuadraticRowEll405
import KLSConstantImprovement.JointRowMainCubicPayoff

/-! The whole-cubic ROW branch with genuine fields and domains. The
quadratic and cubic natural inverse mass gates remain displayed. All
production, adjoint, symmetry and variance pairings are constructed. -/
noncomputable section
open MeasureTheory Matrix Filter ProbabilityTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualWholeCubicRow405
open KLS ActualBoundedCanonicalSource ActualQuadraticGlobalHBalance405
open ActualQuadraticCompletedLoss405 ActualQuadraticGramProduction405 ActualQuadraticCyclicAdjoint405
open ActualQuadraticRowCurvature405 ActualQuadraticRowEll405 ActualQuadraticResponseField405
open ActualQuadraticHilbertMatrix405 ActualCubicHilbertUpper405 ActualCubicSourceDatum405 ActualCubicRepresenter
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceDirectCubicBalance405 ActualAffineTraceDiscount405 ActualAffineGlobalBalance405 ActualAffineMatrixTests405
open ActualAffineSourceIdentities405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem actual_whole_cubic_row_balance (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    2 * (∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
        (∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential) +
          2 * (∫ x, actualRowEll d T x ∂potentialMeasure d.potential) -
            ∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential := by
  have hH := actual_quadratic_global_H_balance d hn hμ T h12 h23 hC hM
  have hCyclic := actual_quadratic_integrated_production_completion d hn hμ T h12 h23 hC hM
  linarith only [hH, hCyclic]

theorem actual_row_ell_young_remainder_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ}
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    0 ≤ (3 / 4 : ℝ) * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      (4 / 3 : ℝ) * (∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential) -
        2 * (∫ x, actualRowEll d T x ∂potentialMeasure d.potential) := by
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hW := actual_affine_discount_bounds d T h12 h23
  have hθ : 0 ≤ ∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential :=
    integral_nonneg_of_ae (actual_row_curvature_nonnegative d _)
  have hy := JointRowMainCubicPayoff.row_ell_young_remainder (hW.1.trans hW.2) hθ
    (actualRowEll_integrated_square d T hTs hM)
  linarith only [hy]

theorem actual_whole_cubic_row_upper_of_mass_bounds (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {CQ CP : ℝ} (hCQ : 0 ≤ CQ) (hCP : 0 ≤ CP)
    (hMQ : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ CQ)
    (hMP : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (actualCubicDatum d T)) x ≤ CP) :
    variance (tensorPolynomial μ T) μ ≤
      42 * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
        21 * (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) +
          (63 / 2 : ℝ) * actualAffineDiscount d T -
            21 * (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) -
              18 * (∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential) := by
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hV := actual_cubic_variance_le_whole_matrix_of_mass_bound d hn hμ T h12 h23 hCP hMP
  have hRow := actual_whole_cubic_row_balance d hn hμ T h12 h23 hCQ hMQ
  have hEll := actual_row_ell_young_remainder_nonnegative d T h12 h23 hMQ
  have hSplit := actual_quadratic_row_curvature_split d T hTs hCQ hMQ
  have hAffine := actual_affine_row_curvature_identity d T hTs
  linarith only [hV, hRow, hEll, hSplit, hAffine]

end KLSConstantImprovement.ActualWholeCubicRow405
#print axioms KLSConstantImprovement.ActualWholeCubicRow405.actual_whole_cubic_row_balance
#print axioms KLSConstantImprovement.ActualWholeCubicRow405.actual_row_ell_young_remainder_nonnegative
#print axioms KLSConstantImprovement.ActualWholeCubicRow405.actual_whole_cubic_row_upper_of_mass_bounds
