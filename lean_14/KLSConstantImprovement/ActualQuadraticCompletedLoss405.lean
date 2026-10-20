import KLSConstantImprovement.ActualQuadraticResidualDomain405
import KLSConstantImprovement.ActualQuadraticProductionDomain405

/-! Integrated positive whole-row loss on the actual source. All
domains and the cyclic adjoint are discharged from the displayed
quadratic inverse mass bound. No production PDE is assumed here. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuadraticCompletedLoss405
open KLS ActualBoundedCanonicalSource ActualQuadraticResidualDomain405
open ActualQuadraticProductionCompletion405 ActualQuadraticProductionDomain405
open ActualQuadraticGramProduction405 ActualQuadraticCyclicAdjoint405
open ActualQuadraticRowEll405 ActualQuadraticHilbertMatrix405 ActualSourceDirectCubicBalance405
open ActualQuadraticResponseField405 ActualSourceCurvatureDomains405
open ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405 ActualSourceQuadraticEta405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def actualQuadraticRowLoss (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  actualQuadraticTargetRowCost d T x + actualQuadraticResidualCost d hn hμ T x +
    actualQuadraticJacobianRowCost d hn hμ T x

theorem actualQuadraticTargetRowCost_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualQuadraticTargetRowCost d T) (potentialMeasure d.potential) :=
  hessian_weighted_trace_integrable d _ (actual_quadratic_target_entry_integrable d T)

theorem actual_quadratic_target_row_nonnegative_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualQuadraticTargetRowCost d T x := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hV := coordinateHessian_posSemidef_of_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  have hUP : (actualQuadraticFluxMatrix d T x * sourceTargetCurvature d x *
      (actualQuadraticFluxMatrix d T x).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same (actualQuadraticFluxMatrix d T x).transpose
  exact trace_mul_nonneg_of_posSemidef hx.1.posSemidef hUP

theorem actual_quadratic_row_loss_nonnegative_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualQuadraticRowLoss d hn hμ T x := by
  filter_upwards [actual_quadratic_target_row_nonnegative_ae d T,
    actual_quadratic_residual_nonnegative_ae d hn hμ T hT,
    actual_quadratic_jacobian_row_nonnegative_ae d hn hμ T] with x hp hr hd
  exact add_nonneg (add_nonneg hp hr) hd

theorem actualQuadraticRowLoss_integrable (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    Integrable (actualQuadraticRowLoss d hn hμ T) (potentialMeasure d.potential) :=
  ((actualQuadraticTargetRowCost_integrable d T).add
    (actualQuadraticResidualCost_integrable d hn hμ T hC hM)).add
      (actualQuadraticJacobianRowCost_integrable d hn hμ T)

theorem actualQuadraticProductionXi_integrable (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    Integrable (actualQuadraticProductionXi d hn hμ T) (potentialMeasure d.potential) :=
  hessian_weighted_trace_integrable d _ (actualQuadraticProduction_entry_integrable d hn hμ T hC hM)

theorem actual_quadratic_integrated_production_completion (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    (∫ x, actualQuadraticProductionXi d hn hμ T x ∂potentialMeasure d.potential) =
      (∫ x, actualQuadraticRowLoss d hn hμ T x ∂potentialMeasure d.potential) +
        2 * (∫ x, actualQuadraticAffineCrossCost d T x ∂potentialMeasure d.potential) -
          2 * (∫ x, actualRowEll d T x ∂potentialMeasure d.potential) -
            ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  obtain ⟨hpair, _, hcyclic⟩ := actual_quadratic_cyclic_adjoint d hn hμ T h12 h23 hC hM
  have hloss := actualQuadraticRowLoss_integrable d hn hμ T hC hM
  have hW := actual_direct_moment_integrable d T
  have he : actualQuadraticProductionXi d hn hμ T =ᵐ[potentialMeasure d.potential]
      fun x => actualQuadraticRowLoss d hn hμ T x + 2 * actualQuadraticHessianPair d hn hμ T x -
        actualDirectMoment d T x := by
    filter_upwards [actual_quadratic_production_completion_ae d hn hμ T] with x hx
    exact hx
  have h2 : Integrable (fun x => 2 * actualQuadraticHessianPair d hn hμ T x)
      (potentialMeasure d.potential) := hpair.const_mul 2
  have hs : Integrable (fun x => actualQuadraticRowLoss d hn hμ T x +
      2 * actualQuadraticHessianPair d hn hμ T x) (potentialMeasure d.potential) := hloss.add h2
  have hsub := integral_sub hs hW
  have hadd := integral_add hloss h2
  have hmul : (∫ x, 2 * actualQuadraticHessianPair d hn hμ T x ∂potentialMeasure d.potential) =
      2 * ∫ x, actualQuadraticHessianPair d hn hμ T x ∂potentialMeasure d.potential := integral_const_mul _ _
  rw [integral_congr_ae he]
  linarith only [hsub, hadd, hmul, hcyclic]

end KLSConstantImprovement.ActualQuadraticCompletedLoss405
#print axioms KLSConstantImprovement.ActualQuadraticCompletedLoss405.actual_quadratic_row_loss_nonnegative_ae
#print axioms KLSConstantImprovement.ActualQuadraticCompletedLoss405.actualQuadraticRowLoss_integrable
#print axioms KLSConstantImprovement.ActualQuadraticCompletedLoss405.actualQuadraticProductionXi_integrable
#print axioms KLSConstantImprovement.ActualQuadraticCompletedLoss405.actual_quadratic_integrated_production_completion
