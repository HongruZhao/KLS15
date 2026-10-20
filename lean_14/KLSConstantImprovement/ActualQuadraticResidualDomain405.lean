import KLSConstantImprovement.ActualQuadraticProductionCompletion405
import KLSConstantImprovement.ActualQuadraticHessianFactorDomain405

/-! Genuine global domains for the two positive whole-row Hessian
squares. Both squares use the actual chosen quadratic inverse. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResidualDomain405
open KLS ActualBoundedCanonicalSource ActualQuadraticProductionCompletion405
open ActualQuadraticHessianFactorDomain405 ActualQuadraticGramProduction405
open ActualResponseProductionDomain405 ActualResponseSquareDomains405 ActualWhitenedWeakMatrixDomain405
open ActualQuadraticJacobianEnergy405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceQuadraticEta405 ActualCanonicalMetricEnergyGraph ActualSourceNaturalTargetCurvatureDomain405
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem hessian_weighted_trace_integrable (d : SourceData μ)
    (A : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, Integrable (fun x => A x i j) (potentialMeasure d.potential)) :
    Integrable (fun x => (coordinateHessian d.potential x * A x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j, coordinateHessian d.potential x i j * A x j i)
    (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => coordinateHessian d.potential x i j * A x j i) 1
      (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j ∞).mul (memLp_one_iff_integrable.mpr (hA j i))
  exact hm.integrable le_rfl

theorem actualQuadraticResidualFactor_white_memLp (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i a b : Fin n) :
    MemLp (fun x => sourceWhitenedJacobian d (actualQuadraticResidualFactor d hn hμ T i) x a b)
      2 (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have htop := actual_constant_hessian_congruence_memLp_top d (T i) a b
  have htwo : MemLp (fun x =>
      (canonicalMetricUnroot d.potential x * T i * canonicalMetricUnroot d.potential x) a b)
      2 (potentialMeasure d.potential) := htop.mono_exponent (by simp)
  have hm : MemLp (fun x =>
      sourceWhitenedJacobian d (actualQuadraticHessianFactor d hn hμ T i) x a b -
        (canonicalMetricUnroot d.potential x * T i * canonicalMetricUnroot d.potential x) a b)
      2 (potentialMeasure d.potential) :=
    (actualQuadraticHessianFactor_white_memLp d hn hμ T hC hM i a b).sub htwo
  apply (memLp_congr_ae ?_).mp hm
  filter_upwards [d.hessian_ae_source] with x hx
  change (canonicalMetricUnroot d.potential x * actualQuadraticHessianFactor d hn hμ T i x *
      canonicalMetricRoot d.potential x) a b -
    (canonicalMetricUnroot d.potential x * T i * canonicalMetricUnroot d.potential x) a b =
      (canonicalMetricUnroot d.potential x *
        (actualQuadraticHessianFactor d hn hμ T i x - T i * coordinateHessian d.potential x) *
          canonicalMetricRoot d.potential x) a b
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
  simp only [Matrix.mul_assoc,
    ActualSourceGradientCoefficientPassage405.hessian_mul_canonicalMetricRoot_at hx.1]

theorem actualQuadraticResidualCost_integrable (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    Integrable (actualQuadraticResidualCost d hn hμ T) (potentialMeasure d.potential) := by
  apply hessian_weighted_trace_integrable d
    (fun x => ActualResponseProductionAlgebra405.compatibleTraceGram
      (fun i => actualQuadraticResidualFactor d hn hμ T i x))
  exact compatibleTraceGram_entry_integrable_of_white d (actualQuadraticResidualFactor d hn hμ T)
    (actualQuadraticResidualFactor_white_memLp d hn hμ T hC hM)

theorem actualQuadraticJacobianRowCost_integrable (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualQuadraticJacobianRowCost d hn hμ T) (potentialMeasure d.potential) := by
  apply hessian_weighted_trace_integrable d
    (fun x => ActualResponseProductionAlgebra405.compatibleTraceGram
      (fun i => quadraticJacobianMatrix d hn hμ (T i) x))
  exact actual_quadratic_jacobian_gram_entry_integrable d hn hμ T

theorem actual_quadratic_jacobian_row_nonnegative_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualQuadraticJacobianRowCost d hn hμ T x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr fun i =>
    (quadraticFluxJacobian_compatible_volume_ae d hn hμ (T i)).filter_mono hac.ae_le] with x hx hD
  exact trace_mul_nonneg_of_posSemidef hx.1.posSemidef
    (ActualResponseProductionAlgebra405.compatibleTraceGram_posSemidef _ hx.1 _ hD)

end KLSConstantImprovement.ActualQuadraticResidualDomain405
#print axioms KLSConstantImprovement.ActualQuadraticResidualDomain405.actualQuadraticResidualFactor_white_memLp
#print axioms KLSConstantImprovement.ActualQuadraticResidualDomain405.actualQuadraticResidualCost_integrable
#print axioms KLSConstantImprovement.ActualQuadraticResidualDomain405.actualQuadraticJacobianRowCost_integrable
#print axioms KLSConstantImprovement.ActualQuadraticResidualDomain405.actual_quadratic_jacobian_row_nonnegative_ae
