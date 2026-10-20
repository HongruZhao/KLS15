import KLSConstantImprovement.ActualResponseSquareDomains405
import KLSConstantImprovement.ActualResponseTargetDomain405
import KLSConstantImprovement.ActualSourceMeanGram405
import KLSConstantImprovement.ActualQuadraticResponseGram405

/-! Every entry of the literal positive response production is globally
L1 under the displayed actual quadratic mass bound. The two trace Grams
are controlled by the actual whitened L2 factors, and the target term by
the actual natural ordinary gradients. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseProductionDomain405
open KLS ActualBoundedCanonicalSource ActualResponseSquareDomains405 ActualResponseTargetDomain405
open ActualResponseCompletionWhitening405 ActualResponseProductionAlgebra405 ActualSourceResponseProduction405
open ActualQuadraticResponseField405 ActualQuadraticResponseGram405 ActualWhitenedWeakMatrixDomain405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405 ActualCanonicalMetricEnergyGraph
open ActualSourceTensorGramMetricBinding ActualSourceMeanGram405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem compatibleTraceGram_entry_integrable_of_white (d : SourceData μ)
    (A : Fin n → Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i a b, MemLp (fun x => sourceWhitenedJacobian d (A i) x a b) 2
      (potentialMeasure d.potential)) (i j : Fin n) :
    Integrable (fun x => (A i x * A j x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hp (a b : Fin n) : MemLp (fun x => (sourceWhitenedJacobian d (A i) x *
      sourceWhitenedJacobian d (A j) x) a b) 1 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := 2) (q := 2) (r := 1) (hA i) (hA j) a b
  apply ((memLp_matrix_trace_entries hp).integrable le_rfl).congr
  filter_upwards [d.hessian_ae_source] with x hx
  exact trace_product_similarity _ _ (A i x) (A j x) (canonicalMetricRoot_mul_unroot_at hx.1)

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h12 h23 hC hM in
theorem actualResponseProduction_entry_integrable (i j : Fin n) :
    Integrable (fun x => actualResponseProduction d hn hμ T x i j) (potentialMeasure d.potential) := by
  have hL := compatibleTraceGram_entry_integrable_of_white d (actualResponseLeftFactor d hn hμ T)
    (actualResponseLeftFactor_white_memLp d hn hμ T h12 h23 hC hM) i j
  have hR := compatibleTraceGram_entry_integrable_of_white d (actualResponseRightFactor d hn hμ T)
    (actualResponseRightFactor_white_memLp d hn hμ T h12 h23) i j
  exact ((actual_response_target_entry_integrable d T i j).add hL).add hR

include h12 h23 hC hM in
theorem actual_response_production_rhs_integrable (i j : Fin n) :
    Integrable (fun x => 2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
      actualResponseProduction d hn hμ T x i j) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hG : Integrable (sourceTensorGramEntry d.potential T i j) (potentialMeasure d.potential) :=
    (actual_traceGram_integrable d T i j).congr (Eventually.of_forall fun x => by
      change matrixTraceGram (coordinateHessian d.potential x) T i j = sourceTensorGramEntry d.potential T i j x
      rw [traceGram_cyclic, sourceTensorGramEntry_eq_trace])
  have hW := (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j).integrable (by simp)
  exact ((hG.const_mul 2).sub hW).sub (actualResponseProduction_entry_integrable d hn hμ T h12 h23 hC hM i j)

end Fixed
end KLSConstantImprovement.ActualResponseProductionDomain405

#print axioms KLSConstantImprovement.ActualResponseProductionDomain405.compatibleTraceGram_entry_integrable_of_white
#print axioms KLSConstantImprovement.ActualResponseProductionDomain405.actualResponseProduction_entry_integrable
#print axioms KLSConstantImprovement.ActualResponseProductionDomain405.actual_response_production_rhs_integrable
