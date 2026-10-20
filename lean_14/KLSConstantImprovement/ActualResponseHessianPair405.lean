import KLSConstantImprovement.ActualResponseGramGlobalForm405
import KLSConstantImprovement.ActualHessianGlobalWeakTests405
import KLSConstantImprovement.ActualQuadraticRowCurvature405

/-! Actual response production tested against the same source Hessian.
Both weak equations are genuine and both natural energy domains have
been paid. The positive production's H-weighted integral is globally L1. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseHessianPair405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualResponseGramGlobalForm405 ActualHessianGlobalWeakTests405 ActualResponseProductionDomain405
open ActualSourceResponseProduction405 ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405
open ActualQuadraticResponseGram405 ActualBoundedRawTestAlgebra405 ActualLocalBoundedWeakAlgebra405
open ActualSourceTensorGramMetricBinding ActualQuadraticRowCurvature405 ActualSourceHessianEvolution405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem integral_trace_mul {ν : Measure (Space n)}
    (A B : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hi : ∀ i j, Integrable (fun x => A x i j * B x j i) ν) :
    (∫ x, (A x * B x).trace ∂ν) = ∑ i, ∑ j, ∫ x, A x i j * B x j i ∂ν := by
  change (∫ x, ∑ i, ∑ j, A x i j * B x j i ∂ν) = _
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ fun j _ => hi i j

def actualResponseXi (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * actualResponseProduction d hn hμ T x).trace

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h12 h23 hC hM in
theorem actualResponseXi_integrable : Integrable (actualResponseXi d hn hμ T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm (i j : Fin n) : MemLp (fun x => coordinateHessian d.potential x i j *
      actualResponseProduction d hn hμ T x j i) 1 (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j ∞).mul (memLp_one_iff_integrable.mpr
      (actualResponseProduction_entry_integrable d hn hμ T h12 h23 hC hM j i))
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => (hm i j).integrable le_rfl

include h12 h23 hC hM in
theorem actual_response_hessian_entry_pair (i j : Fin n) :
    (∫ x, (2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
      actualResponseProduction d hn hμ T x i j) * coordinateHessian d.potential x j i
        ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x j i - sourceConnectionCurvature d x j i) *
        quadraticResponseGram d T x i j ∂potentialMeasure d.potential := by
  let Ht := LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d j i)
  let Wt := quadraticResponseGramLocalTest d hn hμ T hC hM i j
  have hW : MemLp Wt.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
        (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j)
  have hleft := actual_response_gram_global_test d hn hμ T h12 h23 hC hM i j Ht
    (BoundedRawTest.hessian d j i).value_top (BoundedRawTest.hessian d j i).metric_gradient
  have hright := actual_hessian_global_raw_test d j i Wt hW
    (actual_response_gram_metric_derivative_memLp d hn hμ T h12 h23 hC hM i j)
  simp only [Wt, quadraticResponseGramLocalTest_derivative, quadraticResponseGramLocalTest_value] at hright
  calc
    _ = ∑ r, ∫ x, rawCanonicalMetricDerivative d.potential
        (quadraticResponseGramRawDerivative d hn hμ T i j) r x *
          rawCanonicalMetricDerivative d.potential (fun a y => d.third y a j i) r x
            ∂potentialMeasure d.potential := hleft.symm
    _ = ∑ r, ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a j i) r x *
        rawCanonicalMetricDerivative d.potential (quadraticResponseGramRawDerivative d hn hμ T i j) r x
          ∂potentialMeasure d.potential :=
      Finset.sum_congr rfl fun r _ => integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = _ := hright

end Fixed
end KLSConstantImprovement.ActualResponseHessianPair405

#print axioms KLSConstantImprovement.ActualResponseHessianPair405.actualResponseXi_integrable
#print axioms KLSConstantImprovement.ActualResponseHessianPair405.actual_response_hessian_entry_pair
