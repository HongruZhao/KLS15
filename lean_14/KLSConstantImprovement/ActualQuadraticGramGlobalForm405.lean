import KLSConstantImprovement.ActualQuadraticGramCompactProduction405
import KLSConstantImprovement.ActualQuadraticProductionDomain405
import KLSConstantImprovement.ActualHessianGlobalWeakTests405

/-! Actual whole-row Gram global form and exact H entry testing.
Bounded weak Caccioppoli pays its energy from the constructed compact
production and the proved L1 domains, with no strong core claim. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticGramGlobalForm405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticGramCompactProduction405
open ActualQuadraticProductionDomain405 ActualQuadraticRowCurvature405 ActualQuadraticResponseField405
open ActualBoundedWeakGlobalForm405 ActualBoundedWeakGlobalTest405 ActualHessianGlobalWeakTests405
open ActualBoundedRawTestAlgebra405 ActualLocalBoundedWeakAlgebra405 ActualBoundedRawMetricDomain
open ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph ActualSourceHessianEvolution405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}
section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include hC hM in
theorem actual_quadratic_gram_metric_derivative_memLp (i j r : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential (quadraticGramRawDerivative d hn hμ T i j) r)
      2 (potentialMeasure d.potential) := by
  let f := quadraticGramLocalTest d hn hμ T hC hM i j
  have hf : MemLp f.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actualQuadraticGram_top_of_mass_bound d T hM i j)
  obtain ⟨B, hB, hb⟩ := memLp_top_ae_real_bound hf
  have he := bounded_weak_global_energy d f _
    (actualQuadraticProductionRHS_integrable d hn hμ T hC hM i j) hB hf hb
    (actual_quadratic_gram_rawMetricWeakEquation d hn hμ T hC hM i j)
  exact d.raw_metric_derivative_memLp_of_energy f.derivative_local he r

include hC hM in
theorem actual_quadratic_gram_global_test (i j : Fin n) (g : LocalRawTest n)
    (hg : MemLp g.value ∞ (potentialMeasure d.potential))
    (hG : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential g.derivative r) 2
      (potentialMeasure d.potential)) :
    (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential (quadraticGramRawDerivative d hn hμ T i j) r x *
      rawCanonicalMetricDerivative d.potential g.derivative r x ∂potentialMeasure d.potential) =
        ∫ x, actualQuadraticProductionRHS d hn hμ T i j x * g.value x ∂potentialMeasure d.potential := by
  let f := quadraticGramLocalTest d hn hμ T hC hM i j
  have hf : MemLp f.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actualQuadraticGram_top_of_mass_bound d T hM i j)
  exact bounded_weak_global_test d f g _ (actualQuadraticProductionRHS_integrable d hn hμ T hC hM i j)
    hf hg (actual_quadratic_gram_rawMetricWeakEquation d hn hμ T hC hM i j) hG

include hC hM in
theorem actual_quadratic_hessian_entry_pair (i j : Fin n) :
    (∫ x, actualQuadraticProductionRHS d hn hμ T i j x * coordinateHessian d.potential x j i
      ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x j i - sourceConnectionCurvature d x j i) *
        actualQuadraticGram d T x i j ∂potentialMeasure d.potential := by
  let Ht := LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d j i)
  let Wt := quadraticGramLocalTest d hn hμ T hC hM i j
  have hW : MemLp Wt.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actualQuadraticGram_top_of_mass_bound d T hM i j)
  have hl := actual_quadratic_gram_global_test d hn hμ T hC hM i j Ht
    (BoundedRawTest.hessian d j i).value_top (BoundedRawTest.hessian d j i).metric_gradient
  have hr := actual_hessian_global_raw_test d j i Wt hW
    (actual_quadratic_gram_metric_derivative_memLp d hn hμ T hC hM i j)
  simp only [Wt, quadraticGramLocalTest_derivative, quadraticGramLocalTest_value] at hr
  calc
    _ = ∑ r, ∫ x, rawCanonicalMetricDerivative d.potential (quadraticGramRawDerivative d hn hμ T i j) r x *
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a j i) r x ∂potentialMeasure d.potential := hl.symm
    _ = ∑ r, ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a j i) r x *
        rawCanonicalMetricDerivative d.potential (quadraticGramRawDerivative d hn hμ T i j) r x ∂potentialMeasure d.potential :=
      Finset.sum_congr rfl fun r _ => integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = _ := hr

include hC hM in
theorem actualQuadraticProductionXi_integrable :
    Integrable (actualQuadraticProductionXi d hn hμ T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm (i j : Fin n) : MemLp (fun x => coordinateHessian d.potential x i j *
      actualQuadraticProduction d hn hμ T x j i) 1 (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j ∞).mul (memLp_one_iff_integrable.mpr
      (actualQuadraticProduction_entry_integrable d hn hμ T hC hM j i))
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => (hm i j).integrable le_rfl

end Fixed
end KLSConstantImprovement.ActualQuadraticGramGlobalForm405

#print axioms KLSConstantImprovement.ActualQuadraticGramGlobalForm405.actual_quadratic_gram_metric_derivative_memLp
#print axioms KLSConstantImprovement.ActualQuadraticGramGlobalForm405.actual_quadratic_hessian_entry_pair
#print axioms KLSConstantImprovement.ActualQuadraticGramGlobalForm405.actualQuadraticProductionXi_integrable
