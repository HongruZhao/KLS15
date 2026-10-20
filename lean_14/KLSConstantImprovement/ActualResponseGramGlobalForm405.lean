import KLSConstantImprovement.ActualLocalDivergenceMetricEquation405
import KLSConstantImprovement.ActualResponseCompactProduction405
import KLSConstantImprovement.ActualResponseProductionDomain405

/-! The literal response Gram belongs to the actual natural global form.
Its compact equation is proved from the constructed rows and H evolution;
its global energy follows from bounded weak Caccioppoli and conservative
cutoffs. No strong operator core or graph approximation is used. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseGramGlobalForm405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualLocalBoundedWeakAlgebra405 ActualLocalDivergenceMetricEquation405
open ActualResponseCompactProduction405 ActualResponseLocalEquations405 ActualSourceResponseProduction405
open ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405 ActualQuadraticResponseGram405
open ActualResponseProductionDomain405 ActualSourceTensorGramMetricBinding
open ActualBoundedWeakGlobalForm405 ActualBoundedWeakGlobalTest405 ActualBoundedRawMetricDomain
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}
section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h12 h23 hC hM in
theorem actual_response_gram_rawMetricWeakEquation (i j : Fin n) :
    RawMetricWeakEquation d (quadraticResponseGramLocalTest d hn hμ T hC hM i j)
      (fun x => 2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
        actualResponseProduction d hn hμ T x i j) := by
  apply rawMetricWeakEquation_of_sourceLocalDivergence d
    (responseAssembledEquation d hn hμ T h12 h23 hC hM i j)
  · exact responseAssembledEquation_flux_eq_metric_ae d hn hμ T h12 h23 hC hM i j
  · exact (responseAssembledEquation_drift_eq_raw_ae d hn hμ T h12 h23 hC hM i j).trans
      (actual_response_raw_production_binding_ae d hn hμ T i j)

include h12 h23 hC hM in
theorem actual_response_gram_metric_derivative_memLp (i j r : Fin n) :
    MemLp (rawCanonicalMetricDerivative d.potential
      (quadraticResponseGramRawDerivative d hn hμ T i j) r) 2 (potentialMeasure d.potential) := by
  let f := quadraticResponseGramLocalTest d hn hμ T hC hM i j
  have hf : MemLp f.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
        (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j)
  obtain ⟨B, hB, hb⟩ := memLp_top_ae_real_bound hf
  have he := bounded_weak_global_energy d f _
    (actual_response_production_rhs_integrable d hn hμ T h12 h23 hC hM i j) hB hf hb
    (actual_response_gram_rawMetricWeakEquation d hn hμ T h12 h23 hC hM i j)
  exact d.raw_metric_derivative_memLp_of_energy f.derivative_local he r

include h12 h23 hC hM in
theorem exists_actual_response_gram_metricH1 (i j : Fin n) :
    ∃ V : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => quadraticResponseGram d T x i j - ∫ y, quadraticResponseGram d T y i j ∂potentialMeasure d.potential) ∧
      ∀ r, (canonicalMetricGradient d.potential r V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        rawCanonicalMetricDerivative d.potential (quadraticResponseGramRawDerivative d hn hμ T i j) r := by
  let f := quadraticResponseGramLocalTest d hn hμ T hC hM i j
  have hf : MemLp f.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
        (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j)
  obtain ⟨V, hv, hd⟩ := exists_bounded_weak_global_form d f _
    (actual_response_production_rhs_integrable d hn hμ T h12 h23 hC hM i j) hf
    (actual_response_gram_rawMetricWeakEquation d hn hμ T h12 h23 hC hM i j)
  refine ⟨V, ?_, hd⟩
  simpa only [f, quadraticResponseGramLocalTest_value] using hv

include h12 h23 hC hM in
theorem actual_response_gram_global_test (i j : Fin n) (g : LocalRawTest n)
    (hg : MemLp g.value ∞ (potentialMeasure d.potential))
    (hG : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential g.derivative r) 2
      (potentialMeasure d.potential)) :
    (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential
      (quadraticResponseGramRawDerivative d hn hμ T i j) r x *
        rawCanonicalMetricDerivative d.potential g.derivative r x ∂potentialMeasure d.potential) =
      ∫ x, (2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
        actualResponseProduction d hn hμ T x i j) * g.value x ∂potentialMeasure d.potential := by
  let f := quadraticResponseGramLocalTest d hn hμ T hC hM i j
  have hf : MemLp f.value ∞ (potentialMeasure d.potential) :=
    (memLp_congr_ae (Eventually.of_forall (quadraticResponseGramLocalTest_value d hn hμ T hC hM i j))).mpr
      (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
        (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j)
  exact bounded_weak_global_test d f g _
    (actual_response_production_rhs_integrable d hn hμ T h12 h23 hC hM i j) hf hg
    (actual_response_gram_rawMetricWeakEquation d hn hμ T h12 h23 hC hM i j) hG

end Fixed
end KLSConstantImprovement.ActualResponseGramGlobalForm405

#print axioms KLSConstantImprovement.ActualResponseGramGlobalForm405.actual_response_gram_rawMetricWeakEquation
#print axioms KLSConstantImprovement.ActualResponseGramGlobalForm405.actual_response_gram_metric_derivative_memLp
#print axioms KLSConstantImprovement.ActualResponseGramGlobalForm405.exists_actual_response_gram_metricH1
#print axioms KLSConstantImprovement.ActualResponseGramGlobalForm405.actual_response_gram_global_test
