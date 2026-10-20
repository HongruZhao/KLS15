import KLSConstantImprovement.ActualConservativeResolventRawPair405
import KLSConstantImprovement.ActualResponseGramGlobalForm405

/-! Exact actual response production paired with K=R1H. The bounded raw
K test and the centered W_F form are independently constructed, and the
full conservative variational identity retains its mean correction. -/
noncomputable section
open MeasureTheory Matrix Filter Set InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualResponseResolventPair405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualHessianResolventRawTests405 ActualConservativeResolventRawPair405 ActualResponseGramGlobalForm405
open ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405 ActualQuadraticResponseGram405
open ActualSourceResponseProduction405 ActualSourceTensorGramMetricBinding
open ActualSourceMatrixResolvent405 ActualSourceLocalWeakCalculus405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_response_resolvent_entry_pair (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) :
    (∫ x, (2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
      actualResponseProduction d hn hμ T x i j) * sourceMatrixResolvent d (sourceHessianLp d) j i x
        ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x j i - sourceMatrixResolvent d (sourceHessianLp d) j i x) *
        quadraticResponseGram d T x i j ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let Kt := actualHessianResolventLocalTest d j i
  obtain ⟨V, hv, hd⟩ := exists_actual_response_gram_metricH1 d hn hμ T h12 h23 hC hM i j
  have hW : MemLp (fun x => quadraticResponseGram d T x i j) 2 (potentialMeasure d.potential) :=
    (actual_quadratic_response_gram_memLp_top_of_mass_bound d T
      (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM i j).mono_exponent (by simp)
  have hglobal := actual_response_gram_global_test d hn hμ T h12 h23 hC hM i j Kt
    (actualHessianResolventValue_memLp_top d j i) (actualHessianResolventLocalTest_metric_memLp d j i)
  have hvar := actual_hessian_resolvent_form_raw_pair d j i (fun x => quadraticResponseGram d T x i j) hW V hv
  have hEnergy : canonicalMetricEnergy d.potential (actualHessianResolventForm d j i) V =
      ∑ r, ∫ x, rawCanonicalMetricDerivative d.potential
        (quadraticResponseGramRawDerivative d hn hμ T i j) r x *
          rawCanonicalMetricDerivative d.potential Kt.derivative r x ∂potentialMeasure d.potential := by
    rw [canonicalMetricEnergy_apply]
    apply Finset.sum_congr rfl
    intro r _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd r, raw_metric_sourceWeakGradient_ae d (actualHessianResolventForm d j i) r] with x hx hk
    simp only [RCLike.inner_apply, conj_trivial]
    change _ = rawCanonicalMetricDerivative d.potential (quadraticResponseGramRawDerivative d hn hμ T i j) r x *
      rawCanonicalMetricDerivative d.potential (sourceWeakGradient d (actualHessianResolventForm d j i)) r x
    rw [hk, hx] <;> ring
  calc
    _ = ∫ x, (2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
        actualResponseProduction d hn hμ T x i j) * Kt.value x ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      filter_upwards [actualHessianResolventValue_ae d j i] with x hx
      exact congrArg (fun z : ℝ => (2 * sourceTensorGramEntry d.potential T i j x -
        quadraticResponseGram d T x i j - actualResponseProduction d hn hμ T x i j) * z) hx.symm
    _ = _ := hglobal.symm
    _ = canonicalMetricEnergy d.potential (actualHessianResolventForm d j i) V := hEnergy.symm
    _ = _ := hvar

end KLSConstantImprovement.ActualResponseResolventPair405

#print axioms KLSConstantImprovement.ActualResponseResolventPair405.actual_response_resolvent_entry_pair
