import KLSConstantImprovement.ActualLocalDivergenceMetricEquation405
import KLSConstantImprovement.ActualResponseLocalEquations405

/-! Exact global weak Hessian testing against actual bounded finite-energy
raw functions. The L1 curvature is retained; AH is never asserted L2. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualHessianGlobalWeakTests405
open KLS ActualBoundedCanonicalSource ActualBoundedRawTestAlgebra405 ActualLocalBoundedWeakAlgebra405
open ActualResponseLocalEquations405 ActualSourceLocalDivergence405 ActualLocalDivergenceMetricEquation405
open ActualBoundedWeakGlobalForm405 ActualBoundedWeakGlobalTest405 ActualSourceCurvatureDomains405
open ActualSourceHessianEvolution405 ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_hessian_rawMetricWeakEquation (d : SourceData μ) (i j : Fin n) :
    RawMetricWeakEquation d (LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d i j))
      (fun x => coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) := by
  apply rawMetricWeakEquation_of_sourceLocalDivergence d (sourceHessianEntryEquation d i j)
  · have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
    filter_upwards [d.third_symmetric_ae.filter_mono hac.ae_le] with x hN
    funext a
    change (∑ r, (coordinateHessian d.potential x)⁻¹ a r * d.third x i r j) =
      ∑ r, (coordinateHessian d.potential x)⁻¹ a r * d.third x r i j
    exact Finset.sum_congr rfl fun r _ => by rw [(hN i r j).1]
  · exact EventuallyEq.rfl

theorem actual_hessian_global_raw_test (d : SourceData μ) (i j : Fin n) (g : LocalRawTest n)
    (hg : MemLp g.value ∞ (potentialMeasure d.potential))
    (hG : ∀ r, MemLp (rawCanonicalMetricDerivative d.potential g.derivative r) 2
      (potentialMeasure d.potential)) :
    (∑ r, ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
      rawCanonicalMetricDerivative d.potential g.derivative r x ∂potentialMeasure d.potential) =
        ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) * g.value x
          ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hb : Integrable (fun x => coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j)
      (potentialMeasure d.potential) :=
    ((d.hessian_entry_memLp i j ∞).integrable (by simp)).sub (actual_connection_curvature_entry_integrable d i j)
  exact bounded_weak_global_test d (LocalRawTest.ofBoundedRawTest (BoundedRawTest.hessian d i j)) g _ hb
    (BoundedRawTest.hessian d i j).value_top hg (actual_hessian_rawMetricWeakEquation d i j) hG

end KLSConstantImprovement.ActualHessianGlobalWeakTests405

#print axioms KLSConstantImprovement.ActualHessianGlobalWeakTests405.actual_hessian_rawMetricWeakEquation
#print axioms KLSConstantImprovement.ActualHessianGlobalWeakTests405.actual_hessian_global_raw_test
