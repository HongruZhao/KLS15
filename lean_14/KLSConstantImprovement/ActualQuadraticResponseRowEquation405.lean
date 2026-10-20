import KLSConstantImprovement.ActualWeakVectorRowEquation405
import KLSConstantImprovement.ActualQuadraticResponseAdjoint405

/-! The actual response rows satisfy the differentiated adjoint equation.
The forcing is the literal trace-response weak derivative, derived from
the source's genuine third tensor. No derivative of that tensor is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseRowEquation405
open KLS ActualBoundedCanonicalSource ActualQuadraticResponseField405 ActualTraceResponse405
open ActualQuadraticResponseAdjoint405 ActualWeakVectorRowEquation405
open ActualCompactWeakSourceVectorSquare ActualBoundedRawTestAlgebra405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def actualTraceRawDerivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i c : Fin n) (x : Space n) : ℝ :=
  ∑ a, ∑ b, T i a b * d.third x c b a

theorem actualTraceVector_hasLocalWeakDerivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i c : Fin n) :
    HasLocalWeakCoordinateDerivative (actualTraceVector d T i : Space n → ℝ)
      (actualTraceRawDerivative d T i c) c := by
  have he := (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_eq
    (actualTraceVector_coe d T i)
  have hv : (traceResponseTest d T i).value =ᵐ[(volume : Measure (Space n))] actualTraceField d T i :=
    Eventually.of_forall (traceResponseTest_value d T i)
  exact ((traceResponseTest d T i).weak_derivative c).congr_ae
    (hv.trans he.symm)
    (Eventually.of_forall (traceResponseTest_derivative d T i c))

theorem actual_quadratic_response_differentiated_compact_equation (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a : Fin n) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) (hc : HasCompactSupport ψ) :
    (∑ r : Fin n, ∫ x, quadraticResponseDerivative d hn hμ T i r a x * coordinateDerivative ψ r x
      ∂potentialMeasure d.potential) +
      (∑ r : Fin n, ∫ x, coordinateHessian d.potential x r a * quadraticResponseMatrix d T x i r * ψ x
        ∂potentialMeasure d.potential) =
      ∫ x, actualTraceRawDerivative d T i a x * ψ x ∂potentialMeasure d.potential := by
  have hdom := quadratic_response_local_weak_domains d hn hμ T
  have hadj : rawWeakSourceVectorAdjoint d.potential (fun r x => quadraticResponseMatrix d T x i r)
      (fun r a => quadraticResponseDerivative d hn hμ T i r a) =ᵐ[potentialMeasure d.potential]
        (actualTraceVector d T i : Space n → ℝ) :=
    (actual_quadratic_response_adjoint_eq_trace_ae d hn hμ T h12 h23 i).trans
      (actualTraceVector_coe d T i).symm
  exact raw_vector_differentiated_compact_equation d (actualTraceVector d T i)
    (fun r x => quadraticResponseMatrix d T x i r)
    (fun r a => quadraticResponseDerivative d hn hμ T i r a)
    (hdom.1 i) (hdom.2.1 i) (hdom.2.2 i) hadj
    (actualTraceVector_hasLocalWeakDerivative d T i a) hψ hc

end KLSConstantImprovement.ActualQuadraticResponseRowEquation405

#print axioms KLSConstantImprovement.ActualQuadraticResponseRowEquation405.actualTraceVector_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualQuadraticResponseRowEquation405.actual_quadratic_response_differentiated_compact_equation
