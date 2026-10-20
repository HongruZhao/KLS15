import KLSConstantImprovement.ActualResponseLocalEquations405
import KLSConstantImprovement.ActualGramProductionAssemblyAlgebra405
import KLSConstantImprovement.ActualSourceResponseProduction405

/-! Genuine compact weak response production on the constructed source.
The equation is assembled from the actual differentiated row equations
and actual weak H evolution, using their proved bounded-H1 products.
No production PDE, classical Hessian derivative, or global W domain is
an input. Natural quadratic mass remains explicitly displayed. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualResponseCompactProduction405
open KLS ActualBoundedCanonicalSource ActualSourceLocalDivergence405 ActualResponseLocalEquations405
open ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405
open ActualQuadraticResponseMetricFlux405 ActualQuadraticResponseRowEquation405
open ActualSourceResponseProduction405 ActualGramProductionAssemblyAlgebra405
open ActualSourceHessianEvolution405 ActualSourceConnectionFields405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceTensorGramMetricBinding
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

private theorem flux_fin3 {d : SourceData μ} (e : Fin 3 → SourceLocalDivergence d)
    (a : Fin n) (x : Space n) :
    (sourceLocalDivergenceSum e).flux a x =
      (e 0).flux a x + (e 1).flux a x + (e 2).flux a x := by
  simp [sourceLocalDivergenceSum, Fin.sum_univ_succ, add_assoc]

private theorem drift_fin3 {d : SourceData μ} (e : Fin 3 → SourceLocalDivergence d)
    (x : Space n) :
    (sourceLocalDivergenceSum e).drift x = (e 0).drift x + (e 1).drift x + (e 2).drift x := by
  simp [sourceLocalDivergenceSum, Fin.sum_univ_succ, add_assoc]

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

theorem responseAssembledEquation_flux_spec (i j r : Fin n) (x : Space n) :
    (responseAssembledEquation d hn hμ T h12 h23 hC hM i j).flux r x =
      (∑ a, quadraticResponseMatrix d T x j a * quadraticResponseDerivative d hn hμ T i r a x) +
      (∑ a, quadraticResponseMatrix d T x i a * quadraticResponseDerivative d hn hμ T j r a x) +
      (∑ a, ∑ b, (quadraticResponseMatrix d T x i a * quadraticResponseMatrix d T x j b) *
        ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b) := by
  unfold responseAssembledEquation
  rw [flux_fin3]
  rfl

theorem responseAssembledEquation_drift_spec (i j : Fin n) (x : Space n) :
    (responseAssembledEquation d hn hμ T h12 h23 hC hM i j).drift x =
      mixedRowDrift (coordinateHessian d.potential x)
        (responseRowJacobian d hn hμ T i x) (responseRowJacobian d hn hμ T j x)
        (fun a => actualTraceRawDerivative d T i a x)
        (quadraticResponseMatrix d T x i) (quadraticResponseMatrix d T x j) +
      mixedRowDrift (coordinateHessian d.potential x)
        (responseRowJacobian d hn hμ T j x) (responseRowJacobian d hn hμ T i x)
        (fun a => actualTraceRawDerivative d T j a x)
        (quadraticResponseMatrix d T x j) (quadraticResponseMatrix d T x i) +
      mixedHessianDrift (coordinateHessian d.potential x) (sourceConnectionCurvature d x)
        (fun a b r => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b)
        (responseRowJacobian d hn hμ T i x) (responseRowJacobian d hn hμ T j x)
        (quadraticResponseMatrix d T x i) (quadraticResponseMatrix d T x j) := by
  unfold responseAssembledEquation
  rw [drift_fin3]
  rfl

theorem responseAssembledEquation_drift_eq_raw_ae (i j : Fin n) :
    (responseAssembledEquation d hn hμ T h12 h23 hC hM i j).drift =ᵐ[potentialMeasure d.potential]
      actualResponseRawRHS d hn hμ T i j := by
  filter_upwards [d.hessian_ae_source] with x hx
  rw [responseAssembledEquation_drift_spec]
  rw [assembled_drift_expansion _ _ _ _ hx.1.isHermitian.isSymm]
  have hW : quadraticResponseMatrix d T x i ⬝ᵥ
      (coordinateHessian d.potential x *ᵥ quadraticResponseMatrix d T x j) = quadraticResponseGram d T x i j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, quadraticResponseGram,
      Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  have hS : quadraticResponseMatrix d T x i ⬝ᵥ
      (sourceConnectionCurvature d x *ᵥ quadraticResponseMatrix d T x j) = responseRawSourcePair d T i j x := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, responseRawSourcePair]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hQ : (responseRowJacobian d hn hμ T i x * responseRowJacobian d hn hμ T j x).trace =
      responseRawJacobianPair d hn hμ T i j x := rfl
  rw [hW, hS, hQ]
  rfl

theorem responseAssembledEquation_flux_eq_metric_ae (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => (responseAssembledEquation d hn hμ T h12 h23 hC hM i j).flux a x) =
        fun a => ∑ r, (coordinateHessian d.potential x)⁻¹ a r *
          quadraticResponseGramRawDerivative d hn hμ T i j r x := by
  filter_upwards [actual_quadratic_response_metric_flux_ae d hn hμ T h12 h23 i j] with x hx
  funext r
  rw [responseAssembledEquation_flux_spec, congrFun hx r]
  have hN : (∑ a, ∑ b, (quadraticResponseMatrix d T x i a * quadraticResponseMatrix d T x j b) *
      ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x a) r b) =
      (((coordinateHessian d.potential x)⁻¹ *
        sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x) *ᵥ
          quadraticResponseMatrix d T x j) r := by
    simp only [sourceThirdAlong, Matrix.mul_sum, Matrix.mul_smul, Matrix.mulVec, dotProduct,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hN]
  change (∑ a, quadraticResponseMatrix d T x j a * quadraticResponseDerivative d hn hμ T i r a x) +
      (∑ a, quadraticResponseMatrix d T x i a * quadraticResponseDerivative d hn hμ T j r a x) + _ =
      (∑ a, quadraticResponseDerivative d hn hμ T i r a x * quadraticResponseMatrix d T x j a) +
      (∑ a, quadraticResponseDerivative d hn hμ T j r a x * quadraticResponseMatrix d T x i a) + _
  congr 2 <;> exact Finset.sum_congr rfl fun a _ => mul_comm _ _

include h12 h23 hC hM in
theorem actual_response_gram_compact_production (i j : Fin n)
    {θ : Space n → ℝ} (hθ : ContDiff ℝ 3 θ) (hc : HasCompactSupport θ) :
    (∑ a : Fin n, ∫ x, (∑ r : Fin n, (coordinateHessian d.potential x)⁻¹ a r *
      quadraticResponseGramRawDerivative d hn hμ T i j r x) * coordinateDerivative θ a x
        ∂potentialMeasure d.potential) =
      ∫ x, (2 * sourceTensorGramEntry d.potential T i j x - quadraticResponseGram d T x i j -
        actualResponseProduction d hn hμ T x i j) * θ x ∂potentialMeasure d.potential := by
  let e := responseAssembledEquation d hn hμ T h12 h23 hC hM i j
  have hf := responseAssembledEquation_flux_eq_metric_ae d hn hμ T h12 h23 hC hM i j
  have hb := (responseAssembledEquation_drift_eq_raw_ae d hn hμ T h12 h23 hC hM i j).trans
    (actual_response_raw_production_binding_ae d hn hμ T i j)
  calc
    _ = ∑ a : Fin n, ∫ x, e.flux a x * coordinateDerivative θ a x ∂potentialMeasure d.potential :=
      Finset.sum_congr rfl fun a _ => integral_congr_ae (by
        filter_upwards [hf] with x hx
        exact congrArg (fun t : ℝ => t * coordinateDerivative θ a x) (congrFun hx a).symm)
    _ = ∫ x, e.drift x * θ x ∂potentialMeasure d.potential := e.identity θ hθ hc
    _ = _ := integral_congr_ae (hb.fun_mul EventuallyEq.rfl)

end Fixed
end KLSConstantImprovement.ActualResponseCompactProduction405

#print axioms KLSConstantImprovement.ActualResponseCompactProduction405.responseAssembledEquation_drift_eq_raw_ae
#print axioms KLSConstantImprovement.ActualResponseCompactProduction405.responseAssembledEquation_flux_eq_metric_ae
#print axioms KLSConstantImprovement.ActualResponseCompactProduction405.actual_response_gram_compact_production
