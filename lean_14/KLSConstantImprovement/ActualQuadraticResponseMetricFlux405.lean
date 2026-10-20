import KLSConstantImprovement.ActualCompatibleGramFlux405
import KLSConstantImprovement.ActualQuadraticResponseGramLocal405
import KLSConstantImprovement.ActualQuadraticResponseAdjoint405
import KLSConstantImprovement.ActualSourceConnectionFields405

/-! The literal derivative of the actual response Gram has the compatible
metric flux. Compatibility is proved from the same chosen quadratic
Jacobian and the actual affine derivative; no derivative/PDE witness is
provided by the caller. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseMetricFlux405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualQuadraticResponseField405 ActualQuadraticResponseGramLocal405 ActualQuadraticResponseAdjoint405
open ActualSourceHessianEvolution405 ActualSourceConnectionFields405 ActualQuarticThirdWhitening405
open ActualCompatibleGramFlux405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def responseRowJacobian (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => quadraticResponseDerivative d hn hμ T i a b x

theorem full_tensor_affine_derivative (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i a b : Fin n) : mixFamily H T b i a = (T i * H) a b := by
  simp only [mixFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [h12 k i a, h23 i k a, hH.apply k b]; ring

theorem actual_quadratic_response_compatible_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (coordinateHessian d.potential x * responseRowJacobian d hn hμ T i x).IsSymm := by
  have hcomp := (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn
    (quadraticSourceDatum d (T i)) (quadraticSourceDatum_mean_zero d hμ (T i)))).2.2.2.1
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, hcomp.filter_mono hac.ae_le] with x hx hc
  let H := coordinateHessian d.potential x
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => quadraticFluxJacobian d hn hμ (T i) a b x
  have hH : H.IsSymm := hx.1.isHermitian.isSymm
  have hT : (T i).IsSymm := Matrix.IsSymm.ext fun a b => h23 i b a
  have hD : responseRowJacobian d hn hμ T i x = (2 : ℝ) • D - T i * H := by
    ext a b
    change 2 * quadraticFluxJacobian d hn hμ (T i) a b x - mixFamily H T b i a =
      2 * D a b - (T i * H) a b
    rw [full_tensor_affine_derivative H hH T h12 h23]
    rfl
  have hc' : (H * D).IsSymm := hc
  change (H * responseRowJacobian d hn hμ T i x).transpose = _
  rw [hD]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.transpose_sub, Matrix.transpose_smul]
  rw [hc'.eq]
  simp only [Matrix.transpose_mul, hH.eq, hT.eq, Matrix.mul_assoc]
  rfl

theorem actual_quadratic_response_metric_flux_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i j : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (fun a => ∑ r : Fin n, (coordinateHessian d.potential x)⁻¹ a r *
        quadraticResponseGramRawDerivative d hn hμ T i j r x) =
      responseRowJacobian d hn hμ T i x *ᵥ (fun b => quadraticResponseMatrix d T x j b) +
        responseRowJacobian d hn hμ T j x *ᵥ (fun b => quadraticResponseMatrix d T x i b) +
        ((coordinateHessian d.potential x)⁻¹ *
          sourceThirdAlong d (fun a y => quadraticResponseMatrix d T y i a) x) *ᵥ
            (fun b => quadraticResponseMatrix d T x j b) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le,
    actual_quadratic_response_compatible_ae d hn hμ T h12 h23 i,
    actual_quadratic_response_compatible_ae d hn hμ T h12 h23 j] with x hx hN hi hj
  have hJH : (coordinateHessian d.potential x)⁻¹ * coordinateHessian d.potential x = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have hNs (r a b : Fin n) : sourceThirdMatrix d x r a b = sourceThirdMatrix d x a r b := (hN r a b).1
  exact compatible_gram_metric_flux (coordinateHessian d.potential x) (coordinateHessian d.potential x)⁻¹
    (sourceThirdMatrix d x) hx.1.isHermitian.isSymm hJH hNs
    (fun a => quadraticResponseMatrix d T x i a) (fun a => quadraticResponseMatrix d T x j a)
    (responseRowJacobian d hn hμ T i x) (responseRowJacobian d hn hμ T j x) hi hj

end KLSConstantImprovement.ActualQuadraticResponseMetricFlux405

#print axioms KLSConstantImprovement.ActualQuadraticResponseMetricFlux405.actual_quadratic_response_compatible_ae
#print axioms KLSConstantImprovement.ActualQuadraticResponseMetricFlux405.actual_quadratic_response_metric_flux_ae
