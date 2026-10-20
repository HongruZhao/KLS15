import KLSConstantImprovement.ActualNaturalFluxAdjoint405
import KLSConstantImprovement.ActualTraceResponse405

/-! Literal source adjoint of F=2U-Z. Full tensor symmetry binds the
affine row Z_i=T_i X, so its actual adjoint cancels the constructed
quadratic forcing and leaves exactly tr(T_i(H-I)). No response PDE is
postulated and no quadratic mass bound is used in this identification. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticResponseAdjoint405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualNaturalFluxAdjoint405 ActualQuadraticResponseField405 ActualAffineMatrixTests405
open ActualCompactWeakSourceVectorSquare ActualCompactWeakSourceVectorBochner
open ActualQuarticThirdWhitening405 ActualTraceResponse405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

theorem full_tensor_affine_row (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (X : Fin n → ℝ) (i a : Fin n) :
    (∑ k, X k • T k) i a = (T i *ᵥ X) a := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [h12 k i a, h23 i k a]; ring

theorem actual_affine_row_adjoint_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i : Fin n) :
    rawWeakSourceVectorAdjoint d.potential (fun a x => actualAffineMatrix d T x i a)
      (fun a b x => mixFamily (coordinateHessian d.potential x) T b i a) =ᵐ[potentialMeasure d.potential]
      fun x => matrixQuadratic (T i) (gradient d.potential x) -
        (T i * coordinateHessian d.potential x).trace := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hX (a : Fin n) : actualAffineMatrix d T x i a =
      ∑ k, T i a k * gradient d.potential x k := full_tensor_affine_row T h12 h23 _ i a
  have hD (a : Fin n) : mixFamily (coordinateHessian d.potential x) T a i a =
      ∑ k, T i a k * coordinateHessian d.potential x k a := by
    simp only [mixFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => by
      rw [h12 k i a, h23 i k a, hx.1.isHermitian.isSymm.apply k a]
      ring
  simp only [rawWeakSourceVectorAdjoint, rawWeakSourceAdjoint, coordinateDerivative_eq_gradient,
    hX, hD, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, matrixQuadratic,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

theorem quadraticResponse_adjoint_two_sub (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) :
    rawWeakSourceVectorAdjoint d.potential (fun a y => quadraticResponseMatrix d T y i a)
      (fun a b => quadraticResponseDerivative d hn hμ T i a b) x =
      2 * rawWeakSourceVectorAdjoint d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i)))
        (quadraticFluxJacobian d hn hμ (T i)) x -
      rawWeakSourceVectorAdjoint d.potential (fun a y => actualAffineMatrix d T y i a)
        (fun a b y => mixFamily (coordinateHessian d.potential y) T b i a) x := by
  simp only [rawWeakSourceVectorAdjoint, rawWeakSourceAdjoint, quadraticResponseMatrix,
    quadraticResponseDerivative, Matrix.of_apply, quadraticRowFlux]
  calc
    _ = ∑ a : Fin n,
        (2 * (coordinateDerivative d.potential a x * naturalCanonicalFlux d (quadraticSourceDatum d (T i)) a x -
          quadraticFluxJacobian d hn hμ (T i) a a x) -
          (coordinateDerivative d.potential a x * actualAffineMatrix d T x i a -
            mixFamily (coordinateHessian d.potential x) T a i a)) :=
      Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem actual_quadratic_response_adjoint_eq_trace_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (i : Fin n) :
    rawWeakSourceVectorAdjoint d.potential (fun a x => quadraticResponseMatrix d T x i a)
      (fun a b => quadraticResponseDerivative d hn hμ T i a b) =ᵐ[potentialMeasure d.potential]
        actualTraceField d T i := by
  filter_upwards [quadratic_flux_jacobian_adjoint_eq_forcing_ae d hn hμ (T i),
    quadraticSourceDatum_ae d (T i), actual_affine_row_adjoint_ae d T h12 h23 i] with x hu hq hz
  rw [quadraticResponse_adjoint_two_sub, hu, hq, hz]
  simp only [ActualCubicGradientEnergy.centeredQuadratic, actualTraceField,
    Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one]
  ring

end KLSConstantImprovement.ActualQuadraticResponseAdjoint405

#print axioms KLSConstantImprovement.ActualQuadraticResponseAdjoint405.actual_affine_row_adjoint_ae
#print axioms KLSConstantImprovement.ActualQuadraticResponseAdjoint405.actual_quadratic_response_adjoint_eq_trace_ae
