import KLSConstantImprovement.ActualCanonicalConnectionAlgebra405
import KLSConstantImprovement.ActualSourceInverseGradientDomain405

/-!
The finite connection cancellation is bound to the actual source Hessian,
its actual weak third tensor, the actual inverse gradient and its genuine
ordered raw derivative. No classical third derivative is substituted for
the source's weak tensor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix Filter
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualSourceCanonicalConnectionBalance405
open KLS ActualBoundedCanonicalSource ActualSourceInverseTensor405
open ActualSourceInverseGradientDomain405 ActualCanonicalConnectionAlgebra405
variable {n : ℕ} {μ : Measure (Space n)}

def actualCanonicalSecondDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ((coordinateHessian d.potential x)⁻¹ * coordinateHessian ψ x *
    (coordinateHessian d.potential x)⁻¹ * coordinateHessian ψ x).trace

def actualCanonicalTargetDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  (fun i => coordinateDerivative ψ i x) ⬝ᵥ
    (coordinateHessian d.targetPotential (gradient d.potential x) *ᵥ
      (fun i => coordinateDerivative ψ i x))

def actualCanonicalPositiveDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  actualCanonicalSecondDensity d ψ x + actualCanonicalTargetDensity d ψ x

def actualCanonicalPrebochnerDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (coordinateHessian d.potential x i j * actualInverseGradient d ψ i x *
      actualInverseGradient d ψ j x +
        actualInverseGradientDerivative d ψ i j x * actualInverseGradientDerivative d ψ j i x)

def actualConnectionLeftDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k : Fin n, ∑ i : Fin n, ∑ a : Fin n, actualInverseTensor d k x a i *
    (actualInverseGradientDerivative d ψ k a x * coordinateDerivative ψ i x +
      actualInverseGradient d ψ k x * coordinateHessian ψ x a i)

def actualConnectionRightDensity (d : SourceData μ) (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ k : Fin n, ∑ i : Fin n,
    ((1 : Matrix (Fin n) (Fin n) ℝ) k i -
      (coordinateHessian d.potential x * coordinateHessian d.targetPotential
        (gradient d.potential x)) k i) *
      (actualInverseGradient d ψ k x * coordinateDerivative ψ i x)

/-- Actual AE balance before integration. The only source tensor used is
the genuine weak derivative already stored in SourceData. -/
theorem actual_compact_connection_balance_ae (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    (fun x => actualCanonicalPrebochnerDensity d ψ x + actualConnectionLeftDensity d ψ x) =ᵐ[
      potentialMeasure d.potential]
      (fun x => actualCanonicalPositiveDensity d ψ x + actualConnectionRightDensity d ψ x) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  have hHJ : coordinateHessian d.potential x * (coordinateHessian d.potential x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have he := finite_compact_connection_balance (coordinateHessian d.potential x)
    (coordinateHessian d.potential x)⁻¹ (coordinateHessian ψ x)
    (coordinateHessian d.targetPotential (gradient d.potential x)) hx.1.isHermitian.isSymm
    (coordinateHessian_symmetric hψ x) hHJ (fun k => Matrix.of (d.third x k))
    (by simpa only [Matrix.of_apply] using hN) (fun i => coordinateDerivative ψ i x)
  simpa only [actualCanonicalPrebochnerDensity, actualConnectionLeftDensity,
    actualCanonicalPositiveDensity, actualCanonicalSecondDensity, actualCanonicalTargetDensity,
    actualConnectionRightDensity, actualInverseGradient, actualInverseGradientDerivative,
    actualInverseTensor, inverseJacobian, Matrix.of_apply, Matrix.mulVec, dotProduct] using he

end KLSConstantImprovement.ActualSourceCanonicalConnectionBalance405

#print axioms KLSConstantImprovement.ActualSourceCanonicalConnectionBalance405.actual_compact_connection_balance_ae
