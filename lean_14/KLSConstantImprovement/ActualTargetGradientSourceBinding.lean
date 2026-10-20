import KLSConstantImprovement.ActualCompactSourceVectorBochner

/-! Literal target gradients pulled back by the actual gradient map.
All derivatives and source adjoints below are concrete functions. C2
regularity suffices for the pointwise chain and weighted action bindings.
No moment-map existence, proper-map support, graph limit or cap is assumed. -/
noncomputable section
open KLS
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualTargetGradientSourceBinding
open ActualCompactSourceVectorBochner
variable {n : ℕ}

def targetGradientPullback (φ f : Space n → ℝ) (i : Fin n) (y : Space n) : ℝ :=
  coordinateDerivative f i (gradient φ y)

theorem coordinate_derivative_target_gradient_pullback {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (i j : Fin n) (y : Space n) :
    coordinateDerivative (targetGradientPullback φ f i) j y =
      ∑ k : Fin n, coordinateHessian f (gradient φ y) i k*coordinateHessian φ y k j := by
  have hfi : ContDiff ℝ 1 (coordinateDerivative f i) :=
    contDiff_coordinateDerivative hf (by norm_num) i
  have h := coordinateDerivative_comp_gradient (hfi.differentiable (by norm_num)) hφ j y
  change coordinateDerivative (targetGradientPullback φ f i) j y =
    ∑ k : Fin n, coordinateHessian f (gradient φ y) k i*coordinateHessian φ y j k at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  have hsφ := (coordinateHessian_symmetric hφ y).apply j k
  have hsf := (coordinateHessian_symmetric hf (gradient φ y)).apply i k
  rw [hsf, hsφ]

theorem source_adjoint_target_gradient_action {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (y : Space n) :
    sourceVectorAdjoint φ (targetGradientPullback φ f) y =
      (∑ i : Fin n, coordinateDerivative φ i y*coordinateDerivative f i (gradient φ y))-
        ∑ i : Fin n, ∑ j : Fin n,
          coordinateHessian φ y i j*coordinateHessian f (gradient φ y) i j := by
  unfold sourceVectorAdjoint coordinateSourceAdjoint
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinate_derivative_target_gradient_pullback hφ hf i i y]
  apply Finset.sum_congr rfl
  intro j _
  have hs := (coordinateHessian_symmetric hφ y).apply i j
  rw [hs]
  ring

theorem source_jacobian_trace_target_hessian_binding {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : ContDiff ℝ 2 f) (y : Space n) :
    (∑ i : Fin n, ∑ j : Fin n,
      coordinateDerivative (targetGradientPullback φ f i) j y*
        coordinateDerivative (targetGradientPullback φ f j) i y) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        coordinateHessian f (gradient φ y) i k*coordinateHessian φ y k j*
          coordinateHessian f (gradient φ y) j l*coordinateHessian φ y l i := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinate_derivative_target_gradient_pullback hφ hf i j y,
    coordinate_derivative_target_gradient_pullback hφ hf j i y,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end KLSConstantImprovement.ActualTargetGradientSourceBinding
#print axioms KLSConstantImprovement.ActualTargetGradientSourceBinding.coordinate_derivative_target_gradient_pullback
#print axioms KLSConstantImprovement.ActualTargetGradientSourceBinding.source_adjoint_target_gradient_action
#print axioms KLSConstantImprovement.ActualTargetGradientSourceBinding.source_jacobian_trace_target_hessian_binding
