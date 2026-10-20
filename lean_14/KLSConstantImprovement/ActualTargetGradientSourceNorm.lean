import KLSConstantImprovement.ActualSourceVectorBochnerGlobalSquare
import KLSConstantImprovement.ActualTargetGradientSourceBinding

/-! Actual target-gradient source norm, including the noncompact limit.
The source potential and first-order L2 domains remain explicit. No
moment-map existence, optimizer, uniform variance budget or CP is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory KLS Filter
open scoped BigOperators ContDiff
namespace KLSConstantImprovement.ActualTargetGradientSourceNorm
open ActualCompactSourceVectorBochner ActualSourceVectorBochnerGlobalSquare
open ActualTargetGradientSourceBinding
variable {n : ℕ}

theorem target_gradient_pullback_contDiff {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hf : ContDiff ℝ 3 f) (i : Fin n) :
    ContDiff ℝ 2 (targetGradientPullback φ f i) :=
  (contDiff_coordinateDerivative hf (by norm_num) i).comp
    (contDiff_gradient hφ (by norm_num))

theorem integral_target_gradient_source_action_square {φ f : Space n → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hf : ContDiff ℝ 3 f)
    (ha2 : ∀ i, MemLp (targetGradientPullback φ f i) 2 (potentialMeasure φ))
    (hδa : ∀ i, MemLp (coordinateSourceAdjoint φ (targetGradientPullback φ f i) i)
      2 (potentialMeasure φ))
    (hDa : ∀ i j, MemLp (coordinateDerivative (targetGradientPullback φ f i) j)
      2 (potentialMeasure φ))
    {M : ℝ} (hM : 0 ≤ M) (hH : ∀ y i j, |coordinateHessian φ y i j| ≤ M) :
    (∫ y, ((∑ i : Fin n, coordinateDerivative φ i y*coordinateDerivative f i (gradient φ y))-
      ∑ i : Fin n, ∑ j : Fin n, coordinateHessian φ y i j*
        coordinateHessian f (gradient φ y) i j)^2 ∂potentialMeasure φ) =
    ∫ y, (∑ i : Fin n, ∑ j : Fin n,
      coordinateHessian φ y i j*coordinateDerivative f i (gradient φ y)*
        coordinateDerivative f j (gradient φ y))+
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        coordinateHessian f (gradient φ y) i k*coordinateHessian φ y k j*
          coordinateHessian f (gradient φ y) j l*coordinateHessian φ y l i
      ∂potentialMeasure φ := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hv := integral_source_vector_adjoint_square_of_L2_first_order hφ2
    (targetGradientPullback φ f) (target_gradient_pullback_contDiff hφ hf)
    ha2 hδa hDa hM hH
  calc
    _ = ∫ y, (sourceVectorAdjoint φ (targetGradientPullback φ f) y)^2
        ∂potentialMeasure φ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y =>
        congrArg (fun z : ℝ => z^2) (source_adjoint_target_gradient_action hφ2 hf2 y).symm
    _ = _ := by
      rw [hv]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [Finset.sum_add_distrib]
        rw [source_jacobian_trace_target_hessian_binding hφ2 hf2 y]
        rfl

end KLSConstantImprovement.ActualTargetGradientSourceNorm
#print axioms KLSConstantImprovement.ActualTargetGradientSourceNorm.target_gradient_pullback_contDiff
#print axioms KLSConstantImprovement.ActualTargetGradientSourceNorm.integral_target_gradient_source_action_square
