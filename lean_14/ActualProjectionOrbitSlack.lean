import ActualConstantIntegrationProjection
import ProjectionOrbitSlackEstimate
import ActualTensorCurvatureComparison

/-! Actual-law projection variance forces consecutive orbit slack.
All projection and comparison hypotheses of the generic estimate are
proved for the literal graded inverse-gradient operators here. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25 KLSBelow25.ProjectionOrbitSlack KLS.DeterministicBridgeNext
open KLSBelow25.RealHilbertComplexification
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ),
    κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hiso : IsIsotropic (potentialMeasure φ))

theorem gradedLinearTensorProjection_norm_le
    (f : GradedCenteredTensorHilbert hφ) :
    ‖gradedLinearTensorProjection hφ hκ hlower hiso f‖≤‖f‖ := by
  rw [gradedLinearTensorProjection_norm]
  have hh := (gradedConstantIntegration hφ hκ hlower hiso).adjoint.le_opNorm f
  rw [adjoint.norm_map] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (gradedConstantIntegration_norm_le_one hφ hκ hlower hiso) (norm_nonneg f)).trans_eq
      (one_mul ‖f‖))

theorem actual_graded_linear_projection_comparison
    (f : GradedCenteredTensorHilbert hφ) :
    ‖gradedTensorIntegration hφ hκ hlower f‖^2≤
      ‖(gradedTensorIntegration hφ hκ hlower).adjoint f‖^2+
      ‖gradedLinearTensorProjection hφ hκ hlower hiso f‖^2 := by
  let R := gradedTensorIntegration hφ hκ hlower
  let L := gradedConstantIntegration hφ hκ hlower hiso
  have hc := rationalIntegrationComparison_extend R L hκ.le
    (actual_graded_rational_comparison hφ hκ hlower hiso
      (actual_tensor_curvature_comparison hφ hκ hlower))
  have hh := linear_curvature_comparison_of_resolvent (extend R) (extend L)
    (canonicalIntegrationResolvent (extend R) (extend L) κ) hκ
    (canonicalIntegrationResolvent_inverse (extend R) (extend L) hκ.le) hc
      (⟨f,0⟩ : RealHilbertComplexification (GradedCenteredTensorHilbert hφ))
  simp only [←extend_adjoint,norm_sq,extend_re,extend_im,map_zero,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),add_zero] at hh
  simpa only [R,L,gradedLinearTensorProjection_norm] using hh

theorem actual_projection_orbit_variance_le_consecutive_slacks
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) :
    ‖gradedLinearTensorProjection hφ hκ hlower hiso v‖^2-
      (‖gradedLinearTensorProjection hφ hκ hlower hiso v‖^2)^2/‖v‖^2≤
    (2*‖gradedTensorIntegration hφ hκ hlower‖^2+2)*
      ((‖w‖^2+‖gradedLinearTensorProjection hφ hκ hlower hiso v‖^2-‖v‖^4/‖u‖^2)+
       (‖(gradedTensorIntegration hφ hκ hlower).adjoint w‖^2+
        ‖gradedLinearTensorProjection hφ hκ hlower hiso w‖^2-‖w‖^4/‖v‖^2)) :=
  projection_variance_le_consecutive_slacks
    (gradedTensorIntegration hφ hκ hlower) (gradedLinearTensorProjection hφ hκ hlower hiso)
    (gradedLinearTensorProjection_adjoint hφ hκ hlower hiso)
    (gradedLinearTensorProjection_inner hφ hκ hlower hiso)
    (gradedLinearTensorProjection_norm_le hφ hκ hlower hiso)
    (actual_graded_linear_projection_comparison hφ hκ hlower hiso)
    u v w hv hw hupos hvpos

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_linear_projection_comparison
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_orbit_variance_le_consecutive_slacks
