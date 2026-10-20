import ActualProjectionOrbitSlack
import ProjectionSharedResourceSlack
import ActualIndividualObservationCaps

/-! The shared-resource weighted projection slack and conditional observation payment
for the actual inverse-gradient operator. Projection geometry, comparison,
and the quadratic observation cap are all proved internally. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25 KLSBelow25.ProjectionOrbitSlack KLS.DeterministicBridgeNext
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ),
    κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_projection_variance_normalized_le_shared_weighted_slacks
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {weight : ℝ} (hweight : 0<weight) (hweight1 : weight<1) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    (‖P v‖^2-(‖P v‖^2)^2/‖v‖^2)/‖v‖^2≤
      ((‖R‖^2+1)/weight+‖R‖^2/(1-weight))*
        (weight*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
         (1-weight)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2)) :=
  projection_variance_normalized_le_shared_weighted_slacks
    (gradedTensorIntegration hφ hκ hlower)
    (gradedLinearTensorProjection hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_adjoint hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_inner hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_norm_le hφ hκ hlower hμ.isotropic)
    (actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic)
    u v w hv hw hupos hvpos hwpos hweight hweight1

theorem actual_projection_observation_shared_weighted_payment
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    {weight η K l : ℝ} (hweight : 0<weight) (hweight1 : weight<1) (hKl : 0<K*l)
    (hl : K*l*‖u‖^2≤‖v‖^2)
    (hcoefficient : η*((‖gradedTensorIntegration hφ hκ hlower‖^2+1)/weight+
      ‖gradedTensorIntegration hφ hκ hlower‖^2/(1-weight))≤1-2/(K*l)) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    η*(‖P v‖^2/‖v‖^2)≤
      weight*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
      (1-weight)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2) := by
  have hobs := actual_first_graded_observation_sq_le hφ hκ hlower hμ u
  simp only [pow_one] at hobs
  rw [←hv,←gradedLinearTensorProjection_norm hφ hκ hlower hμ.isotropic] at hobs
  have hcap : ‖gradedLinearTensorProjection hφ hκ hlower hμ.isotropic v‖^2≤
      (2/(K*l))*‖v‖^2 := by
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0≤2/(K*l))
    have he : (2/(K*l))*(K*l*‖u‖^2)=2*‖u‖^2 := by
      calc
        _=((2/(K*l))*(K*l))*‖u‖^2 := by ring
        _=2*‖u‖^2 := by rw [div_mul_cancel₀ _ hKl.ne']
    rw [he] at hh
    exact hobs.trans hh
  exact projection_observation_le_shared_weighted_slack_payment
    (gradedTensorIntegration hφ hκ hlower)
    (gradedLinearTensorProjection hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_adjoint hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_inner hφ hκ hlower hμ.isotropic)
    (gradedLinearTensorProjection_norm_le hφ hκ hlower hμ.isotropic)
    (actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic)
    u v w hv hw hupos hvpos hwpos hweight hweight1 hcap hcoefficient

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_variance_normalized_le_shared_weighted_slacks
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_observation_shared_weighted_payment
