import ActualProjectionSharedResourceSlack
import ActualSeed239ExpandedOperatorNormBound
import ProjectionExpandedProfileNumerics
import ActualProjectionOrbitSlack
import ActualIndividualObservationCaps

/-! The shared-resource weighted projection slack and conditional observation payment
for the actual inverse-gradient operator. Projection geometry, comparison,
and the quadratic observation cap are all proved internally. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25 KLSBelow25.ProjectionOrbitSlack KLS.DeterministicBridgeNext
open KLSBelow25.ProjectionExpandedProfileNumerics
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ),
    κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_projection_seed239_expanded_shared_resource_conditional_payment
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2) (hwpos : 0<‖w‖^2)
    (hl : K*floorFactor*‖u‖^2≤‖v‖^2) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    eta*(‖P v‖^2/‖v‖^2)≤
      weight*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
      (1-weight)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2) := by
  have hnorm : ‖gradedTensorIntegration hφ hκ hlower‖^2 ≤ normSqUpper :=
    by
      simpa only [normSqUpper,K,KLSBelow25.CoupledEnergy.NumericsSeed239Expanded.K,
        KLSBelow25.CoupledEnergy.NumericsSeed239Expanded.p] using
          actual_seed239_expanded_graded_operator_norm_sq_le hφ hκ hlower hμ
  have hw0 : 0 < weight := by norm_num [weight]
  have hw1 : weight < 1 := by norm_num [weight]
  have hmono1 : (‖gradedTensorIntegration hφ hκ hlower‖^2+1)/weight ≤
      (normSqUpper+1)/weight :=
    div_le_div_of_nonneg_right (by linarith) hw0.le
  have hmono2 : ‖gradedTensorIntegration hφ hκ hlower‖^2/(1-weight) ≤
      normSqUpper/(1-weight) :=
    div_le_div_of_nonneg_right hnorm (sub_pos.mpr hw1).le
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hcert⟩ := finite_anchor_parameters
  have hcoeff : eta*((‖gradedTensorIntegration hφ hκ hlower‖^2+1)/weight+
      ‖gradedTensorIntegration hφ hκ hlower‖^2/(1-weight)) ≤ 1-2/(K*floorFactor) :=
    (mul_le_mul_of_nonneg_left (add_le_add hmono1 hmono2)
      (by norm_num [eta] : 0 ≤ eta)).trans hcert
  exact actual_projection_observation_shared_weighted_payment hφ hκ hlower hμ
    u v w hv hw hupos hvpos hwpos hw0 hw1 (by norm_num [K,floorFactor]) hl hcoeff

include hμ in
theorem actual_projection_seed239_expanded_shared_resource_successor_norm_sq_pos
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hl : K*floorFactor*‖u‖^2≤‖v‖^2) :
    0<‖w‖^2 := by
  let R := gradedTensorIntegration hφ hκ hlower
  let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
  have hinner := gradedLinearTensorProjection_inner hφ hκ hlower hμ.isotropic
  have hcomp := actual_graded_linear_projection_comparison hφ hκ hlower hμ.isotropic
  have hh := cauchy_comparison_slack_identity R P u v w hupos hv hw
  change ‖w‖^2+⟪v,P v⟫_ℝ-‖v‖^4/‖u‖^2=
    ‖R v-(‖v‖^2/‖u‖^2)•u‖^2+⟪v,defect R P v⟫_ℝ at hh
  have hd : 0≤⟪v,defect R P v⟫_ℝ := by
    rw [defect_quadratic R P hinner]
    exact sub_nonneg.mpr (hcomp v)
  have hquot : ‖v‖^4/‖u‖^2≤‖w‖^2+‖P v‖^2 := by
    rw [hinner] at hh
    nlinarith [sq_nonneg ‖R v-(‖v‖^2/‖u‖^2)•u‖]
  have hsq := (div_le_iff₀ hupos).1 hquot
  have hobs := actual_first_graded_observation_sq_le hφ hκ hlower hμ u
  simp only [pow_one] at hobs
  rw [←hv,←gradedLinearTensorProjection_norm hφ hκ hlower hμ.isotropic] at hobs
  change ‖P v‖^2≤2*‖u‖^2 at hobs
  have hKl : (2:ℝ)≤K*floorFactor := by norm_num [K,floorFactor]
  have hlo2 : 2*‖u‖^2≤‖v‖^2 :=
    (mul_le_mul_of_nonneg_right hKl hupos.le).trans hl
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*‖u‖^2) hlo2 2
  have hu4 : 0<(‖u‖^2)^2 := sq_pos_of_pos hupos
  by_contra hn
  have hw0 : ‖w‖^2≤0 := le_of_not_gt hn
  nlinarith [mul_le_mul_of_nonneg_right hobs hupos.le]

theorem actual_projection_seed239_expanded_shared_resource_conditional_payment_positive
    (u v w : GradedCenteredTensorHilbert hφ)
    (hv : v=(gradedTensorIntegration hφ hκ hlower).adjoint u)
    (hw : w=(gradedTensorIntegration hφ hκ hlower).adjoint v)
    (hupos : 0<‖u‖^2) (hvpos : 0<‖v‖^2)
    (hl : K*floorFactor*‖u‖^2≤‖v‖^2) :
    let R := gradedTensorIntegration hφ hκ hlower
    let P := gradedLinearTensorProjection hφ hκ hlower hμ.isotropic
    eta*(‖P v‖^2/‖v‖^2)≤
      weight*((‖w‖^2+‖P v‖^2-‖v‖^4/‖u‖^2)/‖v‖^2)+
      (1-weight)*((‖R.adjoint w‖^2+‖P w‖^2-‖w‖^4/‖v‖^2)/‖w‖^2) :=
  actual_projection_seed239_expanded_shared_resource_conditional_payment hφ hκ hlower hμ
    u v w hv hw hupos hvpos
    (actual_projection_seed239_expanded_shared_resource_successor_norm_sq_pos hφ hκ hlower hμ u v w hv hw hupos hl) hl

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_seed239_expanded_shared_resource_conditional_payment

#print axioms KLS.DeterministicBridgeIntegration.actual_projection_seed239_expanded_shared_resource_successor_norm_sq_pos
#print axioms KLS.DeterministicBridgeIntegration.actual_projection_seed239_expanded_shared_resource_conditional_payment_positive
