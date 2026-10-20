import ActualGradedTensorOperators

/-! The actual isotropic constant integration is an isometry. Its range
projection is therefore a genuine orthogonal projection, a constraint that
is absent from arbitrary contractive-observation operator models. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLSBelow25.GradedHilbert
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ),
    κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hiso : IsIsotropic (potentialMeasure φ))

theorem gradedConstantIntegration_norm
    (f : GradedConstantTensorHilbert hφ) :
    ‖gradedConstantIntegration hφ hκ hlower hiso f‖=‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq,l2_norm_sq]
  apply tsum_congr
  intro r
  rw [gradedConstantIntegration_apply,constantTensorIntegration_norm hφ hκ hlower hiso]

theorem gradedConstantIntegration_adjoint_comp_self :
    (gradedConstantIntegration hφ hκ hlower hiso).adjoint.comp
      (gradedConstantIntegration hφ hκ hlower hiso)=1 :=
  (norm_map_iff_adjoint_comp_self _).mp
    (gradedConstantIntegration_norm hφ hκ hlower hiso)

def gradedLinearTensorProjection :
    GradedCenteredTensorHilbert hφ→L[ℝ]GradedCenteredTensorHilbert hφ :=
  (gradedConstantIntegration hφ hκ hlower hiso).comp
    (gradedConstantIntegration hφ hκ hlower hiso).adjoint

theorem gradedLinearTensorProjection_adjoint :
    (gradedLinearTensorProjection hφ hκ hlower hiso).adjoint=
      gradedLinearTensorProjection hφ hκ hlower hiso := by
  simp only [gradedLinearTensorProjection,adjoint_comp,adjoint_adjoint]

theorem gradedConstantIntegration_adjoint_projection
    (f : GradedCenteredTensorHilbert hφ) :
    (gradedConstantIntegration hφ hκ hlower hiso).adjoint
      (gradedLinearTensorProjection hφ hκ hlower hiso f)=
        (gradedConstantIntegration hφ hκ hlower hiso).adjoint f := by
  have h := congrArg (fun T => T ((gradedConstantIntegration hφ hκ hlower hiso).adjoint f))
    (gradedConstantIntegration_adjoint_comp_self hφ hκ hlower hiso)
  change (gradedConstantIntegration hφ hκ hlower hiso).adjoint
    (gradedConstantIntegration hφ hκ hlower hiso
      ((gradedConstantIntegration hφ hκ hlower hiso).adjoint f))=
      (gradedConstantIntegration hφ hκ hlower hiso).adjoint f at h
  exact h

theorem gradedLinearTensorProjection_idempotent
    (f : GradedCenteredTensorHilbert hφ) :
    gradedLinearTensorProjection hφ hκ hlower hiso
      (gradedLinearTensorProjection hφ hκ hlower hiso f)=
        gradedLinearTensorProjection hφ hκ hlower hiso f := by
  change gradedConstantIntegration hφ hκ hlower hiso
    ((gradedConstantIntegration hφ hκ hlower hiso).adjoint
      (gradedLinearTensorProjection hφ hκ hlower hiso f))=_
  rw [gradedConstantIntegration_adjoint_projection]
  rfl

theorem gradedLinearTensorProjection_norm
    (f : GradedCenteredTensorHilbert hφ) :
    ‖gradedLinearTensorProjection hφ hκ hlower hiso f‖=
      ‖(gradedConstantIntegration hφ hκ hlower hiso).adjoint f‖ :=
  gradedConstantIntegration_norm hφ hκ hlower hiso _

theorem gradedLinearTensorProjection_inner
    (f : GradedCenteredTensorHilbert hφ) :
    ⟪f,gradedLinearTensorProjection hφ hκ hlower hiso f⟫_ℝ=
      ‖gradedLinearTensorProjection hφ hκ hlower hiso f‖^2 := by
  change ⟪f,gradedConstantIntegration hφ hκ hlower hiso
      ((gradedConstantIntegration hφ hκ hlower hiso).adjoint f)⟫_ℝ=_
  rw [←adjoint_inner_left,real_inner_self_eq_norm_sq,gradedLinearTensorProjection_norm]

theorem gradedLinearTensorProjection_orthogonal_split
    (f : GradedCenteredTensorHilbert hφ) :
    ‖f‖^2=‖gradedLinearTensorProjection hφ hκ hlower hiso f‖^2+
      ‖f-gradedLinearTensorProjection hφ hκ hlower hiso f‖^2 := by
  rw [norm_sub_sq_real,gradedLinearTensorProjection_inner]
  ring

theorem actual_graded_observation_eq_projection (m : ℕ)
    (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hiso).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^m) f)‖^2=
    ‖gradedLinearTensorProjection hφ hκ hlower hiso
      (((gradedTensorIntegration hφ hκ hlower).adjoint^m) f)‖^2 := by
  rw [gradedLinearTensorProjection_norm]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.gradedConstantIntegration_adjoint_comp_self
#print axioms KLS.DeterministicBridgeIntegration.gradedLinearTensorProjection_idempotent
#print axioms KLS.DeterministicBridgeIntegration.gradedLinearTensorProjection_orthogonal_split
#print axioms KLS.DeterministicBridgeIntegration.actual_graded_observation_eq_projection
