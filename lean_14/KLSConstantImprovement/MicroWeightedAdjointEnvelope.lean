import KLSConstantImprovement.MicroWeightedProfile
import KLSConstantImprovement.ParameterizedWeightedEndpoint

/-! Exports the already verified actual joint observation budget and its
all-rate adjoint-power envelope for the finite projection anchor assembly. -/
noncomputable section
open MeasureTheory Matrix Set InnerProductSpace ContinuousLinearMap
open scoped ContDiff ENNReal BigOperators
namespace KLSConstantImprovement.MicroWeightedAdjointEnvelope
open KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration KLSBelow25.RealHilbertComplexification
open KLSBelow25.CoupledEnergy KLSConstantImprovement.MicroWeightedProfileData
set_option maxHeartbeats 110000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 600000
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (a : Fin n→ℝ), κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem K_positive : 0<K := by norm_num [K]

theorem actual_micro_joint_observation_budget :
    jointObservationBudget (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic) K C :=
  KLSConstantImprovement.ParameterizedWeightedEndpoint.actual_joint_observation_budget
    hφ hκ hlower hμ KLSConstantImprovement.MicroWeightedProfileData.profile
    KLSConstantImprovement.MicroWeightedProfile.scalar_certificate

include hμ in
theorem actual_micro_adjoint_power_envelope :
    ∀ rho : ℝ, 1 < rho → ∃ M : ℝ, ∀ m,
      ‖(gradedTensorIntegration hφ hκ hlower).adjoint^m‖^2 ≤ M*(K*rho)^m := by
  let R := gradedTensorIntegration hφ hκ hlower
  let L := gradedConstantIntegration hφ hκ hlower hμ.isotropic
  have hbudget := actual_micro_joint_observation_budget hφ hκ hlower hμ
  change jointObservationBudget R L K C at hbudget
  rcases subsingleton_or_nontrivial (RealHilbertComplexification (GradedCenteredTensorHilbert hφ)) with hsub | hn
  · intro rho hrho
    refine ⟨0,fun m => ?_⟩
    have he : (KLSBelow25.RealHilbertComplexification.extend R).adjoint^m=0 := Subsingleton.elim _ _
    have hz : ‖R.adjoint^m‖=0 := by
      simpa only [←extend_adjoint,←extend_pow,norm_extend,norm_zero] using congrArg norm he
    change ‖R.adjoint^m‖^2 ≤ _
    rw [hz]
    simp
  · have hcomparison := actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower)
    have hcomp := rationalIntegrationComparison_extend R L hκ.le hcomparison
    have hU := canonicalIntegrationResolvent_inverse (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) hκ.le
    have hscalar := scalar_curvature_comparison_of_resolvent (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L)
      (canonicalIntegrationResolvent (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) κ) hκ hU hcomp
    have hbudgetC := jointObservationBudget_extend R L hbudget
    have hspec : spectralRadius ℂ (KLSBelow25.RealHilbertComplexification.extend R).adjoint≤ENNReal.ofReal (Real.sqrt K) := by
      apply spectralRadius_le_of_scalar_comparison (KLSBelow25.RealHilbertComplexification.extend R).adjoint (KLSBelow25.RealHilbertComplexification.extend L).adjoint hκ K_positive 1
      · simpa only [adjoint_adjoint] using hscalar
      · intro m hm
        calc
          ‖(KLSBelow25.RealHilbertComplexification.extend L).adjoint.comp ((KLSBelow25.RealHilbertComplexification.extend R).adjoint^m)‖^2≤C*K^(m+1) :=
            observation_norm_sq_le_of_joint_budget (KLSBelow25.RealHilbertComplexification.extend R) (KLSBelow25.RealHilbertComplexification.extend L) K_positive
              (by norm_num [C]) hbudgetC m hm
          _ = (C*K)*K^m := by rw [pow_succ]; ring
    intro rho hrho
    obtain ⟨M,hM⟩ := squared_power_envelope_of_spectralRadius_le
      (KLSBelow25.RealHilbertComplexification.extend R).adjoint K_positive hspec rho hrho
    refine ⟨M,fun m => ?_⟩
    simpa only [←extend_adjoint,←extend_pow,norm_extend] using hM m

end KLSConstantImprovement.MicroWeightedAdjointEnvelope
#print axioms KLSConstantImprovement.MicroWeightedAdjointEnvelope.actual_micro_joint_observation_budget
#print axioms KLSConstantImprovement.MicroWeightedAdjointEnvelope.actual_micro_adjoint_power_envelope
