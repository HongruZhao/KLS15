import ActualJointAppellObservability
import ActualAppellQuadraticSeed

/-! Individual scalar Appell caps pass to the actual graded tensor
observations without dimension, rank, or binomial losses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory InnerProductSpace Set Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25 KLSBelow25.GradedHilbert
variable {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
  (hlower : ∀ x (v : Fin n→ℝ),κ*(v ⬝ᵥ v)≤v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_individual_graded_observation_sq_le (d : ℕ) {H : ℝ} (hH : 0≤H)
    (hscalar : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      actualAppellEnergy (potentialMeasure φ) f (d+1)≤H*‖f‖^2)
    (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^d) f)‖^2≤
      ((d+1).factorial : ℝ)⁻¹^2*H*‖f‖^2 := by
  have hblock (r : ℕ) (v : CenteredCompatibleTensorHilbert (hφ.of_le (by simp)) r) :
      ‖(actualPowerObservationBlock hφ hκ hlower hμ d r).adjoint v‖^2≤
      (((d+1).factorial : ℝ)⁻¹^2*H)*‖v‖^2 := by
    calc
      _≤((d+1).factorial : ℝ)⁻¹^2*∑I,actualAppellEnergy (potentialMeasure φ)
          ((v : OrderedTensorField φ r) I) (d+1) :=
        actual_repeated_observation_block_adjoint_sq_le hφ hκ hlower hμ d r v
      _≤((d+1).factorial : ℝ)⁻¹^2*∑I,H*‖(v : OrderedTensorField φ r) I‖^2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact Finset.sum_le_sum (fun I _ => hscalar ((v : OrderedTensorField φ r) I))
      _=(((d+1).factorial : ℝ)⁻¹^2*H)*‖v‖^2 := by
        rw [←Finset.mul_sum,←PiLp.norm_sq_eq_of_L2]
        change ((d+1).factorial : ℝ)⁻¹^2*(H*‖v‖^2)=_
        ring
  have hb := weighted_joint_adjoint_observation_le_of_blocks
    (centeredTensorIntegration hφ hκ hlower) (constantTensorIntegration hφ hκ hlower)
    (Real.sqrt_nonneg _) (centeredTensorIntegration_opNorm_le hφ hκ hlower) zero_le_one
    (constantTensorIntegration_opNorm_le_one hφ hκ hlower hμ.isotropic)
    ({d} : Finset ℕ) (fun _ => (1 : ℝ))
    (mul_nonneg (sq_nonneg _) hH)
    (fun r v => by simpa only [Finset.sum_singleton,one_mul] using hblock r v) f
  simp only [Finset.sum_singleton,one_mul] at hb
  change ‖(((gradedTensorIntegration hφ hκ hlower)^d).comp
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic)).adjoint f‖^2≤_ at hb
  simpa only [adjoint_comp,AdjointOrbitRecurrence.adjoint_pow,ContinuousLinearMap.comp_apply] using hb

theorem actual_first_graded_observation_sq_le
    (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2≤2*‖f‖^2 := by
  have hb := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 1
    (by norm_num : (0 : ℝ)≤8) (fun f => actualAppellEnergy_two_le_eight_norm_sq hμ f) f
  norm_num at hb ⊢
  exact hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_individual_graded_observation_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actual_first_graded_observation_sq_le
