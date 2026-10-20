import KLSConstantImprovement.ActualCorrelatedCubicObservationCaps2388
import ConcaveBarrierTangent

/-! The tangent family eliminates the scalar supporting-line premise.
It also recovers the nonlinear correlated cap on the full graded space,
without interchanging a nonlinear function with an infinite sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
open MeasureTheory InnerProductSpace Set Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal

namespace KLSBelow25.CreationSeed2388
open KLS.DeterministicBridgeNext

def supportWeight (u : ℝ) : ℝ := -B*deriv seedPhi u/2
def supportIntercept (u : ℝ) : ℝ := B*(seedPhi u-u*deriv seedPhi u)

theorem supportWeight_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ supportWeight u := by
  have hd : deriv seedPhi u < 0 := seedInverseBarrier.deriv_phi_negative hu
  have hB : 0 < B := B_positive
  dsimp [supportWeight]
  nlinarith

theorem supportIntercept_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ supportIntercept u := by
  have hd : deriv seedPhi u < 0 := seedInverseBarrier.deriv_phi_negative hu
  have hp : 0 < seedPhi u := seedInverseBarrier.phi_positive hu
  have hm : u*deriv seedPhi u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1 hd.le
  dsimp [supportIntercept]
  exact mul_nonneg B_positive.le (by linarith)

theorem supporting_shape {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    2*supportWeight u*v+1*B*seedPhi v ≤ supportIntercept u := by
  have ht := concave_barrier_tangent seedInverseBarrier.concaveOn_phi hu hv
    ((hasDerivAt_seedPhi hu).differentiableAt.hasDerivAt)
  change seedPhi v ≤ seedPhi u+deriv seedPhi u*(v-u) at ht
  have hm := mul_le_mul_of_nonneg_left ht B_positive.le
  dsimp [supportWeight, supportIntercept]
  nlinarith

end KLSBelow25.CreationSeed2388

namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25 KLSBelow25.GradedHilbert
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (v : Fin n → ℝ), κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_correlated_cubic_graded_tangent_cap_creation2388 {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (f : GradedCenteredTensorHilbert hφ) :
    CreationSeed2388.supportWeight u*
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2+
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤
      CreationSeed2388.supportIntercept u*‖f‖^2 := by
  simpa only [one_mul] using actual_correlated_cubic_graded_supporting_cap_creation2388
    hφ hκ hlower hμ (CreationSeed2388.supportWeight_nonneg hu) zero_le_one
    (CreationSeed2388.supportIntercept_nonneg hu) (CreationSeed2388.supporting_shape hu) f

theorem actual_correlated_cubic_graded_tangent_cap_normalized_creation2388 {K u : ℝ}
    (hK : 0 < K) (hu : u ∈ Icc (0 : ℝ) 1) (f : GradedCenteredTensorHilbert hφ) :
    (CreationSeed2388.supportWeight u/K)*(K⁻¹^2*
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2)+
      K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤
      (CreationSeed2388.supportIntercept u/K^3)*‖f‖^2 := by
  have hh := mul_le_mul_of_nonneg_left
    (actual_correlated_cubic_graded_tangent_cap_creation2388 hφ hκ hlower hμ hu f)
    (pow_nonneg (inv_nonneg.mpr hK.le) 3)
  convert hh using 1 <;> field_simp

theorem actual_correlated_cubic_graded_cap_creation2388 (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤
      CreationSeed2388.B*‖f‖^2*CreationSeed2388.seedPhi
        (‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
          (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2/(2*‖f‖^2)) := by
  by_cases hf : f = 0
  · subst f
    simp
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  let v : ℝ := ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
    (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2/(2*‖f‖^2)
  have hv : v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sq_nonneg _) (by positivity)
    · exact (div_le_one (by positivity : 0 < 2*‖f‖^2)).mpr
        (actual_first_graded_observation_sq_le hφ hκ hlower hμ f)
  have ht := actual_correlated_cubic_graded_tangent_cap_creation2388 hφ hκ hlower hμ hv f
  dsimp [CreationSeed2388.supportWeight, CreationSeed2388.supportIntercept, v] at ht
  have hne : ‖f‖^2 ≠ 0 := ne_of_gt hn
  field_simp [hne] at ht
  nlinarith

end KLS.DeterministicBridgeIntegration

#print axioms KLSBelow25.CreationSeed2388.supporting_shape
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_cubic_graded_tangent_cap_creation2388
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_cubic_graded_tangent_cap_normalized_creation2388
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_cubic_graded_cap_creation2388
