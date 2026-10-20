import ActualCorrelatedQuarticObservationCaps200000
import ActualCorrelatedCubicTangentCaps239

/-! The genuine quartic adjacent curve on the full graded Hilbert space.
The tangent supporting family is lifted before selecting its own argument;
there is no nonlinear interchange with an infinite graded sum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open MeasureTheory InnerProductSpace Set Matrix ContinuousLinearMap
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal

namespace KLSBelow25.QuarticCreation200000
open KLS.DeterministicBridgeNext

def observationScale : ℝ := 200000/576
def observationSupportWeight (u : ℝ) : ℝ :=
  -observationScale*deriv seedPhi u/CreationSeed239.B
def observationSupportIntercept (u : ℝ) : ℝ :=
  observationScale*(seedPhi u-u*deriv seedPhi u)

theorem observationSupportWeight_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ observationSupportWeight u := by
  have hd : deriv seedPhi u < 0 := seedInverseBarrier.deriv_phi_negative hu
  dsimp [observationSupportWeight, observationScale]
  apply div_nonneg _ CreationSeed239.B_positive.le
  nlinarith

theorem observationSupportIntercept_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ observationSupportIntercept u := by
  have hd : deriv seedPhi u < 0 := seedInverseBarrier.deriv_phi_negative hu
  have hp : 0 < seedPhi u := seedInverseBarrier.phi_positive hu
  have hm : u*deriv seedPhi u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.1 hd.le
  dsimp [observationSupportIntercept, observationScale]
  exact mul_nonneg (by norm_num) (by linarith)

theorem observation_supporting_shape {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    observationSupportWeight u*CreationSeed239.B*v+
      (1/576)*200000*seedPhi v ≤ observationSupportIntercept u := by
  have ht := concave_barrier_tangent seedInverseBarrier.concaveOn_phi hu hv
    ((hasDerivAt_seedPhi hu).differentiableAt.hasDerivAt)
  change seedPhi v ≤ seedPhi u+deriv seedPhi u*(v-u) at ht
  have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 200000/576)
  dsimp [observationSupportWeight, observationSupportIntercept, observationScale]
  norm_num only [CreationSeed239.B] at *
  nlinarith
end KLSBelow25.QuarticCreation200000

namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25 KLSBelow25.GradedHilbert
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
variable [IsProbabilityMeasure (potentialMeasure φ)]
variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (v : Fin n → ℝ), κ*(v ⬝ᵥ v) ≤ v ⬝ᵥ (coordinateHessian φ x *ᵥ v))
  (hμ : admissibleMeasure (potentialMeasure φ))

theorem actual_correlated_quartic_graded_tangent_cap_creation200000 {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (f : GradedCenteredTensorHilbert hφ) :
    QuarticCreation200000.observationSupportWeight u*
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2+
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤
      QuarticCreation200000.observationSupportIntercept u*‖f‖^2 := by
  have hh := actual_correlated_quartic_graded_supporting_cap_creation200000
    hφ hκ hlower hμ (a := 0) (b := QuarticCreation200000.observationSupportWeight u)
    (c := 1) (H := QuarticCreation200000.observationSupportIntercept u)
    le_rfl (QuarticCreation200000.observationSupportWeight_nonneg hu) zero_le_one
    (QuarticCreation200000.observationSupportIntercept_nonneg hu)
    (fun _ _ v hv _ => by
      simpa only [mul_zero, zero_mul, zero_add] using
        QuarticCreation200000.observation_supporting_shape hu v hv) f
  simpa only [zero_mul, zero_add, one_mul] using hh

theorem actual_correlated_quartic_graded_cap_creation200000
    (f : GradedCenteredTensorHilbert hφ) :
    ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^3) f)‖^2 ≤
      QuarticCreation200000.observationScale*‖f‖^2*QuarticCreation200000.seedPhi
        (‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
          (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2/
            (CreationSeed239.B*‖f‖^2)) := by
  by_cases hf : f = 0
  · subst f
    simp
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  let v : ℝ := ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
    (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2/
      (CreationSeed239.B*‖f‖^2)
  have hcap : ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
      (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ CreationSeed239.B*‖f‖^2 := by
    have hh := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 36) CreationSeed239.B_positive.le)
      (actual_appell_energy_three_creation239_le_norm_sq hμ) f
    norm_num only [Nat.add, Nat.factorial, Nat.cast_ofNat, inv_pow] at hh
    convert hh using 1; ring
  have hv : v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sq_nonneg _) (mul_pos CreationSeed239.B_positive hn).le
    · exact (div_le_one (mul_pos CreationSeed239.B_positive hn)).mpr hcap
  have ht := actual_correlated_quartic_graded_tangent_cap_creation200000 hφ hκ hlower hμ hv f
  change _ ≤ QuarticCreation200000.observationScale*‖f‖^2*
    QuarticCreation200000.seedPhi v
  have hrel : v*(CreationSeed239.B*‖f‖^2) =
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 := by
    dsimp only [v]
    exact div_mul_cancel₀ _ (mul_pos CreationSeed239.B_positive hn).ne'
  have hcancel : QuarticCreation200000.observationSupportWeight v*
      ‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2+
      QuarticCreation200000.observationScale*‖f‖^2*v*
        deriv QuarticCreation200000.seedPhi v = 0 := by
    rw [←hrel]
    dsimp only [QuarticCreation200000.observationSupportWeight]
    field_simp [CreationSeed239.B_positive.ne']
    ring
  dsimp only [QuarticCreation200000.observationSupportIntercept] at ht
  nlinarith only [ht, hcancel]

end KLS.DeterministicBridgeIntegration
#print axioms KLSBelow25.QuarticCreation200000.observation_supporting_shape
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_quartic_graded_tangent_cap_creation200000
#print axioms KLS.DeterministicBridgeIntegration.actual_correlated_quartic_graded_cap_creation200000
