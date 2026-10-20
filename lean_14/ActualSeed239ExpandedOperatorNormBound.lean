import TwoHeadObservationOperatorEndgame
import ActualIndividualObservationCaps
import ActualRegularEndpointCoupled
import ActualWeightedAppellInductionSeed239Expanded
import ActualCreationCubicSeed239Cap

/-! Actual graded operator norm auxiliary bound from the expanded all-degree profile.
This is an operator estimate proved in the correct direction. -/
noncomputable section
open MeasureTheory Matrix Set InnerProductSpace
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.RealHilbertComplexification
open KLSBelow25.CoupledEnergy.NumericsSeed239Expanded
set_option maxHeartbeats 110000000
set_option backward.isDefEq.respectTransparency false

theorem actual_seed239_expanded_graded_operator_norm_sq_le
    {n : ℕ} {φ : Space n→ℝ} {κ : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hμ : admissibleMeasure (potentialMeasure φ))
    : ‖gradedTensorIntegration hφ hκ hlower‖^2≤K*p := by
  have hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      actualWeightedAppellEnergy (potentialMeasure φ) f K N≤C*‖f‖^2 := by
    intro N f
    exact actual_weighted_appell_energy_seed239_expanded_norm_sq_le N hμ f
  have hthree : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      actualAppellEnergy (potentialMeasure φ) f 3≤(36*24 : ℝ)*‖f‖^2 := by
    intro f
    have hb := actual_appell_energy_three_creation239_le_norm_sq hμ f
    norm_num only [KLSBelow25.CreationSeed239.B] at hb
    nlinarith [sq_nonneg ‖f‖]
  have hraw : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      ∑d∈Finset.Icc 2 N,K⁻¹^d*actualAppellEnergy (potentialMeasure φ) f d/(d.factorial : ℝ)^2≤C*‖f‖^2 := by
    intro N f
    convert hcoupled N f using 1
    unfold actualWeightedAppellEnergy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [_root_.mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  have hbudget : KLSBelow25.CoupledEnergy.jointObservationBudget
      (gradedTensorIntegration hφ hκ hlower)
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic) K C := by
    intro N f
    exact actual_joint_graded_observability hφ hκ hlower hμ K_positive C_positive.le hraw N f
  have hcap1 (f : GradedCenteredTensorHilbert hφ) :
      K⁻¹^2*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^1) f)‖^2≤firstCap*‖f‖^2 := by
    have hb := actual_first_graded_observation_sq_le hφ hκ hlower hμ f
    norm_num [K,firstCap] at hb ⊢
    nlinarith
  have hcap2 (f : GradedCenteredTensorHilbert hφ) :
      K⁻¹^3*‖(gradedConstantIntegration hφ hκ hlower hμ.isotropic).adjoint
        (((gradedTensorIntegration hφ hκ hlower).adjoint^2) f)‖^2 ≤ secondCap*‖f‖^2 := by
    have hb0 := actual_individual_graded_observation_sq_le hφ hκ hlower hμ 2
      (by norm_num : (0 : ℝ)≤36*24) hthree f
    norm_num [K,secondCap] at hb0 ⊢
    nlinarith
  have hcost : residualRatio+firstCap/p+secondCap/secondLower+
      (C-firstCap-secondCap)/thirdLower≤p := by
    unfold residualRatio
    linarith
  have hb := real_canonical_operator_endpoint_two_head_budget
    (gradedTensorIntegration hφ hκ hlower)
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic)
    hκ K_positive C_positive.le p_gt_one caps_nonneg.1 caps_nonneg.2
    caps_sum_le_budget secondLower_ge_p thirdLower_ge_second
    (by rfl : secondLower≤p^2-firstCap)
    (by rfl : thirdLower≤ secondLower*(p-firstCap/p)-secondCap)
    residualRatio_gt_one hcost
    (actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower)) hbudget hcap1 hcap2
  linarith

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_seed239_expanded_graded_operator_norm_sq_le
