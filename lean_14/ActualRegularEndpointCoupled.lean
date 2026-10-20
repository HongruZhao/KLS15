import JointObservationOperatorEndgame
import ActualJointAppellObservability
import ActualWeightedAppellEnergy
import ActualTensorCurvatureComparison

/-! A coupled actual Appell estimate gives the regular-law Poincare bound.
The only new input is the scalar coupled estimate; all tensor realization,
curvature, graded observability and operator endgame steps are proved. -/
noncomputable section
open MeasureTheory Matrix Set InnerProductSpace
open scoped ContDiff ENNReal BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration KLSBelow25.RealHilbertComplexification
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_regular_poincare_of_coupled_appell
    {n : ℕ} {φ : Space n→ℝ} {κ K C : ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0<κ)
    (hlower : ∀ x (a : Fin n→ℝ),
      κ*(a ⬝ᵥ a)≤a ⬝ᵥ (coordinateHessian φ x *ᵥ a))
    (hn : 0<n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hK : 0<K) (hC : 0≤C)
    (hcoupled : ∀ (N : ℕ) (f : Lp ℝ 2 (potentialMeasure φ)),
      actualWeightedAppellEnergy (potentialMeasure φ) f K N≤C*‖f‖^2) :
    poincareConstant (potentialMeasure φ)≤ENNReal.ofReal (1+K*(1+C)) := by
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
    exact actual_joint_graded_observability hφ hκ hlower hμ hK hC hraw N f
  have hb := real_canonical_operator_endpoint_joint_budget
    (gradedTensorIntegration hφ hκ hlower)
    (gradedConstantIntegration hφ hκ hlower hμ.isotropic) hκ hK hC
    (actual_graded_rational_comparison hφ hκ hlower hμ.isotropic
      (actual_tensor_curvature_comparison hφ hκ hlower)) hbudget
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal hb)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_regular_poincare_of_coupled_appell
#check KLS.DeterministicBridgeNext.actual_regular_poincare_of_coupled_appell
