import ActualQuadraticTensorObservation
import CompatibleTensorDegreeZero

/-! Exact remaining analytic reduction for the faithful Poincare constant.
These are conditional regular-law endpoints. The geometric comparison and
all-order Appell growth hypotheses have deliberately not been hidden. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem actual_regular_poincare_twentyFive_of_remaining_analytic_bounds
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower)
    (hobs : ∀ j : ℕ, ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤
        (121/4 : ℝ)*(223/10 : ℝ)^j) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal 25 := by
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal (actual_graded_norm_twentyFive_of_analytic_bounds
      hφ hκ hlower hμ.isotropic hcomparison
      (actual_graded_quadratic_observation_le_two hφ hκ hlower hμ) hobs))

theorem actual_regular_poincare_twentyFour886_of_remaining_analytic_bounds
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower)
    (hobs : ∀ j : ℕ, ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤
        (121/4 : ℝ)*(2221/100 : ℝ)^j) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal (12443/500 : ℝ) := by
  exact (poincareConstant_le_one_add_graded_norm_sq hφ hκ hlower hn hμ.isotropic).trans
    (ENNReal.ofReal_le_ofReal (actual_graded_norm_twentyFour886_of_analytic_bounds
      hφ hκ hlower hμ.isotropic hcomparison
      (actual_graded_quadratic_observation_le_two hφ hκ hlower hμ) hobs))

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_regular_poincare_twentyFive_of_remaining_analytic_bounds
#print axioms KLS.DeterministicBridgeIntegration.actual_regular_poincare_twentyFour886_of_remaining_analytic_bounds
