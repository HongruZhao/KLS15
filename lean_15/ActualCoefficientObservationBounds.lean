import ActualRepeatedAppellObservation
import ActualRegularPoincareReduction
import QuinticConvolution

/-! Exact normalization of genuine Appell energy bounds into the full
graded observation bound. The actual coefficient induction and tensor
curvature comparison remain explicit inputs in the final regular theorem. -/
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff ENNReal
namespace KLS.DeterministicBridgeNext
open KLS KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ),
    κ*(a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem actual_repeated_observation_sq_le_of_energy
    (hμ : admissibleMeasure (potentialMeasure φ)) (d : ℕ)
    {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ f : Lp ℝ 2 (potentialMeasure φ),
      actualAppellEnergy (potentialMeasure φ) f (d+1) ≤ C*‖f‖^2) :
    ‖((gradedTensorIntegration hφ hκ hlower)^d).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤
        ((d+1).factorial : ℝ)⁻¹^2*C := by
  have hb := actual_repeated_observation_norm_le hφ hκ hlower hμ d
  have ho := (actualAppellObservation_opNorm_le_iff hμ (d+1) hC).mpr henergy
  have hs := pow_le_pow_left₀ (norm_nonneg _) ho 2
  rw [Real.sq_sqrt hC] at hs
  calc
    _ ≤ (((d+1).factorial : ℝ)⁻¹*‖actualAppellObservation hμ (d+1)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = ((d+1).factorial : ℝ)⁻¹^2*‖actualAppellObservation hμ (d+1)‖^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg _)

theorem actual_observation_quintic_envelope
    (hμ : admissibleMeasure (potentialMeasure φ))
    (hcoeff : ∀ j (f : Lp ℝ 2 (potentialMeasure φ)),
      actualAppellEnergy (potentialMeasure φ) f (j+3) ≤
        Quintic24886.coefficientH (j+3)*‖f‖^2) (j : ℕ) :
    ‖((gradedTensorIntegration hφ hκ hlower)^(j+2)).comp
      (gradedConstantIntegration hφ hκ hlower hμ.isotropic)‖^2 ≤
        (121/4 : ℝ)*(2221/100 : ℝ)^j := by
  have he := actual_repeated_observation_sq_le_of_energy hφ hκ hlower hμ (j+2)
    (Quintic24886.coefficientH_positive (j+3)).le (hcoeff j)
  have hfac : ((j+3).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j+3)
  rw [Quintic24886.coefficientH_ge_three (by omega : 3 ≤ j+3)] at he
  have hid : ((j+2+1).factorial : ℝ)⁻¹^2*
      (Quintic24886.B*Quintic24886.K^(j+3-3)*((j+3).factorial : ℝ)^2)=
        (121/4 : ℝ)*(2221/100 : ℝ)^j := by
    simp only [show j+2+1=j+3 by omega,show j+3-3=j by omega]
    rw [Quintic24886.B,Quintic24886.K]
    field_simp
  exact hid ▸ he

theorem actual_regular_poincare_twentyFour886_of_coefficient_and_curvature
    (hn : 0 < n) (hμ : admissibleMeasure (potentialMeasure φ))
    (hcomparison : ActualTensorCurvatureComparison hφ hκ hlower)
    (hcoeff : ∀ j (f : Lp ℝ 2 (potentialMeasure φ)),
      actualAppellEnergy (potentialMeasure φ) f (j+3) ≤
        Quintic24886.coefficientH (j+3)*‖f‖^2) :
    poincareConstant (potentialMeasure φ) ≤ ENNReal.ofReal (12443/500 : ℝ) :=
  actual_regular_poincare_twentyFour886_of_remaining_analytic_bounds hφ hκ hlower hn hμ
    hcomparison (actual_observation_quintic_envelope hφ hκ hlower hμ hcoeff)

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_repeated_observation_sq_le_of_energy
#print axioms KLS.DeterministicBridgeNext.actual_observation_quintic_envelope
#print axioms KLS.DeterministicBridgeNext.actual_regular_poincare_twentyFour886_of_coefficient_and_curvature
