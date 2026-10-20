import Mathlib

/-! Scalar charges for the original canonical-product symmetric response
lift. Factor Poincare, Stein second moment, fixed-third comparison,
independence and lift/domain inputs remain explicit. Scalar4 is a separate
published factor premise; the internally paid corollary uses71727/5000. -/
noncomputable section
namespace KLSConstantImprovement.OriginalProductSymmetricLiftScalar
set_option maxHeartbeats 2000000

theorem factor_regression_budget {v m k : ℝ}
    (hv : v ≤ 1-m^2/4) (hk : k ≤ 3+(3/4 : ℝ)*m^2) :
    3*v+k ≤ 6 := by linarith

theorem weighted_factor_budget {v k alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hv : v ≤ 1) (hbudget : 3*v+k ≤ 6) : 3*v+k*alpha ≤ 6 := by
  by_cases hk : 0 ≤ k
  · have hmul := mul_le_mul_of_nonneg_left ha1 hk
    nlinarith
  · have hk0 : k ≤ 0 := by linarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg hk0 ha0
    linarith

theorem same_response_product_payment {C h d hess r : ℝ}
    (hC : 0 ≤ C) (hhess : 0 ≤ hess) (hcharge : h ≤ d/3)
    (hlift : r^2 ≤ C*h*hess) : r^2 ≤ (C/3)*d*hess := by
  have hp := mul_le_mul_of_nonneg_right hcharge hhess
  have hq := mul_le_mul_of_nonneg_left hp hC
  nlinarith

theorem verified_constant_product_payment {h d hess r : ℝ}
    (hhess : 0 ≤ hess) (hcharge : h ≤ d/3)
    (hlift : r^2 ≤ (71727/5000 : ℝ)*h*hess) :
    r^2 ≤ (23909/5000 : ℝ)*d*hess := by
  have hp := same_response_product_payment
    (by norm_num : (0 : ℝ) ≤ 71727/5000) hhess hcharge hlift
  norm_num at hp ⊢
  exact hp

end KLSConstantImprovement.OriginalProductSymmetricLiftScalar
#print axioms KLSConstantImprovement.OriginalProductSymmetricLiftScalar.factor_regression_budget
#print axioms KLSConstantImprovement.OriginalProductSymmetricLiftScalar.weighted_factor_budget
#print axioms KLSConstantImprovement.OriginalProductSymmetricLiftScalar.same_response_product_payment
#print axioms KLSConstantImprovement.OriginalProductSymmetricLiftScalar.verified_constant_product_payment
