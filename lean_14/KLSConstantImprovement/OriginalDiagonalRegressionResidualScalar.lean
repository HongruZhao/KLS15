import Mathlib

/- Scalar consequences only. The original marginal comparison, common joint-H
regression identity, fourth covariance identities, and Poisson projection are
explicit premises. This file supplies no actual-law analytic bridge and was not
built by the research worker. -/

namespace KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar

theorem scalar_regression_variance_bound
    (a c h2 m4 y d : ℝ)
    (hupper : m4 ≤ 6 + (3 / 4 : ℝ) * a ^ 2)
    (hreg : a ^ 2 ≤ c) (hcap : h2 ≤ 2)
    (hy : y = h2 - 1 - c / 4) (hd : d = 9 - m4) :
    y ≤ d / 3 := by
  nlinarith

theorem scalar_extra_savings
    (a c h2 m4 y d delta : ℝ)
    (hupper : m4 ≤ 6 + (3 / 4 : ℝ) * a ^ 2)
    (hy : y = h2 - 1 - c / 4) (hd : d = 9 - m4)
    (hdelta : delta = 2 - h2) :
    y + delta + (c - a ^ 2) / 4 ≤ d / 3 := by
  nlinarith

theorem weighted_regression_sum
    {ι : Type*} [Fintype ι] (t y d : ι → ℝ)
    (hpaid : ∀ i, y i ≤ d i / 3) :
    (∑ i, (t i) ^ 2 * y i) ≤ (∑ i, (t i) ^ 2 * d i) / 3 := by
  calc
    (∑ i, (t i) ^ 2 * y i) ≤ ∑ i, (t i) ^ 2 * (d i / 3) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hpaid i) (sq_nonneg (t i))
    _ = (∑ i, (t i) ^ 2 * d i) / 3 := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem projected_pairing_square
    (r y d energy : ℝ) (he : 0 ≤ energy)
    (hy : y ≤ d / 3) (hcauchy : r ^ 2 ≤ 36 * y * energy) :
    r ^ 2 ≤ 12 * d * energy := by
  have h := mul_le_mul_of_nonneg_right hy he
  nlinarith

theorem covariance_fourcharge_identity
    (n g lambda f j b d delta y : ℝ)
    (hcompatible : 3 * j = g + 4 * lambda - 4 * f)
    (hd : d = 8 * n - g) (hdelta : delta = 2 * n - lambda)
    (hreg : y = f - b / 4) :
    y = 4 * n - d / 4 - delta - b / 4 - 3 * j / 4 := by
  linarith

theorem covariance_fourcharge_upper
    (n b d delta j y : ℝ)
    (hdelta : 0 ≤ delta) (hj : 0 ≤ j)
    (hid : y = 4 * n - d / 4 - delta - b / 4 - 3 * j / 4) :
    y ≤ 4 * n - d / 4 - b / 4 := by
  linarith

#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.scalar_regression_variance_bound
#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.scalar_extra_savings
#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.weighted_regression_sum
#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.projected_pairing_square
#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.covariance_fourcharge_identity
#print axioms KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar.covariance_fourcharge_upper

end KLSConstantImprovement.OriginalDiagonalRegressionResidualScalar
