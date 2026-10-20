import Mathlib

/- Refined constants for the frozen original ODECO same-metric payment.
The Eitan/mixed-moment and same-response analytic premises stay explicit. -/

namespace KLSConstantImprovement.OriginalAffineOffMetricRefinedScalar

theorem shifted_moment_coefficient :
    (8 * (89 / 10 : ℝ) ^ 4) = (62742241 / 1250 : ℝ) := by norm_num

theorem refined_affine_off_squared_budget
    (u2 off2 u4 N d : ℝ) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hholder : u2 ^ 2 ≤ off2 * u4)
    (hu4 : 0 ≤ u4) (hoff : off2 ≤ d / 4)
    (hmixed : u4 ≤ (62742241 / 1250 : ℝ) * N) :
    u2 ^ 2 ≤ (62742241 / 5000 : ℝ) * N * d := by
  have hproduct : off2 * u4 ≤ (d / 4) * ((62742241 / 1250 : ℝ) * N) :=
    mul_le_mul hoff hmixed hu4 (by positivity)
  nlinarith

theorem refined_metric_off_squared_budget
    (o u2 N d : ℝ) (ho : 0 ≤ o) (hu2 : 0 ≤ u2)
    (hN : 0 ≤ N) (hd : 0 ≤ d)
    (hmain : o ≤ 9 * u2)
    (hpaid : u2 ^ 2 ≤ (62742241 / 5000 : ℝ) * N * d) :
    o ^ 2 ≤ 2 * 713 ^ 2 * N * d := by
  have hsquare : o ^ 2 ≤ (9 * u2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (by positivity : 0 ≤ 9 * u2 + o)]
  nlinarith [mul_nonneg hN hd]

#print axioms KLSConstantImprovement.OriginalAffineOffMetricRefinedScalar.shifted_moment_coefficient
#print axioms KLSConstantImprovement.OriginalAffineOffMetricRefinedScalar.refined_affine_off_squared_budget
#print axioms KLSConstantImprovement.OriginalAffineOffMetricRefinedScalar.refined_metric_off_squared_budget

end KLSConstantImprovement.OriginalAffineOffMetricRefinedScalar
