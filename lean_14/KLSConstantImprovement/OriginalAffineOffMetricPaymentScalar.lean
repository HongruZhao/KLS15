import Mathlib

/- Scalar consequences of the original ODECO affine off metric payment.
Fractional moment hierarchy, same original joint kernel, Holder, and
the metric-dependent common Poisson identity remain explicit inputs. -/

namespace KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar

theorem affine_off_squared_budget
    (u2 off2 u4 N d : ℝ) (hd : 0 ≤ d) (hN : 0 ≤ N)
    (hholder : u2 ^ 2 ≤ off2 * u4)
    (hu4 : 0 ≤ u4) (hoff : off2 ≤ d / 4) (hmixed : u4 ≤ 52488 * N) :
    u2 ^ 2 ≤ 13122 * N * d := by
  have hproduct : off2 * u4 ≤ (d / 4) * (52488 * N) :=
    mul_le_mul hoff hmixed hu4 (by positivity)
  nlinarith

theorem metric_off_main_budget
    (o u2 N d : ℝ) (ho : 0 ≤ o) (hu2 : 0 ≤ u2)
    (hmain : o ≤ 9 * u2) (hpaid : u2 ^ 2 ≤ 13122 * N * d) :
    o ^ 2 ≤ 1062882 * N * d := by
  have hsquare : o ^ 2 ≤ (9 * u2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (by positivity : 0 ≤ 9 * u2 + o)]
  nlinarith

theorem same_metric_combined_upper
    (V core off response loss curvature : ℝ)
    (hidentity : V = core + off + response - loss - curvature)
    (hloss : 0 ≤ loss) : V ≤ core + off + response - curvature := by
  linarith

theorem regularized_off_main_upper
    (o u2 eta R : ℝ) (h : o ≤ 9 * u2 + 9 * eta * R) :
    o - 9 * eta * R ≤ 9 * u2 := by
  linarith

#print axioms KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar.affine_off_squared_budget
#print axioms KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar.metric_off_main_budget
#print axioms KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar.same_metric_combined_upper
#print axioms KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar.regularized_off_main_upper

end KLSConstantImprovement.OriginalAffineOffMetricPaymentScalar
