import Mathlib

/-! Finite curvature weights in an actual scalar exponential source
tangent. The original normalized density/kernel/right-derivative domain
and integrations are analytic inputs. These declarations do not assert
a finite-deficit, dependent-law or all-tensor cubic moment/response bound. -/
noncomputable section
namespace KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent

theorem signed_cross_curvature_compensation {t c : ℝ} :
    2*(t^4*c)+3*(t^3*(2-t)*c/3) = t^3*(t+2)*c := by ring

theorem paid_curvature_compensation_nonneg {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    0 ≤ 2*(t^4*c)+3*(t^3*(2-t)*c/3) := by
  rw [signed_cross_curvature_compensation]
  exact mul_nonneg (mul_nonneg (pow_nonneg ht 3) (by linarith)) hc

theorem cubic_moment_tangent_nonpositive {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    -(t^3*(t+5)*c) ≤ 0 := by
  have h := mul_nonneg (mul_nonneg (pow_nonneg ht 3) (by linarith : 0 ≤ t+5)) hc
  linarith

theorem same_response_residual_tangent_nonpositive {t c : ℝ}
    (ht : 0 ≤ t) (hc : 0 ≤ c) :
    -(t^3*(2*t^3+3*t^2+39*t+174)*c)/2 ≤ 0 := by
  have hpoly : 0 ≤ 2*t^3+3*t^2+39*t+174 := by
    have ht3 := pow_nonneg ht 3
    have ht2 := sq_nonneg t
    nlinarith
  have h := mul_nonneg (mul_nonneg (pow_nonneg ht 3) hpoly) hc
  linarith

end KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent
#print axioms KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent.signed_cross_curvature_compensation
#print axioms KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent.paid_curvature_compensation_nonneg
#print axioms KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent.cubic_moment_tangent_nonpositive
#print axioms KLSConstantImprovement.OriginalExponentialSourceCurvatureTangent.same_response_residual_tangent_nonpositive
