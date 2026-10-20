import Mathlib

/-! Scalar closure for the proved original-law ODECO cubic-test response
projection. The actual covariance, full-regression and weighted tensor
charges remain explicit premises. No arbitrary Poisson response or
general-tensor original additive theorem is asserted. -/
noncomputable section
namespace KLSConstantImprovement.OriginalCubicResponseProjectionScalar
set_option maxHeartbeats 2000000

theorem regression_shuffle_charge {ell d s c : ℝ}
    (hell : ell ≤ (7/12 : ℝ)*d) (hs : 0 ≤ s)
    (hc : c^2 ≤ 42*ell*s) : c^2 ≤ (49/2 : ℝ)*d*s := by
  have hp := mul_le_mul_of_nonneg_right hell hs
  nlinarith

theorem cubic_projection_bound {d s a b c phi : ℝ}
    (hd : 0 ≤ d) (hs : 0 ≤ s) (hphi : phi = a+b-c)
    (ha : a^2 ≤ 3*d*s) (hb : b^2 ≤ (20/3 : ℝ)*d*s)
    (hc : c^2 ≤ (49/2 : ℝ)*d*s) : phi^2 ≤ 100*d*s := by
  have hroot0 := Real.sqrt_nonneg (d*s)
  have hroot := Real.sq_sqrt (show 0 ≤ d*s by positivity)
  have ha0 := abs_nonneg a
  have hb0 := abs_nonneg b
  have hc0 := abs_nonneg c
  have haa : |a| ≤ 2*Real.sqrt (d*s) := by
    by_contra! hn
    nlinarith [sq_abs a]
  have hbb : |b| ≤ 3*Real.sqrt (d*s) := by
    by_contra! hn
    nlinarith [sq_abs b]
  have hcc : |c| ≤ 5*Real.sqrt (d*s) := by
    by_contra! hn
    nlinarith [sq_abs c]
  have habs : |phi| ≤ |a|+|b|+|c| := by
    rw [hphi]
    calc
      |a+b-c| ≤ |a+b|+|c| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (a+b) (-c)
      _ ≤ |a|+|b|+|c| := by linarith [abs_add_le a b]
  have hp0 := abs_nonneg phi
  have hbound : |phi| ≤ 10*Real.sqrt (d*s) := by linarith
  have hmul := mul_le_mul hbound hbound hp0 (by positivity)
  nlinarith [sq_abs phi]

theorem cubic_projected_response_payment {d s phi r hess : ℝ}
    (hphi : phi^2 ≤ 100*d*s) (hr : r = 3*phi)
    (hh : hess = 36*s) : r^2 ≤ 25*d*hess := by
  rw [hr,hh]
  nlinarith

end KLSConstantImprovement.OriginalCubicResponseProjectionScalar
#print axioms KLSConstantImprovement.OriginalCubicResponseProjectionScalar.regression_shuffle_charge
#print axioms KLSConstantImprovement.OriginalCubicResponseProjectionScalar.cubic_projection_bound
#print axioms KLSConstantImprovement.OriginalCubicResponseProjectionScalar.cubic_projected_response_payment
