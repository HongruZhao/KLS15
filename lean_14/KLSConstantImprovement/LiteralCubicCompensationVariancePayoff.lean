import KLSConstantImprovement.RelaxedLiteralCubicRayleighPayoff

/-! A conditional literal-cubic compensation variance route. This s is
Var(X dot e), not the rejected Gaussian-damping K8 quantity. Its uniform
ten-per-N cap remains OPEN. Actual polynomial/kernel/Bochner/covariance
bindings are the companion paper inputs; no universal improvement is claimed. -/
noncomputable section
namespace KLSConstantImprovement.LiteralCubicCompensationVariancePayoff

theorem covariance_young {V s c : ℝ}
    (hV : 0 ≤ V) (hs : 0 ≤ s) (hc : c^2 ≤ V*s) :
    5*c ≤ (7/16:ℝ)*V+(100/7:ℝ)*s := by
  have hb : 0 ≤ (7/16:ℝ)*V+(100/7:ℝ)*s := by positivity
  by_contra h
  have hbad : (7/16:ℝ)*V+(100/7:ℝ)*s < 5*c := lt_of_not_ge h
  have hsum : 0 < 5*c+((7/16:ℝ)*V+(100/7:ℝ)*s) := by linarith
  have hstrict := mul_pos (sub_pos.mpr hbad) hsum
  nlinarith [sq_nonneg ((7/16:ℝ)*V-(100/7:ℝ)*s)]

theorem variance_from_polynomial_compensation {V J s c : ℝ}
    (hV : 0 ≤ V) (hs : 0 ≤ s) (hc : c^2 ≤ V*s)
    (hpoly : V-5*c+6*s=6*J) :
    V ≤ (32/3:ℝ)*J+(928/63:ℝ)*s := by
  have hy := covariance_young hV hs hc
  linarith

theorem conditional_raw_cubic_cap {N V J q s c : ℝ}
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hc : c^2 ≤ V*s) (hpoly : V-5*c+6*s=6*J)
    (hmain : Real.sqrt 2*J+q ≤ (12+9*Real.sqrt 2)*N)
    (hcompensation : s ≤ 10*N) :
    V ≤ (105152/315:ℝ)*N ∧ V ≤ 334*N ∧ V ≤ 336*N := by
  have hv := variance_from_polynomial_compensation hV hs hc hpoly
  have hj := RelaxedLiteralCubicRayleighPayoff.rational_trace_support hN hq hmain
  constructor
  · linarith
  constructor <;> nlinarith

end KLSConstantImprovement.LiteralCubicCompensationVariancePayoff
#print axioms KLSConstantImprovement.LiteralCubicCompensationVariancePayoff.covariance_young
#print axioms KLSConstantImprovement.LiteralCubicCompensationVariancePayoff.variance_from_polynomial_compensation
#print axioms KLSConstantImprovement.LiteralCubicCompensationVariancePayoff.conditional_raw_cubic_cap
