import Mathlib

/-! Exact scalar obstruction for the actual mixed-product damping example.
The literal original-law centering, whitening, and moment identification is
the separate analytic/checker bridge, not silently claimed by this module.
This rejects an auxiliary K8 nomination; it changes no CP or 1D-four result. -/
noncomputable section
namespace KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift

theorem mixed_product_requires_trace_six {s k : ℝ}
    (h : 0 ≤ (-60*s-6*k)+8*(12*s)) : k ≤ 6*s := by
  linarith

theorem actual_parameter_trace_exceeds_six :
    (6 : ℝ)*(379/8) < 1698645/5944 := by norm_num

theorem actual_parameter_damping_eight_slack_negative :
    (-13543845/2972 : ℝ)+8*(1137/2) < 0 := by norm_num

theorem actual_parameter_required_coefficient {K : ℝ}
    (h : (-13543845/2972 : ℝ)+K*(1137/2) ≥ 0) :
    (4514615/563194 : ℝ) ≤ K := by
  linarith

end KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift.mixed_product_requires_trace_six
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift.actual_parameter_trace_exceeds_six
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift.actual_parameter_damping_eight_slack_negative
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DampingProductLift.actual_parameter_required_coefficient
