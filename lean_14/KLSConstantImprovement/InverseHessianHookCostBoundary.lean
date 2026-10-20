import Mathlib

/-! Scalar bookkeeping of the genuine Gamma-product inverse-H hook
obstruction. Original density, source, adjoint and L2 norm identifications
are explicit analytic bindings in the companion note. No response cap. -/
namespace KLSConstantImprovement.InverseHessianHookCostBoundary

theorem gamma_four_inverse_hook_calibration :
    (12/(4-2:ℝ)+6/(4-1:ℝ))=8 ∧
    ((-2/4:ℝ)^2)/8=1/32 ∧
    (1/32:ℝ)<1/17 := by norm_num

theorem inverse_hook_cost_lower {k cost : ℝ} (hk : 0<k)
    (hcost : cost=12*k+6*k/(k+1)) :
    12*k<cost := by
  have hd : 0<k+1 := by linarith
  have hp : 0<6*k/(k+1) := div_pos (by positivity) hd
  linarith

theorem inverse_hook_cost_unbounded_bookkeeping {k bound cost : ℝ}
    (hk : 0<k) (hbound : bound≤12*k)
    (hcost : cost=12*k+6*k/(k+1)) :
    bound<cost := by
  exact hbound.trans_lt (inverse_hook_cost_lower hk hcost)

end KLSConstantImprovement.InverseHessianHookCostBoundary
#print axioms KLSConstantImprovement.InverseHessianHookCostBoundary.gamma_four_inverse_hook_calibration
#print axioms KLSConstantImprovement.InverseHessianHookCostBoundary.inverse_hook_cost_lower
#print axioms KLSConstantImprovement.InverseHessianHookCostBoundary.inverse_hook_cost_unbounded_bookkeeping
