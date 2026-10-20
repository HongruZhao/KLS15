import Mathlib

/-! Same actual regular-source response chi=2eta-b. Graph/BL/regression
identifications remain explicit inputs; no weighted gradient cap follows. -/
namespace GeometricResponseFunctionContraction

theorem function_norm_and_BL_charge
    (chi2 eta2 j u0 : ℝ)
    (hexpand : chi2 = 4 * eta2 - 4 * j + u0) :
    chi2 + 4 * (j - eta2) = u0 := by
  ring_nf at hexpand ⊢
  linarith

theorem regressed_function_norm_le_quadratic_residual
    (chi0 delta u0 b2 : ℝ) (hdelta : 0 ≤ delta)
    (hid : chi0 + 4 * delta = u0 - b2 / 4) :
    chi0 ≤ u0 - b2 / 4 := by
  linarith

end GeometricResponseFunctionContraction

#print axioms GeometricResponseFunctionContraction.function_norm_and_BL_charge
#print axioms GeometricResponseFunctionContraction.regressed_function_norm_le_quadratic_residual
