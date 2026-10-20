import Mathlib

/-! Exact consequences of E(CH)=L/2 for the actual ordinary-source
quadratic rows. Same-law/domain/expectation identifications are analytic
inputs; no extra-H response cost or cross sign is asserted. -/
namespace OrdinaryRowRightRegression

theorem right_residual_norm_eq
    (res br b2 : ℝ) (hexpand : res = br - b2 / 4) :
    br = b2 / 4 + res := by
  linarith

theorem gradient_and_regression_charge_le_position
    (res br b2 j h : ℝ) (hres : 0 ≤ res)
    (hexpand : res = br - b2 / 4)
    (hright : br = j - 4 * h) :
    4 * h + b2 / 4 ≤ j := by
  linarith

end OrdinaryRowRightRegression

#print axioms OrdinaryRowRightRegression.right_residual_norm_eq
#print axioms OrdinaryRowRightRegression.gradient_and_regression_charge_le_position
