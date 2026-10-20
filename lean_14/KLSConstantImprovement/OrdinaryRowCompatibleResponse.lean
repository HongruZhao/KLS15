import Mathlib

/-! Scalar consequences of the same actual ordinary-source row form.
Canonical field, ordinary L0 weak rows, geometric A datum, norm
identifications and metric excess remain explicit analytic inputs.
-/
namespace OrdinaryRowCompatibleResponse

theorem right_metric_norm_eq
    (br uh j pair h u0 : ℝ)
    (hexpand : br = 4 * uh + j - 4 * pair)
    (hform : h + uh = u0) (hpair : pair = u0) :
    br = j - 4 * h := by
  linarith

theorem ordinary_gradient_loss_le_quarter
    (br j h : ℝ) (hbr : 0 ≤ br) (hid : br = j - 4 * h) :
    4 * h ≤ j := by
  linarith

theorem correlated_metric_response_payment
    (i wc br j h k r g : ℝ)
    (hriesz : i ≤ wc) (hmetric : wc ≤ br + k + 6 * g)
    (hright : br = j - 4 * h) (hk : k = 2 * r - j) :
    i ≤ 2 * r - 4 * h + 6 * g := by
  linarith

theorem correlated_metric_response_le_relaxed_gate
    (i r h g : ℝ) (hh : 0 ≤ h)
    (hpay : i ≤ 2 * r - 4 * h + 6 * g) :
    i ≤ 2 * r + 6 * g := by
  linarith

end OrdinaryRowCompatibleResponse

#print axioms OrdinaryRowCompatibleResponse.right_metric_norm_eq
#print axioms OrdinaryRowCompatibleResponse.ordinary_gradient_loss_le_quarter
#print axioms OrdinaryRowCompatibleResponse.correlated_metric_response_payment
#print axioms OrdinaryRowCompatibleResponse.correlated_metric_response_le_relaxed_gate
