import Mathlib

/-! Same geometric eta/b scalar graph; the extra identities come from
Aeta=b=grad_target(P/6). Actual source/domain/Gram inputs remain explicit.
No uniform both-slot/transpose norm cap or original CP claim follows. -/
namespace QuadraticGradientReferenceProjection

theorem quadratic_gradient_force_cross
    (m g s n k : ℝ) (hforce : m + s + n = g + k) :
    n - k = -(m - g) - s := by
  linarith

theorem eta_connection_loss_retains_three_skews
    (a b z s : ℝ) (htotal : a + b + 2 * z = s)
    (hgradient : z = -a - s) : b = a + 3 * s := by
  linarith

theorem quadratic_gradient_projection_loss_pays_skew
    (a b z s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hGram : z ^ 2 ≤ a * b) (hgradient : z = -a - s)
    (hloss : b = a + 3 * s) : s ≤ a := by
  have hmul : s * s ≤ a * s := by nlinarith
  rcases eq_or_lt_of_le hs with hzero | hpos
  · simpa [← hzero] using ha
  · exact (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [hmul])

theorem whole_cubic_transpose_credit
    (v m s a : ℝ) (hvariance : v / 36 = m - a)
    (hskew : s ≤ a) : v ≤ 36 * (m - s) := by
  linarith

end QuadraticGradientReferenceProjection

#print axioms QuadraticGradientReferenceProjection.quadratic_gradient_force_cross
#print axioms QuadraticGradientReferenceProjection.eta_connection_loss_retains_three_skews
#print axioms QuadraticGradientReferenceProjection.quadratic_gradient_projection_loss_pays_skew
#print axioms QuadraticGradientReferenceProjection.whole_cubic_transpose_credit
