import Mathlib

/-! Finite consequences of the actual SAME scalar graph projection.
The source isometry/field/domain bindings and defect Gram are explicit
paper inputs, not assumed all-matrix lifts or a uniform N budget. -/
namespace CompatibleConnectionProjection

theorem connection_cost_le_paid_source_curvature
    (c2 src : ℝ) (hc : 0 ≤ c2) (hs : 0 ≤ src)
    (hRiesz : c2 ^ 2 ≤ src * c2) : c2 ≤ src := by
  nlinarith

theorem same_connection_projection_total_defect
    (m i src c2 n k s ch d2 : ℝ)
    (hordinary : d2 = m - s + ch)
    (hcurvature : ch = src + 2 * n)
    (hscalar : d2 = i + 2 * k + c2) :
    (m - i) + (src - c2) + 2 * (n - k) = s := by
  linarith

theorem symmetric_response_equal_projection_losses
    (a b z : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hGram : z ^ 2 ≤ a * b) (hsym : a + b + 2 * z = 0) :
    a = b ∧ z = -a := by
  have hsq : (a - b) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b)]
  have heq : a = b := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  constructor
  · exact heq
  · linarith

theorem paired_projection_cross_lower
    (a b z s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htotal : a + b + 2 * z = s) : -z ≥ -s / 2 := by
  linarith

end CompatibleConnectionProjection

#print axioms CompatibleConnectionProjection.connection_cost_le_paid_source_curvature
#print axioms CompatibleConnectionProjection.same_connection_projection_total_defect
#print axioms CompatibleConnectionProjection.symmetric_response_equal_projection_losses
#print axioms CompatibleConnectionProjection.paired_projection_cross_lower
