import Mathlib

/-!
The actual target-closed skew response supplies a balanced derivative
hook price and a same-response null correction. Analytic closure,
three-slot whitening, cutoff/domain and Riesz identifications are
explicit inputs to these finite consequences.
-/
namespace TargetClosedSkewResponse

theorem balanced_derivative_price
    (q s derivative hook : ℝ)
    (hcost : q = s + derivative)
    (hclosed : derivative = 3 * hook / 8) :
    q = s + 3 * hook / 8 := by
  linarith

theorem same_response_curl_cost
    (i ce q d cross lambda : ℝ)
    (hcross : cross = d / 2)
    (hriesz : i ≤ ce - 2 * lambda * cross + lambda ^ 2 * q) :
    i ≤ ce - lambda * d + lambda ^ 2 * q := by
  rw [hcross] at hriesz
  nlinarith

theorem corrected_cost_charge
    (i ce q d : ℝ) (hq : 0 < q)
    (hcost : ∀ lambda : ℝ, i ≤ ce - lambda * d + lambda ^ 2 * q) :
    i ≤ ce - d ^ 2 / (4 * q) := by
  have hne : q ≠ 0 := ne_of_gt hq
  have hid : ce - (d / (2 * q)) * d + (d / (2 * q)) ^ 2 * q =
      ce - d ^ 2 / (4 * q) := by
    field_simp
    <;> ring
  simpa only [hid] using hcost (d / (2 * q))

end TargetClosedSkewResponse

#print axioms TargetClosedSkewResponse.balanced_derivative_price
#print axioms TargetClosedSkewResponse.same_response_curl_cost
#print axioms TargetClosedSkewResponse.corrected_cost_charge
