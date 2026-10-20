import Mathlib

/-!
Scalar consequences of the same random-row weighted endpoint
subtraction. Actual canonical source, weighted vector Bochners,
common cutoff/domain and tensor-slot identities remain explicit
analytic premises. No numerical response/variance cap is asserted.
-/
namespace WeightedEndpointConnection

theorem retains_signed_slot_difference
    (m p rk gc gr c q : ℝ)
    (hendpoint : m = p + 2 * rk - gc + c)
    (hhook : q = (gc + gr) / 2 - c) :
    m = p + 2 * rk - q - (gc - gr) / 2 := by
  linarith

theorem retains_skew_hook_credit
    (m p rk gc gr c q gsk : ℝ)
    (hendpoint : m = p + 2 * rk - gc + c)
    (hhook : q = (gc + gr) / 2 - c)
    (hskew : gsk / 2 ≤ q) :
    m ≤ p + 2 * rk - (gc - gr) / 2 - gsk / 2 := by
  linarith

theorem same_connection_completed_square
    (m w theta ellc ellk p r2 k2 rc rk c center : ℝ)
    (hwhole : 2 * m = w + theta + 2 * ellc - p -
      (r2 - 2 * rc + w) - (r2 - 2 * rk + k2))
    (hendpoint : m = p + 2 * rk - k2 + c)
    (hcenter : center = r2 - rc - 2 * rk + w / 4 + ellk + k2) :
    3 * m = w / 2 + theta + 2 * ellc + 2 * ellk + c - 2 * center := by
  linarith

theorem full_tensor_curl_charge
    (w q d : ℝ) (hw : 0 ≤ w) (hq : 0 ≤ q)
    (hcurl : d ^ 2 ≤ 2 * w * q) : 2 * d - q ≤ 2 * w := by
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · have hd : d = 0 := by nlinarith [sq_nonneg d]
    simp only [← hq0, hd]
    linarith
  · have hmul : 0 ≤ q * (q - 2 * d + 2 * w) := by
      nlinarith [sq_nonneg (q - d)]
    by_contra hnot
    have hneg : q - 2 * d + 2 * w < 0 := by linarith
    have hprod := mul_neg_of_pos_of_neg hqpos hneg
    linarith

end WeightedEndpointConnection

#print axioms WeightedEndpointConnection.retains_signed_slot_difference
#print axioms WeightedEndpointConnection.retains_skew_hook_credit
#print axioms WeightedEndpointConnection.same_connection_completed_square
#print axioms WeightedEndpointConnection.full_tensor_curl_charge
