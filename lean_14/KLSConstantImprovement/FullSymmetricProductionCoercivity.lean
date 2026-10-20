import Mathlib

/-!
Finite consequences of the full three-slot ordering identity.  The pointwise
tensor identity and the actual regular-source field/domain bindings are proved
in the companion paper note and remain explicit inputs here.  No source fields
are passed to another law, and no original-class CP endpoint is asserted.
-/

namespace KLSConstantImprovement.FullSymmetricProductionCoercivity

theorem ordering_from_full_generator
    (col row a aTranspose h ht : ℝ)
    (hc : col = a + h) (hr : row = aTranspose + ht)
    (hg : 9 * (a - aTranspose) = 3 * (col - row)) :
    2 * (col - row) = 3 * (h - ht) := by
  linarith

theorem symmetric_part_bound
    (col row a h ht : ℝ)
    (hc : col = a + h)
    (horder : 2 * (col - row) = 3 * (h - ht))
    (hht : 0 ≤ ht) : a ≤ row + h / 2 := by
  linarith

private theorem pairing_young_two
    (W a c : ℝ) (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hcs : c ^ 2 ≤ W * a) : 2 * c ≤ W + a := by
  by_contra hn
  have hgap : 0 < 2 * c - (W + a) := by linarith
  have hsum : 0 < 2 * c + (W + a) := by linarith
  have hp := mul_pos hgap hsum
  nlinarith [sq_nonneg (W - a)]

private theorem pairing_young_three
    (W a c : ℝ) (hW : 0 ≤ W) (ha : 0 ≤ a)
    (hcs : c ^ 2 ≤ W * a) : 4 * c ≤ 3 * a + 4 * W / 3 := by
  by_contra hn
  have hgap : 0 < 4 * c - (3 * a + 4 * W / 3) := by linarith
  have hsum : 0 < 4 * c + (3 * a + 4 * W / 3) := by linarith
  have hp := mul_pos hgap hsum
  nlinarith [sq_nonneg (3 * a - 4 * W / 3)]

theorem half_rate_production_lower
    (W col row a h ht c E PF L Xi : ℝ)
    (hW : 0 ≤ W) (ha : 0 ≤ a) (hcs : c ^ 2 ≤ W * a)
    (hc : col = a + h)
    (horder : 2 * (col - row) = 3 * (h - ht))
    (hE : E = 4 * W + a + h - 4 * c)
    (hXi : Xi = PF + E / 2 + 8 * L) :
    PF + W - row / 2 + h / 4 + 3 * ht / 4 + 8 * L ≤ Xi := by
  have hy := pairing_young_two W a c hW ha hcs
  linarith

theorem full_rate_production_lower
    (W col row a h ht c E PF L Xi : ℝ)
    (hW : 0 ≤ W) (ha : 0 ≤ a) (hcs : c ^ 2 ≤ W * a)
    (hc : col = a + h)
    (horder : 2 * (col - row) = 3 * (h - ht))
    (hE : E = 4 * W + a + h - 4 * c)
    (hXi : Xi = PF + E / 2 + 8 * L) :
    PF + 4 * W / 3 - row + 3 * ht / 2 + 8 * L ≤ Xi := by
  have hy := pairing_young_three W a c hW ha hcs
  linarith

theorem half_rate_actual_response_upper
    (W r cf row theta extra PF L h ht Xi MF : ℝ)
    (hrow : row ≤ theta)
    (htheta : theta + extra = 2 * r - 2 * cf)
    (hXi : PF + W - row / 2 + h / 4 + 3 * ht / 4 + 8 * L ≤ Xi)
    (hMF : MF = W + r - cf - (Xi + extra) / 2) :
    MF ≤ W / 2 + 3 * (r - cf) / 2 - 3 * extra / 4
      - PF / 2 - h / 8 - 3 * ht / 8 - 4 * L := by
  linarith

theorem full_rate_actual_response_upper
    (W r cf row theta extra PF L ht Xi MF : ℝ)
    (hrow : row ≤ theta)
    (htheta : theta + extra = 2 * r - 2 * cf)
    (hXi : PF + 4 * W / 3 - row + 3 * ht / 2 + 8 * L ≤ Xi)
    (hMF : MF = W + r - cf - (Xi + extra) / 2) :
    MF ≤ W / 3 + 2 * (r - cf) - extra
      - PF / 2 - 3 * ht / 4 - 4 * L := by
  linarith

end KLSConstantImprovement.FullSymmetricProductionCoercivity

#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.ordering_from_full_generator
#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.symmetric_part_bound
#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.half_rate_production_lower
#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.full_rate_production_lower
#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.half_rate_actual_response_upper
#print axioms KLSConstantImprovement.FullSymmetricProductionCoercivity.full_rate_actual_response_upper
