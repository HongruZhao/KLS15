import Mathlib

/-!
Finite/scalar consequences of the same-source quadratic connection
identity. Actual canonical source/PDE, trace IBP, domain and field
identification remain explicit analytic inputs. No numerical response
cap or unconditional Poincare endpoint is stated here.
-/

namespace QuadraticRowSourceConnectionCharge

theorem compensated_generator_nonneg
    (lf f r gamma p cross : ℝ)
    (hr : 0 ≤ r) (hg : 0 ≤ gamma) (hp : 0 ≤ p)
    (hcross : cross ^ 2 ≤ r * gamma)
    (hchain : lf + 3 * f = 2 * r + gamma + p + 4 * cross) :
    p + gamma / 2 ≤ lf + 3 * f + 6 * r := by
  have hyoung : 0 ≤ 8 * r + gamma / 2 + 4 * cross := by
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · have hc : cross = 0 := by nlinarith [sq_nonneg cross]
      simp only [← hr0, hc]
      linarith
    · have hmul : 0 ≤ r * (8 * r + gamma / 2 + 4 * cross) := by
        nlinarith [sq_nonneg (4 * r + cross)]
      by_contra hnot
      have hneg : 8 * r + gamma / 2 + 4 * cross < 0 := lt_of_not_ge hnot
      have hprod := mul_neg_of_pos_of_neg hrpos hneg
      linarith
  linarith

theorem source_connection_charge_eq
    (j r k cross : ℝ)
    (hchain : 3 * j = 2 * r + k + 4 * cross)
    (hcross : cross = j - r) : k = 2 * r - j := by
  linarith

theorem source_connection_charge_le_four
    (n j r k : ℝ)
    (hj : 0 ≤ j) (hr : r ≤ 2 * n)
    (hid : k = 2 * r - j) : k ≤ 4 * n := by
  linarith

theorem row_connection_retains_bl_deficit
    (u dq j r gamma p : ℝ)
    (hp : 0 ≤ p) (hid : gamma + p = 2 * r - j)
    (hbl : j = u + dq) :
    gamma + p = 2 * r - u - dq ∧ gamma ≤ 2 * r - u - dq := by
  constructor <;> linarith

end QuadraticRowSourceConnectionCharge

#print axioms QuadraticRowSourceConnectionCharge.compensated_generator_nonneg
#print axioms QuadraticRowSourceConnectionCharge.source_connection_charge_eq
#print axioms QuadraticRowSourceConnectionCharge.source_connection_charge_le_four
#print axioms QuadraticRowSourceConnectionCharge.row_connection_retains_bl_deficit
