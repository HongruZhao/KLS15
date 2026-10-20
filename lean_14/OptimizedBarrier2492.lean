import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact scalar arithmetic for an improved Section 4 cubic barrier.
No measure, Appell, Hodge, operator, or global Poincare theorem is asserted here.
-/
noncomputable section
namespace OptimizedBarrier2492

def B : ℝ := 121 / 4
def K : ℝ := 11123 / 500
def R : ℝ := 31 / 125
def r : ℝ := 2750 / 11123
def delta : ℝ := 7121 / 30250

def a : ℝ := 431 / 200
def b : ℝ := 62 / 625
def bu : ℝ := 31 / 250
def A : ℝ := 6341 / 1000
def alpha : ℝ := 4341 / 8341
def P : ℝ := 48284943 / 17974855
def Q : ℝ := 12804921628 / 581037187875

def w (z : ℝ) : ℝ := (a * z + b) / (a + b)
def U (z : ℝ) : ℝ := P * z + Q - (P + Q) * w z ^ 3
def Up (z : ℝ) : ℝ := P - 3 * a / (a + b) * (P + Q) * w z ^ 2

theorem r_sq : r ^ 2 = B / K ^ 2 := by norm_num [r, B, K]
theorem r_majorant : 0 < r ∧ r < R := by norm_num [r, R]
theorem delta_range : 0 < delta ∧ delta < 1 / 2 := by norm_num [delta]
theorem delta_eq : delta = K / B - 1 / 2 := by norm_num [delta, K, B]
theorem alpha_range : 0 < alpha ∧ alpha < 1 := by norm_num [alpha]
theorem coefficient_A : A = 4 / (1 - alpha) - 2 := by norm_num [A, alpha]
theorem coefficient_a : a = 2 + 5 * R / 8 := by norm_num [a, R]
theorem coefficient_b : b = 2 * R / 5 := by norm_num [b, R]
theorem coefficient_bu : bu = R / 2 := by norm_num [bu, R]
theorem coefficient_c : 3 * a = A + R / 2 := by norm_num [a, A, R]
theorem coefficient_P : 2 * a * P = alpha * K := by norm_num [a, P, alpha, K]
theorem coefficient_Q : 3 * a * Q + bu = b * P := by norm_num [a, Q, bu, b, P]
theorem P_Q_positive : 0 < P ∧ 0 < Q := by norm_num [P, Q]

theorem barrier_identity (z : ℝ) :
    (a * z + b) * Up z = 3 * a * U z + bu - alpha * K * z := by
  norm_num [a, b, Up, U, w, P, Q, bu, alpha, K]
  ring

theorem barrier_at_one : U 1 = 0 := by norm_num [U, w, a, b, P, Q]
theorem barrier_endpoint_above_one : 1 < U (57 / 100) := by
  norm_num [U, w, a, b, P, Q]
theorem barrier_endpoint_derivative_negative : Up (57 / 100) < 0 := by
  norm_num [Up, w, a, b, P, Q]

def s : ℝ := 598 / 25
def Delta : ℝ := s ^ 2 - K * s - 2

theorem scalar_delta_positive : 0 < Delta := by norm_num [Delta, s, K]
theorem scalar_margin_positive : 0 < Delta ^ 2 - 2 * B * s := by
  norm_num [Delta, s, K, B]
theorem scalar_q_epsilon (q epsilon : ℝ)
    (hq : q = Delta / (K * s)) (he : epsilon = B / (K ^ 2 * s)) :
    0 < q ∧ 0 < epsilon ∧ 2 * epsilon < q ^ 2 := by
  rw [hq, he]
  norm_num [Delta, s, K, B]
theorem improved_poincare_constant : 1 + s = 623 / 25 := by norm_num [s]
theorem improved_strictly_below_25 : 1 + s < 25 := by norm_num [s]
theorem improved_strictly_below_2495 : 1 + s < 499 / 20 := by norm_num [s]

#print axioms barrier_identity
#print axioms barrier_endpoint_above_one
#print axioms scalar_margin_positive
end OptimizedBarrier2492
