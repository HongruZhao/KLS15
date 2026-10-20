import Mathlib
import FiniteDegreeCorrection

/-! A new quintic scalar barrier. This module does not assert the analytic
Appell criterion, its operator realization, or a global Poincare theorem. -/
noncomputable section
namespace Quintic24886

def B : ℝ := 121 / 4
def K : ℝ := 2221 / 100
def R : ℝ := 1 / 4
def r : ℝ := 550 / 2221
def delta : ℝ := 1417 / 6050
def a : ℝ := 77 / 36
def b : ℝ := 9 / 80
def cu : ℝ := 5 / 36
def A : ℝ := 1207 / 180
def alpha : ℝ := 847 / 1567
def c : ℝ := 308 / 45
def P : ℝ := 19989 / 7835
def Q : ℝ := 492237 / 19305440
def L : ℝ := 1540 / 1621
def xmax : ℝ := 3234 / 8105
def kappa : ℝ := 285296 / 21689875

def x (z : ℝ) : ℝ := L * (1 - z)
def W (v : ℝ) : ℝ := 1 - 16 / 5 * v + 88 / 25 * v ^ 2 -
    176 / 125 * v ^ 3 + 44 / 625 * v ^ 4 + kappa * v ^ 5
def Wp (v : ℝ) : ℝ := -16 / 5 + 176 / 25 * v -
    528 / 125 * v ^ 2 + 176 / 625 * v ^ 3 + 5 * kappa * v ^ 4
def Wpp (v : ℝ) : ℝ := 176 / 25 - 1056 / 125 * v +
    528 / 625 * v ^ 2 + 20 * kappa * v ^ 3

def U (z : ℝ) : ℝ := P * z + Q - (P + Q) * W (x z)
def Up (z : ℝ) : ℝ := P + (P + Q) * L * Wp (x z)
def Upp (z : ℝ) : ℝ := -(P + Q) * L ^ 2 * Wpp (x z)

theorem parameter_ranges :
    0 < r ∧ r < R ∧ 0 < alpha ∧ alpha < 1 ∧
    0 < delta ∧ delta < 1 / 2 ∧ 0 < P ∧ 0 < Q := by
  norm_num [r, R, alpha, delta, P, Q]
theorem r_sq : r ^ 2 = B / K ^ 2 := by norm_num [r, B, K]
theorem delta_eq : delta = K / B - 1 / 2 := by norm_num [delta, K, B]
theorem coefficient_A : A = 4 / (1 - alpha) - 2 := by norm_num [A, alpha]
theorem coefficient_a : a = 2 + 5 * R / 9 := by norm_num [a, R]
theorem coefficient_b : b = 9 * R / 20 := by norm_num [b, R]
theorem coefficient_cu : cu = 5 * R / 9 := by norm_num [cu, R]
theorem coefficient_c : c = A + cu := by norm_num [c, A, cu]
theorem coefficient_L : L = a / (a + b) := by norm_num [L, a, b]
theorem coefficient_P : (c - a) * P = alpha * K := by
  norm_num [c, a, P, alpha, K]
theorem coefficient_Q : c * Q + b = b * P := by norm_num [c, Q, b, P]

theorem x_range {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    0 ≤ x z ∧ x z ≤ xmax := by
  norm_num [x, L, xmax]
  constructor <;> linarith [hz.1, hz.2]

theorem x_upper_lt : xmax < 2 / 5 := by norm_num [xmax]

theorem Wpp_positive {v : ℝ} (hv : 0 ≤ v) (htop : v ≤ xmax) : 0 < Wpp v := by
  have hbase : 0 < (176 / 25 : ℝ) - 1056 / 125 * v := by
    have hmax := x_upper_lt
    linarith
  have h2 : 0 ≤ (528 / 625 : ℝ) * v ^ 2 := by positivity
  have h3 : 0 ≤ 20 * kappa * v ^ 3 := by unfold kappa; positivity
  unfold Wpp
  linarith

theorem barrier_residual_identity (z : ℝ) :
    (a * z + b) * Up z - c * U z - b + alpha * K * z =
    a * (P + Q) * (9 / 5) * kappa * (x z) ^ 4 * (xmax - x z) := by
  norm_num [a, b, Up, U, Wp, W, x, L, c, P, Q, alpha, K, kappa, xmax]
  ring

theorem barrier_residual_nonnegative {z : ℝ} (hz : z ∈ Set.Icc (29 / 50) 1) :
    0 ≤ (a * z + b) * Up z - c * U z - b + alpha * K * z := by
  rw [barrier_residual_identity]
  have hx := x_range hz
  have hlast : 0 ≤ xmax - x z := sub_nonneg.mpr hx.2
  norm_num [a, P, Q, kappa]
  positivity

theorem barrier_at_one : U 1 = 0 := by norm_num [U, W, x, L, P, Q]
theorem barrier_endpoint_above_one : 1 < U (29 / 50) := by
  norm_num [U, W, x, L, P, Q, kappa]
theorem barrier_endpoint_derivative_negative : Up (29 / 50) < 0 := by
  norm_num [Up, Wp, x, L, P, Q, kappa]

def s : ℝ := 11943 / 500
def Delta : ℝ := s ^ 2 - K * s - 2

theorem scalar_delta_positive : 0 < Delta := by norm_num [Delta, s, K]
theorem scalar_margin_positive : 0 < Delta ^ 2 - 2 * B * s := by
  norm_num [Delta, s, K, B]
theorem scalar_q_epsilon (q epsilon : ℝ)
    (hq : q = Delta / (K * s)) (he : epsilon = B / (K ^ 2 * s)) :
    0 < q ∧ 0 < epsilon ∧ 2 * epsilon < q ^ 2 := by
  rw [hq, he]
  norm_num [Delta, s, K, B]
theorem improved_constant : 1 + s = 12443 / 500 := by norm_num [s]
theorem improved_strictly_below_249 : 1 + s < 249 / 10 := by norm_num [s]

#print axioms barrier_residual_identity
#print axioms barrier_residual_nonnegative
#print axioms scalar_margin_positive
end Quintic24886
