import Mathlib

/-! Exact proposed scalar data for the variable-alpha target24. This file
certifies endpoint and normalization arithmetic only. The barrier interval
inequalities and its inverse regularity are separate proof obligations. -/
noncomputable section
namespace VariableAlpha24
set_option maxHeartbeats 1000000

def B : ℝ := 57/2
def K : ℝ := 2133/100
def delta : ℝ := K/B-1/2
def alphaZero : ℝ := 99999/100000
def seedT : ℝ := 18/25
def commonT : ℝ := 13/20
def seedC : ℝ := 43259/100000
def commonC : ℝ := 8661/20000
def seedR : ℝ := 74927/50000
def commonR : ℝ := 25029/100000

def seedV (t : ℝ) : ℝ := 8228/3125-99963/50000*t+91727/100000*t^2-
  45111/50000*t^3+2793/10000*t^4+2583/4000*t^5-213249/100000*t^6+
  48041/20000*t^7-116239/100000*t^8
def commonV (t : ℝ) : ℝ := 307869/100000-8668/3125*t+15879/12500*t^2-
  1657/1250*t^3+2777/2500*t^4-29807/20000*t^5+5639/4000*t^6-
  80923/100000*t^7

theorem B_positive : 0 < B := by norm_num [B]
theorem K_positive : 0 < K := by norm_num [K]
theorem delta_range : 0 < delta ∧ delta < 1/2 := by norm_num [delta,B,K]
theorem alphaZero_range : 0 < alphaZero ∧ alphaZero < 1 := by norm_num [alphaZero]
theorem seedT_range : 0 < seedT ∧ seedT < 1 := by norm_num [seedT]
theorem commonT_range : 0 < commonT ∧ commonT < 1 := by norm_num [commonT]
theorem seedC_positive : 0 < seedC := by norm_num [seedC]
theorem commonC_positive : 0 < commonC := by norm_num [commonC]
theorem seedR_positive : 0 < seedR := by norm_num [seedR]
theorem commonR_positive : 0 < commonR := by norm_num [commonR]
theorem seedR_majorant : 64 ≤ seedR^2*B := by norm_num [seedR,B]
theorem commonR_majorant : B ≤ commonR^2*K^2 := by norm_num [commonR,B,K]

theorem seed_endpoint_above_one : 1 < seedT^2*(seedV seedT)^2 := by
  norm_num [seedT,seedV]
theorem common_endpoint_above_one : 1 < commonT^2*(commonV commonT)^2 := by
  norm_num [commonT,commonV]

theorem seed_zero_strict_margin :
    (17+seedR)*(seedV 0)^2 < alphaZero*(9/2)*B := by
  norm_num [seedV,seedR,alphaZero,B]
theorem common_zero_strict_margin :
    (2+commonR)*(commonV 0)^2 < alphaZero*K := by
  norm_num [commonV,commonR,alphaZero,K]

def s : ℝ := 23
def Delta : ℝ := s^2-K*s-2
theorem scalar_delta_positive : 0 < Delta := by norm_num [Delta,s,K]
theorem scalar_margin_exact : Delta^2-2*B*s = 146881/10000 := by
  norm_num [Delta,s,K,B]
theorem scalar_margin_positive : 0 < Delta^2-2*B*s := by
  rw [scalar_margin_exact]
  norm_num
theorem target_integer_constant : 1+s = 24 := by norm_num [s]

end VariableAlpha24
#print axioms VariableAlpha24.seed_endpoint_above_one
#print axioms VariableAlpha24.common_endpoint_above_one
#print axioms VariableAlpha24.seed_zero_strict_margin
#print axioms VariableAlpha24.common_zero_strict_margin
#print axioms VariableAlpha24.scalar_margin_positive
