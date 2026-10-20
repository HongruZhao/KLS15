import Mathlib

/-! Exact arithmetic sharpening of the existing two-head operator threshold.
The analytic observation budget and its two low-degree caps are unchanged.
This module certifies only the scalar premises of that operator theorem. -/

noncomputable section
namespace KLSImprovement.OperatorThreshold14992816

def rate : ℝ := 67 / 5
def budget : ℝ := 6 / 125
def firstCap : ℝ := 2 / rate ^ 2
def secondCap : ℝ := (49 / 2) / rate ^ 3
def threshold : ℝ := 13053 / 12500
def secondLower : ℝ := threshold ^ 2 - firstCap
def thirdLower : ℝ := secondLower * (threshold - firstCap / threshold) - secondCap
def residualRatio : ℝ := threshold - firstCap / threshold - secondCap / secondLower -
  (budget - firstCap - secondCap) / thirdLower
def bound : ℝ := 937051 / 62500

theorem rate_positive : 0 < rate := by norm_num [rate]
theorem budget_positive : 0 < budget := by norm_num [budget]
theorem threshold_gt_one : 1 < threshold := by norm_num [threshold]
theorem caps_nonneg : 0 ≤ firstCap ∧ 0 ≤ secondCap := by
  norm_num [firstCap, secondCap, rate]
theorem caps_sum_le_budget : firstCap + secondCap ≤ budget := by
  norm_num [firstCap, secondCap, rate, budget]
theorem secondLower_ge_threshold : threshold ≤ secondLower := by
  norm_num [secondLower, firstCap, threshold, rate]
theorem thirdLower_ge_second : secondLower ≤ thirdLower := by
  norm_num [thirdLower, secondLower, firstCap, secondCap, threshold, rate]
theorem residualRatio_gt_one : 1 < residualRatio := by
  norm_num [residualRatio, thirdLower, secondLower, firstCap, secondCap,
    threshold, rate, budget]
theorem cost_identity :
    residualRatio + firstCap / threshold + secondCap / secondLower +
      (budget - firstCap - secondCap) / thirdLower = threshold := by
  unfold residualRatio
  ring
theorem endpoint_value : 1 + rate * threshold = bound := by
  norm_num [rate, threshold, bound]
theorem improves_previous_endpoint : bound < (149963 : ℝ) / 10000 := by
  norm_num [bound]

end KLSImprovement.OperatorThreshold14992816

#print axioms KLSImprovement.OperatorThreshold14992816.residualRatio_gt_one
#print axioms KLSImprovement.OperatorThreshold14992816.improves_previous_endpoint
