import KLSConstantImprovement.AcceptedMix96Data
import KLSConstantImprovement.PositiveRawBudgetLinearCombination
import KLSConstantImprovement.QuarticM48Weighted20261020
import KLSConstantImprovement.QuarticM32Weighted20261020

/-! Original-law weighted budget obtained only by an exact nonnegative
combination of the two frozen original-law weighted budgets (after both merger acceptance chains pass), then by discarding a
nonnegative post-head remainder. No new analytic hypothesis is used. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.AcceptedMix96Weighted
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open AcceptedMix96Data
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem rawMix_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (g : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,rawMix d*K⁻¹^d*actualAppellEnergy μ g d/(d.factorial : ℝ)^2) ≤
      C*‖g‖^2 := by
  have h0 : (∑ d ∈ Finset.Icc 2 N,
      QuarticM48Profile20261020Data.t d*K⁻¹^d*actualAppellEnergy μ g d/(d.factorial : ℝ)^2) ≤
      QuarticM48Profile20261020Data.C*‖g‖^2 := by
    simpa only [K_eq] using QuarticM48Weighted20261020.raw_budget_norm_sq N hμ g
  have h1 : (∑ d ∈ Finset.Icc 2 N,
      QuarticM32Profile20261020Data.t d*L⁻¹^d*actualAppellEnergy μ g d/(d.factorial : ℝ)^2) ≤
      QuarticM32Profile20261020Data.C*‖g‖^2 := by
    simpa only [L_eq] using QuarticM32Weighted20261020.raw_budget_norm_sq N hμ g
  have he := PositiveRawBudgetLinearCombination.sum_le_of_two_budgets K L
    QuarticM48Profile20261020Data.C QuarticM32Profile20261020Data.C a (‖g‖^2)
    QuarticM48Profile20261020Data.t QuarticM32Profile20261020Data.t
    (fun d=>actualAppellEnergy μ g d) (ne_of_gt K_positive) (ne_of_gt L_positive)
    (by norm_num [a]) N h0 h1
  simpa only [rawMix,C_eq] using he

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (g : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ g d/(d.factorial : ℝ)^2) ≤
      C*‖g‖^2 := by
  have he := PositiveRawBudgetLinearCombination.sum_mono K t rawMix
    (fun d=>actualAppellEnergy μ g d) K_positive.le N t_le_rawMix
    (fun d _=>actualAppellEnergy_nonneg μ g d)
  exact he.trans (rawMix_budget_norm_sq N hμ g)

end KLSConstantImprovement.AcceptedMix96Weighted
#print axioms KLSConstantImprovement.AcceptedMix96Weighted.rawMix_budget_norm_sq
#print axioms KLSConstantImprovement.AcceptedMix96Weighted.raw_budget_norm_sq
