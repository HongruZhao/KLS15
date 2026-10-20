import KLSConstantImprovement.QuarticM48Support20261020
/-! The raw401.3023465 theorem for the original admissible laws discharges
both analytic inputs of the rank-four generator head. The resulting
all-rank weighted budget has no additional cubic or quartic hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM48Weighted20261020
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget
open QuarticM48Profile20261020Data QuarticM48Profile20261020
open QuarticM48Support20261020
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x,(f x)^2 ∂μ) :=
  QuarticM48Profile20261020.weighted_budget original_raw quartic_support N hμ hf

theorem weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  QuarticM48Profile20261020.weighted_budget_norm_sq original_raw quartic_support N hμ f

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 :=
  QuarticM48Profile20261020.raw_budget_norm_sq original_raw quartic_support N hμ f

end KLSConstantImprovement.QuarticM48Weighted20261020
#print axioms KLSConstantImprovement.QuarticM48Weighted20261020.weighted_budget
#print axioms KLSConstantImprovement.QuarticM48Weighted20261020.raw_budget_norm_sq
#print axioms KLSConstantImprovement.QuarticM48Weighted20261020.weighted_budget_norm_sq
