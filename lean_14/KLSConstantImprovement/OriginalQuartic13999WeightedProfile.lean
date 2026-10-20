import KLSConstantImprovement.OriginalQuartic13999Support
/-! The raw401.317 theorem for the original admissible laws discharges
both analytic inputs of the rank-four generator head. The resulting
all-rank weighted budget has no additional cubic or quartic hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.OriginalQuartic13999WeightedProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget
open Raw401317Quartic13999ProfileData Raw401317Quartic13999Profile
open OriginalQuartic13999Support
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x,(f x)^2 ∂μ) :=
  Raw401317Quartic13999Profile.weighted_budget original_raw quartic_support N hμ hf

theorem weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  Raw401317Quartic13999Profile.weighted_budget_norm_sq original_raw quartic_support N hμ f

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 :=
  Raw401317Quartic13999Profile.raw_budget_norm_sq original_raw quartic_support N hμ f

end KLSConstantImprovement.OriginalQuartic13999WeightedProfile
#print axioms KLSConstantImprovement.OriginalQuartic13999WeightedProfile.weighted_budget
#print axioms KLSConstantImprovement.OriginalQuartic13999WeightedProfile.raw_budget_norm_sq
#print axioms KLSConstantImprovement.OriginalQuartic13999WeightedProfile.weighted_budget_norm_sq
