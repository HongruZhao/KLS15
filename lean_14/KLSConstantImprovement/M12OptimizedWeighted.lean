import KLSConstantImprovement.M12OptimizedSupport
/-! The raw401.317 theorem for the original admissible laws discharges
both analytic inputs of the rank-four generator head. The resulting
all-rank weighted budget has no additional cubic or quartic hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.M12OptimizedWeighted
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget
open M12OptimizedProfileData M12OptimizedProfile
open M12OptimizedSupport
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x,(f x)^2 ∂μ) :=
  M12OptimizedProfile.weighted_budget original_raw quartic_support N hμ hf

theorem weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  M12OptimizedProfile.weighted_budget_norm_sq original_raw quartic_support N hμ f

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 :=
  M12OptimizedProfile.raw_budget_norm_sq original_raw quartic_support N hμ f

end KLSConstantImprovement.M12OptimizedWeighted
#print axioms KLSConstantImprovement.M12OptimizedWeighted.weighted_budget
#print axioms KLSConstantImprovement.M12OptimizedWeighted.raw_budget_norm_sq
#print axioms KLSConstantImprovement.M12OptimizedWeighted.weighted_budget_norm_sq
