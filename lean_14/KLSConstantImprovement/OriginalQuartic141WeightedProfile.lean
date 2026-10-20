import KLSConstantImprovement.Raw4047255Quartic141Profile
import KLSConstantImprovement.RawCubicQuarticAffineSupport
import KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint

/-! The raw404.7255 theorem for the original admissible laws discharges
both analytic inputs of the rank-four generator head. The resulting
all-rank weighted budget has no additional cubic or quartic hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.OriginalQuartic141WeightedProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget
open Raw4047255Quartic141ProfileData Raw4047255Quartic141Profile
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem original_raw : RawCubicWeightedBudget.UniversalRawCubicBound H :=
  OriginalCubic4047255OptimizedEndpoint.original_observation_raw4047255

theorem quartic_support :
    RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B := by
  have hH : 216 ≤ H := by norm_num [H]
  have hs : contact ∈ Ioo (0 : ℝ) 1 := by norm_num [contact]
  exact @RawCubicQuarticAffineSupport.normalized_support H contact hH (@original_raw) hs

theorem weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x,(f x)^2 ∂μ) :=
  Raw4047255Quartic141Profile.weighted_budget original_raw quartic_support N hμ hf

theorem weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  Raw4047255Quartic141Profile.weighted_budget_norm_sq original_raw quartic_support N hμ f

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 :=
  Raw4047255Quartic141Profile.raw_budget_norm_sq original_raw quartic_support N hμ f

end KLSConstantImprovement.OriginalQuartic141WeightedProfile
#print axioms KLSConstantImprovement.OriginalQuartic141WeightedProfile.original_raw
#print axioms KLSConstantImprovement.OriginalQuartic141WeightedProfile.quartic_support
#print axioms KLSConstantImprovement.OriginalQuartic141WeightedProfile.weighted_budget
#print axioms KLSConstantImprovement.OriginalQuartic141WeightedProfile.raw_budget_norm_sq
