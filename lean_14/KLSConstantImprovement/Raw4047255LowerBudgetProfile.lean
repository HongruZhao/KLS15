import KLSConstantImprovement.LongPrefixWeightedProfile
import KLSConstantImprovement.LowerBudgetProfileMonotonicity
import KLSConstantImprovement.OriginalCubic4047255OptimizedEndpoint

/-! The proved original-law raw404.7255 bound lowers the full all-rank
weighted budget, retaining the old degree weights and every infinite-tail
certificate. The simple quadratic/cubic head replaces the old correlated
seed head. No additional cubic observation augmentation is needed.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.Raw4047255LowerBudgetProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open TriplePositiveEnergyWeightedBudget LowerBudgetProfileMonotonicity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def C : ℝ := 48975995049/1000000000000
def H : ℝ := 809451/2000
abbrev K := LongPrefixWeightedProfileData.K
abbrev c := LongPrefixWeightedProfileData.c
abbrev t := LongPrefixWeightedProfileData.t
abbrev young := LongPrefixWeightedProfileData.young
def profile : Parameters := withBudget LongPrefixWeightedProfileData.profile C

theorem scalar_certificate : RawCubicWeightedBudget.ScalarCertificate profile H := by
  have hOld := LongPrefixWeightedProfile.scalar_certificate
  have hD : C ≤ LongPrefixWeightedProfileData.C := by
    norm_num [C, LongPrefixWeightedProfileData.C]
  refine {
    K_positive := hOld.K_positive
    c_positive := hOld.c_positive
    base_budget := by
      norm_num [profile, withBudget, LongPrefixWeightedProfileData.profile,
        C, LongPrefixWeightedProfileData.K, LongPrefixWeightedProfileData.t]
    young_positive := hOld.young_positive
    weight_positive := hOld.weight_positive
    alpha_nonneg := hOld.alpha_nonneg
    alpha_lt_one := hOld.alpha_lt_one
    theta_nonneg := hOld.theta_nonneg
    theta_le_one := hOld.theta_le_one
    lambda_nonneg := hOld.lambda_nonneg
    lambda_le_one := hOld.lambda_le_one
    lambda_boundary := hOld.lambda_boundary
    zeta_nonneg := hOld.zeta_nonneg
    zeta_cap := hOld.zeta_cap
    quadratic_payment := hOld.quadratic_payment
    terminal_payment := hOld.terminal_payment
    coefficient_lower := ?_
    head_nonneg := ?_
    third_nonneg := ?_
    head_margin := ?_ }
  · intro d hd
    exact (hOld.coefficient_lower d hd).trans
      (coefficient_le_lowerBudget LongPrefixWeightedProfileData.profile
        hOld.K_positive.le hD d (hOld.young_positive d (by omega)))
  · change 0 ≤ LongPrefixWeightedProfileData.c +
      head (withBudget LongPrefixWeightedProfileData.profile C)
    rw [head_withBudget, LongPrefixWeightedProfileData.head_value]
    norm_num [LongPrefixWeightedProfileData.profile, LongPrefixWeightedProfileData.c,
      LongPrefixWeightedProfileData.K, LongPrefixWeightedProfileData.C,
      LongPrefixWeightedProfileData.young, C]
  · change 0 ≤ LongPrefixWeightedProfileData.c -
      coefficient (withBudget LongPrefixWeightedProfileData.profile C) 3
    rw [coefficient_withBudget, LongPrefixWeightedProfileData.coefficient_three]
    norm_num [LongPrefixWeightedProfileData.profile, LongPrefixWeightedProfileData.c,
      LongPrefixWeightedProfileData.K, LongPrefixWeightedProfileData.C,
      LongPrefixWeightedProfileData.young, C]
  · change (LongPrefixWeightedProfileData.c +
        head (withBudget LongPrefixWeightedProfileData.profile C)) *
        (2 * t 2 / K ^ 2) +
      (LongPrefixWeightedProfileData.c -
        coefficient (withBudget LongPrefixWeightedProfileData.profile C) 3) *
        (t 3 * H / (36 * K ^ 3)) < LongPrefixWeightedProfileData.c * C
    rw [head_withBudget, coefficient_withBudget, LongPrefixWeightedProfileData.head_value,
      LongPrefixWeightedProfileData.coefficient_three]
    norm_num [LongPrefixWeightedProfileData.profile, LongPrefixWeightedProfileData.c,
      LongPrefixWeightedProfileData.K, LongPrefixWeightedProfileData.C,
      LongPrefixWeightedProfileData.young, LongPrefixWeightedProfileData.t,
      t, young, K, C, H]

theorem weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C * (∫ x, (f x) ^ 2 ∂μ) :=
  RawCubicWeightedBudget.actual_weighted_energy_le profile scalar_certificate
    OriginalCubic4047255OptimizedEndpoint.original_observation_raw4047255 N hμ hf

theorem weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C * ‖f‖ ^ 2 :=
  RawCubicWeightedBudget.actual_weighted_energy_norm_sq_le profile scalar_certificate
    OriginalCubic4047255OptimizedEndpoint.original_observation_raw4047255 N hμ f

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N, t d * K⁻¹ ^ d * actualAppellEnergy μ f d /
      (d.factorial : ℝ) ^ 2) ≤ C * ‖f‖ ^ 2 := by
  have hb := weighted_budget_norm_sq N hμ f
  have he : GeneralWeighted.energy μ f (weight profile) N =
      ∑ d ∈ Finset.Icc 2 N, t d * K⁻¹ ^ d * actualAppellEnergy μ f d /
        (d.factorial : ℝ) ^ 2 := by
    unfold GeneralWeighted.energy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [weight, profile, withBudget, LongPrefixWeightedProfileData.profile,
      PositiveEnergyWeightedDrift.weight, CoupledEnergy.factorialWeight,
      mul_inv_rev, inv_pow, div_eq_mul_inv]
    ring
  rwa [he] at hb

end KLSConstantImprovement.Raw4047255LowerBudgetProfile
#print axioms KLSConstantImprovement.Raw4047255LowerBudgetProfile.scalar_certificate
#print axioms KLSConstantImprovement.Raw4047255LowerBudgetProfile.weighted_budget
#print axioms KLSConstantImprovement.Raw4047255LowerBudgetProfile.weighted_budget_norm_sq
#print axioms KLSConstantImprovement.Raw4047255LowerBudgetProfile.raw_budget_norm_sq
