import KLSConstantImprovement.RawCubic336WeightedProfileData

/-! The exact selected generator profile. Its scalar certificate is proved;
the universal raw cubic observation bound remains an explicit hypothesis. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.RawCubic336WeightedProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.RawCubic336WeightedProfileData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem scalar_certificate : RawCubicWeightedBudget.ScalarCertificate profile 336 := by
  refine {
    K_positive := by norm_num [profile,K]
    c_positive := by norm_num [profile,c]
    base_budget := by norm_num [profile,K,C,t]
    young_positive := young_positive
    weight_positive := t_positive
    alpha_nonneg := alpha_nonneg
    alpha_lt_one := alpha_lt_one
    theta_nonneg := theta_nonneg
    theta_le_one := theta_le_one
    lambda_nonneg := lambda_nonneg
    lambda_le_one := lambda_le_one
    lambda_boundary := lambda_boundary
    zeta_nonneg := zeta_nonneg
    zeta_cap := zeta_cap
    quadratic_payment := by
      norm_num [profile,PositiveEnergyWeightedDrift.kappa,PositiveEnergyWeightedGenerator.gamma,
        K,young,t,tTail,theta,lambda,alpha]
    terminal_payment := terminal_payment
    coefficient_lower := coefficient_lower
    head_nonneg := ?_
    third_nonneg := ?_
    head_margin := ?_ }
  · change 0 ≤ c+head profile
    rw [head_value]
    norm_num [c]
  · change 0 ≤ c-coefficient profile 3
    rw [coefficient_three]
    norm_num [c]
  · change (c+head profile)*(2*t 2/K^2)+
      (c-coefficient profile 3)*(t 3*336/(36*K^3)) < c*C
    rw [head_value,coefficient_three]
    norm_num [c,C,K,t]

theorem weighted_budget
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x, (f x)^2 ∂μ) :=
  RawCubicWeightedBudget.actual_weighted_energy_le profile scalar_certificate hraw N hμ hf

theorem weighted_budget_norm_sq
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  RawCubicWeightedBudget.actual_weighted_energy_norm_sq_le profile scalar_certificate hraw N hμ f

theorem t_nonneg (d : ℕ) : 0 ≤ t d := by
  by_cases hd : 2 ≤ d
  · exact (t_positive d hd).le
  · interval_cases d <;> norm_num [t,tTail]

theorem raw_budget_norm_sq
    (hraw : RawCubicWeightedBudget.UniversalRawCubicBound 336)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 := by
  have hb := weighted_budget_norm_sq hraw N hμ f
  have he : GeneralWeighted.energy μ f (weight profile) N=
      ∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2 := by
    unfold GeneralWeighted.energy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [weight,profile,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight,
      mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  rwa [he] at hb

theorem exact_endpoint : 1+K*p=(13999/1000 : ℝ) := by norm_num [K,p]
theorem endpoint_lt_fourteen : (13999/1000 : ℝ)<14 := by norm_num

end KLSConstantImprovement.RawCubic336WeightedProfile
#print axioms KLSConstantImprovement.RawCubic336WeightedProfile.scalar_certificate
#print axioms KLSConstantImprovement.RawCubic336WeightedProfile.weighted_budget
#print axioms KLSConstantImprovement.RawCubic336WeightedProfile.raw_budget_norm_sq
