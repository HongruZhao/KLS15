import KLSConstantImprovement.QuarticM32Profile20261020Data
import KLSConstantImprovement.RawCubicQuarticWeightedBudget

/-! Exact raw401.3023465 profile with a genuine rank-four generator head.
The scalar certificate is exact rational arithmetic. Universal weighted
budgets take the same-test quartic support explicitly until it is supplied
by the actual arbitrary-rawH cubic-to-quartic transfer. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.QuarticM32Profile20261020
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.QuarticM32Profile20261020Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def H : ℝ := 802604693/2000000
def contact : ℝ := 78898093437181/100000000000000
def J : ℝ := 159319868624440738113622150288445264999/624337573385983656452539964625000
def A : ℝ := J*contact/(16*H)
def B : ℝ := J/576

theorem scalar_certificate : RawCubicQuarticWeightedBudget.ScalarCertificate profile H A B := by
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
    fourth_nonneg := ?_
    small_three_budget := by norm_num [profile,K,C,t,H]
    head_margin := ?_ }
  · change 0 ≤ c+head profile
    rw [head_value]
    norm_num [c]
  · change 0 ≤ (c-coefficient profile 4)*t 4/K^4
    rw [coefficient_four]
    norm_num [c,K,t]
  · unfold RawCubicQuarticWeightedHead.headBound
      RawCubicQuarticWeightedHead.cubicCoefficient
      RawCubicQuarticWeightedHead.quarticCoefficient
    change (c+head profile)*(2*t 2/K^2)+
      max ((c-coefficient profile 3)*t 3/K^3-
        (c-coefficient profile 4)*t 4/K^4*A) 0*(H/36)+
          (c-coefficient profile 4)*t 4/K^4*B < c*C
    rw [head_value,coefficient_three,coefficient_four]
    norm_num [c,C,K,t,H,J,A,B,contact]

theorem weighted_budget
    (hraw : RawCubicQuarticWeightedBudget.UniversalRawCubicBound H)
    (hsupport : RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x, (f x)^2 ∂μ) :=
  RawCubicQuarticWeightedBudget.actual_weighted_energy_le profile scalar_certificate hraw hsupport N hμ hf

theorem weighted_budget_norm_sq
    (hraw : RawCubicQuarticWeightedBudget.UniversalRawCubicBound H)
    (hsupport : RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  RawCubicQuarticWeightedBudget.actual_weighted_energy_norm_sq_le profile scalar_certificate hraw hsupport N hμ f

theorem t_nonneg (d : ℕ) : 0 ≤ t d := by
  by_cases hd : 2 ≤ d
  · exact (t_positive d hd).le
  · interval_cases d <;> norm_num [t,tTail]

theorem raw_budget_norm_sq
    (hraw : RawCubicQuarticWeightedBudget.UniversalRawCubicBound H)
    (hsupport : RawCubicQuarticWeightedBudget.UniversalCubicQuarticUnitSupport A B)
    (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 := by
  have hb := weighted_budget_norm_sq hraw hsupport N hμ f
  have he : GeneralWeighted.energy μ f (weight profile) N=
      ∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2 := by
    unfold GeneralWeighted.energy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [weight,profile,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight,
      mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  rwa [he] at hb

theorem exact_endpoint : 1+K*p=(692049/50000 : ℝ) := by norm_num [K,p]
theorem endpoint_lt_fourteen : (692049/50000 : ℝ)<14 := by norm_num

end KLSConstantImprovement.QuarticM32Profile20261020
#print axioms KLSConstantImprovement.QuarticM32Profile20261020.scalar_certificate
#print axioms KLSConstantImprovement.QuarticM32Profile20261020.weighted_budget
#print axioms KLSConstantImprovement.QuarticM32Profile20261020.raw_budget_norm_sq
