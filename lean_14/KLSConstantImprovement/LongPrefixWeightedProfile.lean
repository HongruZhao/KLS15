import KLSConstantImprovement.LongPrefixWeightedProfileData
import CorrelatedCubicRationalTangents239

/-! Complete exact scalar certificate for the independent all-rank profile.
The original-law finite weighted budget is unconditional: all scalar
conditions are discharged here, including the correlated cubic head. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.LongPrefixWeightedProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
open KLSConstantImprovement.LongPrefixWeightedProfileData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def tangentT : ℝ := 124091563479/200000000000
def tangentPoint : ℝ := tangentT^2*(CreationSeed239.seedV tangentT)^2
def headWeight2 : ℝ := (c+head profile)*(2*t 2/K^2)
def headWeight3 : ℝ := (c-coefficient profile 3)*(t 3*CreationSeed239.B/K^3)
def tangentHeight : ℝ := headWeight3*
  (CreationSeed239.seedPhi tangentPoint-tangentPoint*deriv CreationSeed239.seedPhi tangentPoint)+
  max (headWeight2+headWeight3*deriv CreationSeed239.seedPhi tangentPoint) 0

theorem tangentPoint_mem : tangentPoint ∈ Icc (0 : ℝ) 1 := by
  norm_num [tangentPoint,tangentT,CreationSeed239.seedV]

theorem tangent_phi : CreationSeed239.seedPhi tangentPoint=1-tangentT^2 :=
  CreationSeed239.seedPhi_polynomial_parameter (by norm_num [tangentT])
    (by norm_num [tangentT,CreationSeed239.seedT])

theorem tangent_deriv : deriv CreationSeed239.seedPhi tangentPoint=
    (-(CreationSeed239.seedV tangentT*CreationSeed239.seedSlope tangentT))⁻¹ :=
  CreationSeed239.deriv_seedPhi_polynomial_parameter (by norm_num [tangentT])
    (by norm_num [tangentT,CreationSeed239.seedT]) tangentPoint_mem.2

theorem headWeight3_nonneg : 0 ≤ headWeight3 := by
  unfold headWeight3
  rw [coefficient_three]
  norm_num [c,K,t,CreationSeed239.B]

theorem tangent_height_lt : tangentHeight < c*C := by
  unfold tangentHeight headWeight2 headWeight3
  rw [head_value,coefficient_three,tangent_phi,tangent_deriv]
  norm_num [c,C,K,t,tangentPoint,tangentT,CreationSeed239.B,
    CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp]

theorem correlated_head_margin (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (c+head profile)*(2*t 2/K^2)*u+
      (c-coefficient profile 3)*(t 3*CreationSeed239.B/K^3)*CreationSeed239.seedPhi u < c*C := by
  have ht := concave_barrier_tangent CreationSeed239.seedInverseBarrier.concaveOn_phi
    tangentPoint_mem hu ((CreationSeed239.hasDerivAt_seedPhi tangentPoint_mem).differentiableAt.hasDerivAt)
  change CreationSeed239.seedPhi u ≤ CreationSeed239.seedPhi tangentPoint+
    deriv CreationSeed239.seedPhi tangentPoint*(u-tangentPoint) at ht
  have hb := mul_le_mul_of_nonneg_left ht headWeight3_nonneg
  have hl : (headWeight2+headWeight3*deriv CreationSeed239.seedPhi tangentPoint)*u ≤
      max (headWeight2+headWeight3*deriv CreationSeed239.seedPhi tangentPoint) 0 := by
    by_cases hp : 0 ≤ headWeight2+headWeight3*deriv CreationSeed239.seedPhi tangentPoint
    · rw [max_eq_left hp]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 hp
    · rw [max_eq_right (le_of_not_ge hp)]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hp) hu.1
  have hh : headWeight2*u+headWeight3*CreationSeed239.seedPhi u ≤ tangentHeight := by
    unfold tangentHeight
    nlinarith only [hb,hl]
  exact hh.trans_lt tangent_height_lt

theorem scalar_certificate : ScalarCertificate profile := by
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
    head_margin := correlated_head_margin }
  · change 0 ≤ c+head profile
    rw [head_value]
    norm_num [c]
  · change 0 ≤ c-coefficient profile 3
    rw [coefficient_three]
    norm_num [c]

theorem universal_weighted_budget (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*(∫ x, (f x)^2 ∂μ) :=
  actual_weighted_energy_le profile scalar_certificate N hμ hf

theorem universal_weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    GeneralWeighted.energy μ f (weight profile) N ≤ C*‖f‖^2 :=
  actual_weighted_energy_norm_sq_le profile scalar_certificate N hμ f


theorem t_floor (d : ℕ) (hd : 2 ≤ d) : tau ≤ t d := LongPrefixWeightedProfileData.t_floor d hd

theorem t_nonneg (d : ℕ) : 0 ≤ t d := by
  by_cases hd:2 ≤ d
  · exact (t_positive d hd).le
  · interval_cases d <;> norm_num [t,tTail]

theorem t_two : t 2=1 := by norm_num [t]
theorem t_three : t 3=(482469878667/500000000000 : ℝ) := by norm_num [t]
theorem t_four : t 4=(1115409358379/1000000000000 : ℝ) := by norm_num [t]

theorem raw_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    (∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2) ≤ C*‖f‖^2 := by
  have hb:=universal_weighted_budget_norm_sq N hμ f
  have he:GeneralWeighted.energy μ f (weight profile) N=
      ∑ d ∈ Finset.Icc 2 N,t d*K⁻¹^d*actualAppellEnergy μ f d/(d.factorial : ℝ)^2 := by
    unfold GeneralWeighted.energy
    apply Finset.sum_congr rfl
    intro d hd
    simp only [weight,profile,PositiveEnergyWeightedDrift.weight,CoupledEnergy.factorialWeight,
      mul_inv_rev,inv_pow,div_eq_mul_inv]
    ring
  rwa [he] at hb

end KLSConstantImprovement.LongPrefixWeightedProfile
#print axioms KLSConstantImprovement.LongPrefixWeightedProfile.scalar_certificate
#print axioms KLSConstantImprovement.LongPrefixWeightedProfile.universal_weighted_budget
#print axioms KLSConstantImprovement.LongPrefixWeightedProfile.universal_weighted_budget_norm_sq

#print axioms KLSConstantImprovement.LongPrefixWeightedProfile.raw_budget_norm_sq
