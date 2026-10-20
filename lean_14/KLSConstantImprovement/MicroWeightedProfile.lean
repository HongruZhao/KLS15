import KLSConstantImprovement.MicroWeightedProfileData
import CorrelatedCubicRationalTangents239

/-! Complete exact scalar certificate for the independent all-rank profile.
The original-law finite weighted budget is unconditional: all scalar
conditions are discharged here, including the correlated cubic head. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace KLSConstantImprovement.MicroWeightedProfile
open KLS KLSBelow25 KLS.DeterministicBridgeNext
open KLSConstantImprovement.ParameterizedWeightedBudget
open KLSConstantImprovement.MicroWeightedProfileData
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def tangentT : ℝ := 5/8
def tangentPoint : ℝ := tangentT^2*(CreationSeed239.seedV tangentT)^2
def headWeight2 : ℝ := (c+head profile)*(2/K^2)
def headWeight3 : ℝ := (c-coefficient profile 3)*(CreationSeed239.B/K^3)
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
  norm_num [c,K,CreationSeed239.B]

theorem tangent_height_lt : tangentHeight < c*C := by
  unfold tangentHeight headWeight2 headWeight3
  rw [head_value,coefficient_three,tangent_phi,tangent_deriv]
  norm_num [c,C,K,tangentPoint,tangentT,CreationSeed239.B,
    CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp]

theorem correlated_head_margin (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (c+head profile)*(2/K^2)*u+
      (c-coefficient profile 3)*(CreationSeed239.B/K^3)*CreationSeed239.seedPhi u < c*C := by
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
    base_budget := by norm_num [profile,K,C]
    young_positive := young_positive
    zeta2_nonneg := zeta2_nonneg
    zeta2_cap := zeta2_cap
    zeta3_nonneg := zeta3_nonneg
    zeta3_cap := zeta3_cap
    alpha_nonneg := alpha_nonneg
    alpha_lt_one := alpha_lt_one
    alpha_two := by norm_num [profile,alpha]
    alpha_three := by norm_num [profile,alpha]
    alpha_low := alpha_low
    Q_sign := by norm_num [profile,K,young,alpha]
    R_sign := by norm_num [profile,K,alpha]
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
    actualWeightedAppellEnergy μ f K N ≤ C*(∫ x, (f x)^2 ∂μ) :=
  actual_weighted_energy_le profile scalar_certificate N hμ hf

theorem universal_weighted_budget_norm_sq (N : ℕ) {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) :
    actualWeightedAppellEnergy μ f K N ≤ C*‖f‖^2 :=
  actual_weighted_energy_norm_sq_le profile scalar_certificate N hμ f

end KLSConstantImprovement.MicroWeightedProfile
#print axioms KLSConstantImprovement.MicroWeightedProfile.scalar_certificate
#print axioms KLSConstantImprovement.MicroWeightedProfile.universal_weighted_budget
#print axioms KLSConstantImprovement.MicroWeightedProfile.universal_weighted_budget_norm_sq
