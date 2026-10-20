import CorrelatedCubicInitialization239

/-! Expanded all-N profile shared-resource finite-anchor numerical premises; no numerical endpoint follows from this file.
Only the actual correlated cubic curve is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
namespace KLSBelow25.ProjectionExpandedProfileNumerics
open CreationSeed239 CorrelatedInitialization239
def K : ℝ := 64419/5000
def p : ℝ := 10447/10000
def firstCap : ℝ := 2/K^2
def secondCap : ℝ := (239/10)/K^3
def t : ℝ := 693439/1000000
def tangentPoint : ℝ := t^2*(seedV t)^2
def thirdLower : ℝ := 5549189/5000000
def C : ℝ := 981/20000
def secondLower : ℝ := p^2-firstCap
def rate : ℝ := 10000001/10000000
def weight1 : ℝ := 1/p-1/thirdLower
def weight2 : ℝ := 1/secondLower-1/thirdLower
def supportCap : ℝ := 81127/100000000
def supportT : ℝ := 697951/1000000
def supportPoint : ℝ := supportT^2*(seedV supportT)^2
def supportCoefficient : ℝ :=
  2*weight1/K^2+((239/10)*weight2/K^3)*deriv seedPhi supportPoint

theorem t_nonneg : 0 ≤ t := by norm_num [t]
theorem t_lt_seedT : t < seedT := by norm_num [t, seedT]
theorem tangentPoint_mem : tangentPoint ∈ Icc (0 : ℝ) 1 := by
  norm_num [tangentPoint, t, seedV]
theorem K_positive : 0 < K := by norm_num [K]
theorem p_positive : 0 < p := by norm_num [p]
theorem firstCap_positive : 0 < firstCap := by norm_num [firstCap, K]
theorem secondCap_nonneg : 0 ≤ secondCap := by norm_num [secondCap, K]

theorem thirdLower_le_tangentLower :
    thirdLower ≤ tangentLower p firstCap secondCap tangentPoint := by
  unfold tangentLower
  rw [tangentPoint, seedPhi_polynomial_parameter t_nonneg t_lt_seedT,
    deriv_seedPhi_polynomial_parameter t_nonneg t_lt_seedT tangentPoint_mem.2]
  norm_num [thirdLower, p, firstCap, secondCap, K, t, seedV, seedSlope, seedVp]

theorem correlated_initialization {x y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ firstCap)
    (hy : y ≤ secondCap*seedPhi (x/firstCap)) :
    thirdLower ≤ (p^2-x)*(p-x/p)-y := by
  have hm : x/firstCap ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx0 firstCap_positive.le, (div_le_one firstCap_positive).mpr hx⟩
  exact thirdLower_le_tangentLower.trans
    (correlated_seed_initialization_lower p_positive firstCap_positive secondCap_nonneg
      tangentPoint_mem hm hy)

theorem supportT_nonneg : 0 ≤ supportT := by norm_num [supportT]
theorem supportT_lt_seedT : supportT < seedT := by norm_num [supportT, seedT]
theorem supportPoint_mem : supportPoint ∈ Icc (0 : ℝ) 1 := by
  norm_num [supportPoint, supportT, seedV]

theorem supportCoefficient_nonneg : 0 ≤ supportCoefficient := by
  unfold supportCoefficient
  rw [supportPoint, deriv_seedPhi_polynomial_parameter supportT_nonneg supportT_lt_seedT
    supportPoint_mem.2]
  norm_num [weight1, weight2, K, p, secondLower, firstCap, thirdLower,
    supportT, seedV, seedSlope, seedVp]

theorem supportHeight_le_cap :
    ((239/10)*weight2/K^3)*(seedPhi supportPoint-supportPoint*deriv seedPhi supportPoint)+
      supportCoefficient ≤ supportCap := by
  unfold supportCoefficient
  rw [supportPoint, seedPhi_polynomial_parameter supportT_nonneg supportT_lt_seedT,
    deriv_seedPhi_polynomial_parameter supportT_nonneg supportT_lt_seedT supportPoint_mem.2]
  norm_num [weight1, weight2, K, p, secondLower, firstCap, thirdLower, supportCap,
    supportT, seedV, seedSlope, seedVp]

theorem actual_seed_support {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    2*(weight1/K^2)*z+(weight2/K^3)*B*seedPhi z ≤ supportCap := by
  have ht := KLS.DeterministicBridgeNext.concave_barrier_tangent
    seedInverseBarrier.concaveOn_phi supportPoint_mem hz
    ((hasDerivAt_seedPhi supportPoint_mem).differentiableAt.hasDerivAt)
  change seedPhi z ≤ seedPhi supportPoint+deriv seedPhi supportPoint*(z-supportPoint) at ht
  have hw : 0 ≤ (239/10)*weight2/K^3 := by
    norm_num [weight2, K, secondLower, p, firstCap, thirdLower]
  have hm := mul_le_mul_of_nonneg_left ht hw
  have hz' := mul_le_mul_of_nonneg_left hz.2 supportCoefficient_nonneg
  have he : 2*(weight1/K^2)*z+(weight2/K^3)*B*
      (seedPhi supportPoint+deriv seedPhi supportPoint*(z-supportPoint)) =
      ((239/10)*weight2/K^3)*(seedPhi supportPoint-supportPoint*deriv seedPhi supportPoint)+
        supportCoefficient*z := by
    unfold supportCoefficient
    norm_num only [B]
    ring
  calc
    _ ≤ 2*(weight1/K^2)*z+(weight2/K^3)*B*
        (seedPhi supportPoint+deriv seedPhi supportPoint*(z-supportPoint)) := by
      norm_num only [B]
      convert add_le_add_left hm (2*(weight1/K^2)*z) using 1 <;> ring
    _ = _ := he
    _ ≤ ((239/10)*weight2/K^3)*(seedPhi supportPoint-supportPoint*deriv seedPhi supportPoint)+
        supportCoefficient := add_le_add le_rfl (by simpa only [mul_one] using hz')
    _ ≤ supportCap := supportHeight_le_cap

def floorFactor : ℝ := 99967/100000
def eta : ℝ := 1511/100000
def weight : ℝ := 509/1000
def normSqUpper : ℝ := K*(523/500)
def totalSpend : ℝ := supportCap+C/thirdLower
def correctedLower : ℝ := p-(1-eta)*totalSpend/floorFactor
def remainingSpend : ℝ := totalSpend/floorFactor-(p-1)
def growth : ℝ := 1000001/1000000

theorem finite_anchor_parameters :
    1 < p ∧ 0 < floorFactor ∧ floorFactor < 1 ∧ 0 < eta ∧ eta < 1 ∧
    1/2 < weight ∧ weight < 1 ∧ 1 < growth ∧
    floorFactor ≤ p-totalSpend/floorFactor ∧ growth ≤ correctedLower ∧
    growth^2 ≤ correctedLower*(1-remainingSpend) ∧
    (1-weight)*correctedLower/weight ≤ floorFactor ∧
    1/2 ≤ 1-remainingSpend ∧
    eta*((normSqUpper+1)/weight+normSqUpper/(1-weight)) ≤
      1-2/(K*floorFactor) := by
  norm_num [p,floorFactor,eta,weight,growth,totalSpend,supportCap,C,thirdLower,
    correctedLower,remainingSpend,normSqUpper,K]

theorem head_parameters :
    0 ≤ firstCap ∧ p ≤ secondLower ∧ p^2 ≤ thirdLower ∧
    secondLower ≤ p^2-firstCap ∧
    0 ≤ weight1 ∧ 0 ≤ weight2 ∧ 0 ≤ supportCap := by
  norm_num [p,firstCap,K,secondLower,thirdLower,weight1,weight2,supportCap]

theorem endpoint_value_conditional : 1+K*p = (722985293 : ℝ)/50000000 := by norm_num [K,p]

end KLSBelow25.ProjectionExpandedProfileNumerics
#print axioms KLSBelow25.ProjectionExpandedProfileNumerics.thirdLower_le_tangentLower
#print axioms KLSBelow25.ProjectionExpandedProfileNumerics.correlated_initialization
#print axioms KLSBelow25.ProjectionExpandedProfileNumerics.actual_seed_support
#print axioms KLSBelow25.ProjectionExpandedProfileNumerics.finite_anchor_parameters
#print axioms KLSBelow25.ProjectionExpandedProfileNumerics.head_parameters
