import QuarticObservationSupportingAlgebra
import QuarticObservationRationalTangents200000
import CorrelatedCubicInitialization239
import ThreeObservationInitialization
noncomputable section
open Set
namespace KLSBelow25.ProjectionThreeHeadRefinedNumerics
open ProjectionSlackRatio QuarticObservationSupport
set_option maxHeartbeats 15000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def K : ℝ := 8051/625
def C : ℝ := 1957/40000
def p : ℝ := 13054/12500
def thirdLower : ℝ := 1108589/1000000
def fourthLower : ℝ := 564087/500000
def supportCap : ℝ := 156303/125000000
def floorFactor : ℝ := 12496/12500
def eta : ℝ := 1511/100000
def weight : ℝ := 509/1000
def growth : ℝ := 1000001/1000000
def init3_t3 : ℝ := 346701/500000
def init4_t3 : ℝ := 343977/500000
def init4_t4 : ℝ := 178581/500000
def init4_r : ℝ := 1027619/1000000
def init4_x : ℝ := 2943/250000
def head_t3 : ℝ := 692887/1000000
def head_t4 : ℝ := 88461/250000
def firstCap : ℝ := 2/K^2
def secondCap : ℝ := CreationSeed239.B/K^3
def secondLower : ℝ := p^2-firstCap
def normSqUpper : ℝ := K*(523/500)
def weight1 : ℝ := 1/p-1/fourthLower
def weight2 : ℝ := 1/secondLower-1/fourthLower
def weight3 : ℝ := 1/thirdLower-1/fourthLower
def initialWeight : ℝ := thirdHeadInitialWeight p init4_r init4_x
def init3_t3_point : ℝ := init3_t3^2*(CreationSeed239.seedV init3_t3)^2
theorem init3_t3_nonneg : 0 ≤ init3_t3 := by norm_num [init3_t3]
theorem init3_t3_lt : init3_t3 < CreationSeed239.seedT := by norm_num [init3_t3,CreationSeed239.seedT]
theorem init3_t3_point_mem : init3_t3_point ∈ Icc (0 : ℝ) 1 := by
  norm_num [init3_t3_point,init3_t3,CreationSeed239.seedV]
theorem init3_t3_phi : CreationSeed239.seedPhi init3_t3_point=1-init3_t3^2 :=
  CreationSeed239.seedPhi_polynomial_parameter init3_t3_nonneg init3_t3_lt
theorem init3_t3_deriv : deriv CreationSeed239.seedPhi init3_t3_point=
    (-(CreationSeed239.seedV init3_t3*CreationSeed239.seedSlope init3_t3))⁻¹ :=
  CreationSeed239.deriv_seedPhi_polynomial_parameter init3_t3_nonneg init3_t3_lt init3_t3_point_mem.2
def init4_t3_point : ℝ := init4_t3^2*(CreationSeed239.seedV init4_t3)^2
theorem init4_t3_nonneg : 0 ≤ init4_t3 := by norm_num [init4_t3]
theorem init4_t3_lt : init4_t3 < CreationSeed239.seedT := by norm_num [init4_t3,CreationSeed239.seedT]
theorem init4_t3_point_mem : init4_t3_point ∈ Icc (0 : ℝ) 1 := by
  norm_num [init4_t3_point,init4_t3,CreationSeed239.seedV]
theorem init4_t3_phi : CreationSeed239.seedPhi init4_t3_point=1-init4_t3^2 :=
  CreationSeed239.seedPhi_polynomial_parameter init4_t3_nonneg init4_t3_lt
theorem init4_t3_deriv : deriv CreationSeed239.seedPhi init4_t3_point=
    (-(CreationSeed239.seedV init4_t3*CreationSeed239.seedSlope init4_t3))⁻¹ :=
  CreationSeed239.deriv_seedPhi_polynomial_parameter init4_t3_nonneg init4_t3_lt init4_t3_point_mem.2
def init4_t4_point : ℝ := init4_t4^2*(QuarticCreation200000.seedV init4_t4)^2
theorem init4_t4_nonneg : 0 ≤ init4_t4 := by norm_num [init4_t4]
theorem init4_t4_lt : init4_t4 < QuarticCreation200000.seedT := by norm_num [init4_t4,QuarticCreation200000.seedT]
theorem init4_t4_point_mem : init4_t4_point ∈ Icc (0 : ℝ) 1 := by
  norm_num [init4_t4_point,init4_t4,QuarticCreation200000.seedV]
theorem init4_t4_phi : QuarticCreation200000.seedPhi init4_t4_point=1-init4_t4^2 :=
  QuarticCreation200000.seedPhi_polynomial_parameter init4_t4_nonneg init4_t4_lt
theorem init4_t4_deriv : deriv QuarticCreation200000.seedPhi init4_t4_point=
    (-(QuarticCreation200000.seedV init4_t4*QuarticCreation200000.seedSlope init4_t4))⁻¹ :=
  QuarticCreation200000.deriv_seedPhi_polynomial_parameter init4_t4_nonneg init4_t4_lt init4_t4_point_mem.2
def head_t3_point : ℝ := head_t3^2*(CreationSeed239.seedV head_t3)^2
theorem head_t3_nonneg : 0 ≤ head_t3 := by norm_num [head_t3]
theorem head_t3_lt : head_t3 < CreationSeed239.seedT := by norm_num [head_t3,CreationSeed239.seedT]
theorem head_t3_point_mem : head_t3_point ∈ Icc (0 : ℝ) 1 := by
  norm_num [head_t3_point,head_t3,CreationSeed239.seedV]
theorem head_t3_phi : CreationSeed239.seedPhi head_t3_point=1-head_t3^2 :=
  CreationSeed239.seedPhi_polynomial_parameter head_t3_nonneg head_t3_lt
theorem head_t3_deriv : deriv CreationSeed239.seedPhi head_t3_point=
    (-(CreationSeed239.seedV head_t3*CreationSeed239.seedSlope head_t3))⁻¹ :=
  CreationSeed239.deriv_seedPhi_polynomial_parameter head_t3_nonneg head_t3_lt head_t3_point_mem.2
def head_t4_point : ℝ := head_t4^2*(QuarticCreation200000.seedV head_t4)^2
theorem head_t4_nonneg : 0 ≤ head_t4 := by norm_num [head_t4]
theorem head_t4_lt : head_t4 < QuarticCreation200000.seedT := by norm_num [head_t4,QuarticCreation200000.seedT]
theorem head_t4_point_mem : head_t4_point ∈ Icc (0 : ℝ) 1 := by
  norm_num [head_t4_point,head_t4,QuarticCreation200000.seedV]
theorem head_t4_phi : QuarticCreation200000.seedPhi head_t4_point=1-head_t4^2 :=
  QuarticCreation200000.seedPhi_polynomial_parameter head_t4_nonneg head_t4_lt
theorem head_t4_deriv : deriv QuarticCreation200000.seedPhi head_t4_point=
    (-(QuarticCreation200000.seedV head_t4*QuarticCreation200000.seedSlope head_t4))⁻¹ :=
  QuarticCreation200000.deriv_seedPhi_polynomial_parameter head_t4_nonneg head_t4_lt head_t4_point_mem.2
def initialHeight : ℝ := height (initialWeight/K^2) (2*init4_r/K^3) (1/K^4)
  init4_t3_point init4_t4_point
def supportHeight : ℝ := height (weight1/K^2) (weight2/K^3) (weight3/K^4)
  head_t3_point head_t4_point
def totalSpend : ℝ := supportCap+C/fourthLower
def correctedLower : ℝ := p-(1-eta)*totalSpend/floorFactor
def remainingSpend : ℝ := totalSpend/floorFactor-(p-1)

theorem K_positive : 0 < K := by norm_num [K]
theorem firstCap_positive : 0 < firstCap := by norm_num [firstCap,K]
theorem secondCap_nonneg : 0 ≤ secondCap := by norm_num [secondCap,K,CreationSeed239.B]
theorem p_positive : 0 < p := by norm_num [p]
theorem initialWeight_nonneg : 0 ≤ initialWeight := by
  norm_num [initialWeight,thirdHeadInitialWeight,p,init4_r,init4_x]
theorem initial_effective_nonneg : 0 ≤ effective (2*init4_r/K^3) (1/K^4) init4_t4_point := by
  rw [effective,init4_t4_deriv]
  norm_num [K,init4_r,QuarticCreation200000.observationScale,CreationSeed239.B,
    init4_t4,QuarticCreation200000.seedV,QuarticCreation200000.seedSlope,QuarticCreation200000.seedVp]
theorem head_effective_nonneg : 0 ≤ effective (weight2/K^3) (weight3/K^4) head_t4_point := by
  rw [effective,head_t4_deriv]
  norm_num [weight2,weight3,secondLower,firstCap,thirdLower,fourthLower,p,K,
    QuarticCreation200000.observationScale,CreationSeed239.B,head_t4,
    QuarticCreation200000.seedV,QuarticCreation200000.seedSlope,QuarticCreation200000.seedVp]

theorem thirdLower_le_tangentLower :
    thirdLower ≤ CorrelatedInitialization239.tangentLower p firstCap secondCap init3_t3_point := by
  unfold CorrelatedInitialization239.tangentLower
  rw [init3_t3_phi,init3_t3_deriv]
  norm_num [thirdLower,p,firstCap,secondCap,K,CreationSeed239.B,init3_t3,
    init3_t3_point,CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp]

theorem correlated_initialization {x y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ firstCap)
    (hy : y ≤ secondCap*CreationSeed239.seedPhi (x/firstCap)) :
    thirdLower ≤ (p^2-x)*(p-x/p)-y := by
  have hm : x/firstCap ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hx0 firstCap_positive.le, (div_le_one firstCap_positive).mpr hx⟩
  exact thirdLower_le_tangentLower.trans
    (CorrelatedInitialization239.correlated_seed_initialization_lower p_positive firstCap_positive
      secondCap_nonneg init3_t3_point_mem hm hy)

theorem fourthLower_le_initialBase :
    fourthLower ≤ thirdHeadInitialBase p init4_r init4_x-initialHeight := by
  unfold initialHeight height effective
  rw [init4_t3_phi,init4_t3_deriv,init4_t4_phi,init4_t4_deriv]
  norm_num [fourthLower,thirdHeadInitialBase,initialWeight,thirdHeadInitialWeight,p,K,
    init4_r,init4_x,init4_t3_point,init4_t4_point,init4_t3,init4_t4,QuarticCreation200000.observationScale,
    CreationSeed239.B,CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp,
    QuarticCreation200000.seedV,QuarticCreation200000.seedSlope,QuarticCreation200000.seedVp]

theorem supportHeight_le_cap : supportHeight ≤ supportCap := by
  unfold supportHeight height effective
  rw [head_t3_phi,head_t3_deriv,head_t4_phi,head_t4_deriv]
  norm_num [supportCap,weight1,weight2,weight3,secondLower,firstCap,thirdLower,fourthLower,p,K,
    head_t3_point,head_t4_point,head_t3,head_t4,QuarticCreation200000.observationScale,CreationSeed239.B,
    CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp,
    QuarticCreation200000.seedV,QuarticCreation200000.seedSlope,QuarticCreation200000.seedVp]

theorem initial_shape (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) (hcurve : v ≤ CreationSeed239.seedPhi u) :
    2*(initialWeight/K^2)*u+(2*init4_r/K^3)*CreationSeed239.B*v+
      (200000/(576*K^4))*QuarticCreation200000.seedPhi v ≤ initialHeight := by
  have hh := supporting_shape (a := initialWeight/K^2) (b := 2*init4_r/K^3)
    (c := 1/K^4) (by positivity) init4_t3_point_mem init4_t4_point_mem
    initial_effective_nonneg u hu v hv hcurve
  convert hh using 1 <;> first | rfl | ring

theorem head_shape (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) (hcurve : v ≤ CreationSeed239.seedPhi u) :
    2*(weight1/K^2)*u+(weight2/K^3)*CreationSeed239.B*v+
      (200000*weight3/(576*K^4))*QuarticCreation200000.seedPhi v ≤ supportCap := by
  have hh := supporting_shape (a := weight1/K^2) (b := weight2/K^3)
    (c := weight3/K^4) (by norm_num [weight3,thirdLower,fourthLower,K])
    head_t3_point_mem head_t4_point_mem head_effective_nonneg u hu v hv hcurve
  calc
    _ ≤ supportHeight := by convert hh using 1 <;> first | rfl | ring
    _ ≤ supportCap := supportHeight_le_cap

theorem numerical_parameters :
    1 < p ∧ 0 < secondLower ∧ 0 < thirdLower ∧ 0 < fourthLower ∧
    0 ≤ init4_r ∧ init4_r ≤ 2*(p-firstCap/p) ∧
    0 ≤ weight1 ∧ 0 ≤ weight2 ∧ 0 ≤ weight3 ∧
    0 ≤ initialHeight ∧ 0 ≤ supportCap := by
  refine ⟨by norm_num [p],by norm_num [secondLower,p,firstCap,K],
    by norm_num [thirdLower],by norm_num [fourthLower],
    by norm_num [init4_r],by norm_num [init4_r,p,firstCap,K],
    by norm_num [weight1,p,fourthLower],
    by norm_num [weight2,secondLower,p,firstCap,K,fourthLower],
    by norm_num [weight3,thirdLower,fourthLower],?_,by norm_num [supportCap]⟩
  unfold initialHeight height effective
  rw [init4_t3_phi,init4_t3_deriv,init4_t4_phi,init4_t4_deriv]
  norm_num [initialWeight,thirdHeadInitialWeight,p,K,init4_r,init4_x,init4_t3_point,init4_t4_point,init4_t3,init4_t4,
    QuarticCreation200000.observationScale,CreationSeed239.B,
    CreationSeed239.seedV,CreationSeed239.seedSlope,CreationSeed239.seedVp,
    QuarticCreation200000.seedV,QuarticCreation200000.seedSlope,QuarticCreation200000.seedVp]

theorem finite_anchor_parameters :
    1 < p ∧ 0 < floorFactor ∧ floorFactor < 1 ∧ 0 < eta ∧ eta < 1 ∧
    1/2 < weight ∧ weight < 1 ∧ 1 < growth ∧
    floorFactor ≤ p-totalSpend/floorFactor ∧ growth ≤ correctedLower ∧
    growth^2 ≤ correctedLower*(1-remainingSpend) ∧
    (1-weight)*correctedLower/weight ≤ floorFactor ∧
    1/2 ≤ 1-remainingSpend ∧
    eta*((normSqUpper+1)/weight+normSqUpper/(1-weight)) ≤
      1-2/(K*floorFactor) := by
  norm_num [p,floorFactor,eta,weight,growth,totalSpend,supportCap,C,fourthLower,
    correctedLower,remainingSpend,normSqUpper,K]

theorem endpoint_value : 1+K*p=(56455127 : ℝ)/3906250 := by norm_num [K,p]
end KLSBelow25.ProjectionThreeHeadRefinedNumerics
#print axioms KLSBelow25.ProjectionThreeHeadRefinedNumerics.fourthLower_le_initialBase
#print axioms KLSBelow25.ProjectionThreeHeadRefinedNumerics.supportHeight_le_cap
#print axioms KLSBelow25.ProjectionThreeHeadRefinedNumerics.finite_anchor_parameters
