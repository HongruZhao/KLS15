import KLSConstantImprovement.ActualCubicCreationJointRawSupport
import KLSConstantImprovement.ActualCubicCreationJointDual

/-! A sharper fifth-free joint support on the same original law.
The mixed cubic/quadratic tests are eliminated with positive rational
weights. The retained seed2388 raw cap then gives a strictly smaller
creation-support constant. This module proves an intermediate estimate;
it does not assert a new universal Poincare endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicCreationOptimizedSupport
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicCreationJointRawSupport ActualCubicCreationJointDual
open ActualDeficitCurvatureConditionalEndpoint
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem mixed_support_elimination {V Q R g D C s t u : ℝ}
    (hs : s = u*t) (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hst : s ≤ t)
    (hp : V+s^2*g-2*s*D ≤ C*(9*Q+4*s^2*R-12*s*R))
    (hv : 0 ≤ V+t^2*g-2*t*D) (hg : g ≤ 8*R) :
    (1-u)*V+(C*(12*s-4*s^2)-8*s*(t-s))*R ≤ 9*C*Q := by
  have hvp := mul_nonneg hu hv
  have hgp := mul_le_mul_of_nonneg_left hg (mul_nonneg hs0 (sub_nonneg.mpr hst))
  linear_combination hp + hvp + hgp - (t*g-2*D)*hs

theorem optimized_rational_mixed_support {V Q R g D : ℝ}
    (hp : V+(427011/464674 : ℝ)^2*g-2*(427011/464674 : ℝ)*D ≤
      (71727/5000 : ℝ)*(9*Q+4*(427011/464674 : ℝ)^2*R-12*(427011/464674 : ℝ)*R))
    (hv : 0 ≤ V+(1181820/232337 : ℝ)^2*g-2*(1181820/232337 : ℝ)*D)
    (hg : g ≤ 8*R) :
    V+(2803611889/29042125 : ℝ)*R ≤ (19697/125 : ℝ)*Q := by
  nlinarith [hp,hv,hg]

theorem tensorPolynomial_optimized_creation_support_posDim {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c = T b a c) (hT23 : ∀ a b c,T a b c = T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (2803611889/29042125 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
        (19697/125 : ℝ)*(fourthContraction μ T+2*tensorSquare T) := by
  let K := symmetricAnnihilation μ T
  have hK := symmetricAnnihilation_isSymm μ T
  have hC : LongPrefixCubicBellmanEndpoint.bound ≤ (71727/5000 : ℝ) := by
    norm_num [LongPrefixCubicBellmanEndpoint.bound]
  have hp := quadraticPerturbation_poincare_of_bound_le hn hμ T hT12 hT23 K hK
    (427011/464674) (71727/5000) hC
  rw [quadraticGradientPairing_symmetricAnnihilation] at hp
  have hv := ProbabilityTheory.variance_nonneg
    (quadraticPerturbation μ T K (1181820/232337)) μ
  rw [quadraticPerturbation_variance hμ T K (1181820/232337)] at hv
  exact optimized_rational_mixed_support hp hv (centeredQuadratic_variance_le_eight hμ K hK)

theorem tensorPolynomial_optimized_creation_support {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c = T b a c) (hT23 : ∀ a b c,T a b c = T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (2803611889/29042125 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
        (19697/125 : ℝ)*(fourthContraction μ T+2*tensorSquare T) := by
  cases n with
  | zero =>
      have hz : tensorPolynomial μ T = (fun _ => 0) := by
        funext x
        simp [tensorPolynomial]
      rw [hz]
      change ProbabilityTheory.variance (0 : Space 0 → ℝ) μ+_ ≤ _
      rw [ProbabilityTheory.variance_zero]
      simp [matrixFrobeniusSq,fourthContraction,tensorSquare,square,tripleSum]
  | succ n =>
      exact tensorPolynomial_optimized_creation_support_posDim (by omega) hμ T hT12 hT23

def jointConstant : ℝ := 86453779175388/70090297225

theorem tensorPolynomial_variance_add_ninety_creation_le_of_raw {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c = T b a c) (hT23 : ∀ a b c,T a b c = T a c b)
    (H : ℝ) (hraw : ProbabilityTheory.variance (tensorPolynomial μ T) μ ≤ H*tensorSquare T) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      90*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
        ((189820639/2803611889 : ℝ)*H+
          (2613791250/2803611889 : ℝ)*(157576/125))*tensorSquare T := by
  have hs := tensorPolynomial_optimized_creation_support hμ T hT12 hT23
  have hf := (fourthContraction_bounds hμ T hT23).2
  have hp : ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      (2803611889/29042125 : ℝ)*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
        (157576/125 : ℝ)*tensorSquare T := by
    nlinarith [hs,hf]
  linear_combination (189820639/2803611889 : ℝ)*hraw+
    (2613791250/2803611889 : ℝ)*hp

theorem tensorPolynomial_variance_add_ninety_creation_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n))
    (hT12 : ∀ a b c,T a b c = T b a c) (hT23 : ∀ a b c,T a b c = T a c b) :
    ProbabilityTheory.variance (tensorPolynomial μ T) μ+
      90*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤ jointConstant*tensorSquare T := by
  have hj := tensorPolynomial_variance_add_ninety_creation_le_of_raw hμ T hT12 hT23
    (21492/25) (tensorPolynomial_variance_le_creation2388 hμ T)
  norm_num [jointConstant] at hj ⊢
  exact hj

theorem jointConstant_lt_creation2388 : jointConstant < (1511252/1225 : ℝ) := by
  norm_num [jointConstant]

theorem jointConstant_lt_joint23852_support : jointConstant < (7555854/6125 : ℝ) := by
  norm_num [jointConstant]

theorem actual_cubic_creation_joint_charge_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ) = 1) :
    90*matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f)) ≤
      actualAppellEnergy μ f 3*(jointConstant-actualAppellEnergy μ f 3) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualCubicNextArray μ f
  have hj := tensorPolynomial_variance_add_ninety_creation_le hμ T
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
  unfold tensorSquare at hj
  rw [actualCubicNextArray_square] at hj
  have hcs := covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hcs
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x,(f x)^2 ∂μ)-(∫ x,f x ∂μ)^2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x,f x ∂μ)]
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg (tensorPolynomial μ T) μ)
  change 90*matrixFrobeniusSq (symmetricAnnihilation μ T) ≤ _
  nlinarith [hcs,hpaid,hj]

theorem actual_proper_creation_pairing_sq_le_joint_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ) = 1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2 ≤
      (1/10 : ℝ)*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
        (jointConstant-actualAppellEnergy μ f 3) := by
  have hs := actual_proper_creation_pairing_sq_le_nine hμ hf
  have hj := actual_cubic_creation_joint_charge_unit hμ hf hunit
  have hpaid := mul_le_mul_of_nonneg_right hj (actualAppellEnergy_nonneg μ f 2)
  nlinarith [hs,hpaid]

theorem actual_proper_creation_pairing_sq_le_min_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ) = 1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2 ≤
      actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
        min 48 ((jointConstant-actualAppellEnergy μ f 3)/10) := by
  by_cases h : (48 : ℝ) ≤ (jointConstant-actualAppellEnergy μ f 3)/10
  · rw [min_eq_left h]
    nlinarith [actual_proper_creation_pairing_sq_le_retained hμ hf]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [actual_proper_creation_pairing_sq_le_joint_unit hμ hf hunit]

theorem actual_proper_creation_pairing_abs_le_min_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ) = 1) :
    |actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3| ≤
      Real.sqrt (actualAppellEnergy μ f 3)*
        Real.sqrt (actualAppellEnergy μ f 2*
          min 48 ((jointConstant-actualAppellEnergy μ f 3)/10)) := by
  have hb := Real.abs_le_sqrt (actual_proper_creation_pairing_sq_le_min_unit hμ hf hunit)
  rw [mul_assoc,Real.sqrt_mul (actualAppellEnergy_nonneg μ f 3)] at hb
  exact hb

end KLSConstantImprovement.ActualCubicCreationOptimizedSupport
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.mixed_support_elimination
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.optimized_rational_mixed_support
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.tensorPolynomial_optimized_creation_support_posDim
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.tensorPolynomial_optimized_creation_support
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.tensorPolynomial_variance_add_ninety_creation_le_of_raw
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.tensorPolynomial_variance_add_ninety_creation_le
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.jointConstant_lt_creation2388
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.jointConstant_lt_joint23852_support
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.actual_cubic_creation_joint_charge_unit
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.actual_proper_creation_pairing_sq_le_joint_unit
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.actual_proper_creation_pairing_sq_le_min_unit
#print axioms KLSConstantImprovement.ActualCubicCreationOptimizedSupport.actual_proper_creation_pairing_abs_le_min_unit
