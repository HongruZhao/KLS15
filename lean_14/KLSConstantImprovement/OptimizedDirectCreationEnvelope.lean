import KLSConstantImprovement.ActualCubicCreationOptimizedSupport

/-!
Fresh original-law dual integration, owned by original_upper_recovery6.
No build has been performed by this worker.

The already accepted optimized support is used directly, before mixing
with the raw cubic cap to change its creation coefficient to 90. This
keeps the same original cubic, quadratic, law, and proper remainder.
No residual projection or replacement moment array is introduced.

The output is a genuinely stronger universal proper-creation envelope.
It does not itself prove a smaller cubic seed or Poincare endpoint: the
same envelope must still be wired through the original heat terminal,
barrier criterion and a complete scalar profile certificate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff

namespace KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft

open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicGradientEnergy
open ActualCubicQuadraticRegression ActualCubicQuadraticDeficit
open ActualCubicCreationJointDual
open ActualDeficitCurvatureConditionalEndpoint

variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def directLambda : ℝ := 2803611889 / 29042125
def directIntercept : ℝ := 157576 / 125
def directSlope : ℝ := 9 / directLambda
def directCost (M : ℝ) : ℝ := min 48 (directSlope * (directIntercept - M))

theorem directLambda_gt_ninety : 90 < directLambda := by
  norm_num [directLambda]

theorem directSlope_pos : 0 < directSlope := by
  norm_num [directSlope, directLambda]

theorem directSlope_lt_tenth : directSlope < (1 / 10 : ℝ) := by
  norm_num [directSlope, directLambda]

theorem direct_line_difference (M : ℝ) :
    (ActualCubicCreationOptimizedSupport.jointConstant - M) / 10 -
      directSlope * (directIntercept - M) =
    ((1 / 10 : ℝ) - directSlope) * ((21492 / 25 : ℝ) - M) := by
  norm_num [ActualCubicCreationOptimizedSupport.jointConstant,
    directSlope, directLambda, directIntercept]
  ring

theorem directCost_le_retained_cost {M : ℝ} (hM : M ≤ (21492 / 25 : ℝ)) :
    directCost M ≤ min 48
      ((ActualCubicCreationOptimizedSupport.jointConstant - M) / 10) := by
  have hp : 0 ≤ ((1 / 10 : ℝ) - directSlope) * ((21492 / 25 : ℝ) - M) :=
    mul_nonneg (le_of_lt (sub_pos.mpr directSlope_lt_tenth)) (sub_nonneg.mpr hM)
  have hl : directSlope * (directIntercept - M) ≤
      (ActualCubicCreationOptimizedSupport.jointConstant - M) / 10 := by
    rw [← direct_line_difference M] at hp
    linarith
  exact min_le_min (le_refl 48) hl

theorem actual_direct_creation_charge_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x) ^ 2 ∂μ) = 1) :
    directLambda * matrixFrobeniusSq
        (symmetricAnnihilation μ (actualCubicNextArray μ f)) ≤
      actualAppellEnergy μ f 3 * (directIntercept - actualAppellEnergy μ f 3) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualCubicNextArray μ f
  have hT12 := actualCubicNextArray_first_symmetry hμ.logConcave hf
  have hT23 := actualCubicNextArray_last_symmetry hμ.logConcave hf
  have hj := ActualCubicCreationOptimizedSupport.tensorPolynomial_optimized_creation_support
    hμ T hT12 hT23
  have hF := (fourthContraction_bounds hμ T hT23).2
  have hp : ProbabilityTheory.variance (tensorPolynomial μ T) μ +
      directLambda * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤
        directIntercept * tensorSquare T := by
    norm_num [directLambda, directIntercept] at hj ⊢
    nlinarith
  unfold tensorSquare at hp
  rw [actualCubicNextArray_square] at hp
  have hcs := covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hcs
  have hfvar : ProbabilityTheory.variance f μ ≤ 1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x, (f x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤ 1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x, f x ∂μ)]
  have hpaid := mul_le_mul_of_nonneg_left hfvar
    (ProbabilityTheory.variance_nonneg (tensorPolynomial μ T) μ)
  change directLambda * matrixFrobeniusSq (symmetricAnnihilation μ T) ≤ _
  nlinarith [hcs, hpaid, hp]

theorem actual_direct_proper_pairing_sq_le_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x) ^ 2 ∂μ) = 1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ^ 2 ≤
      actualAppellEnergy μ f 3 * actualAppellEnergy μ f 2 *
        (directSlope * (directIntercept - actualAppellEnergy μ f 3)) := by
  have hs := actual_proper_creation_pairing_sq_le_nine hμ hf
  have hj := actual_direct_creation_charge_unit hμ hf hunit
  have hpaid := mul_le_mul_of_nonneg_right hj (actualAppellEnergy_nonneg μ f 2)
  norm_num [directSlope, directLambda] at hpaid ⊢
  nlinarith [hs, hpaid]

theorem actual_direct_proper_pairing_sq_le_min_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x) ^ 2 ∂μ) = 1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ^ 2 ≤
      actualAppellEnergy μ f 3 * actualAppellEnergy μ f 2 *
        directCost (actualAppellEnergy μ f 3) := by
  unfold directCost
  by_cases h : (48 : ℝ) ≤ directSlope * (directIntercept - actualAppellEnergy μ f 3)
  · rw [min_eq_left h]
    nlinarith [actual_proper_creation_pairing_sq_le_retained hμ hf]
  · rw [min_eq_right (le_of_not_ge h)]
    exact actual_direct_proper_pairing_sq_le_unit hμ hf hunit

theorem actual_direct_proper_pairing_abs_le_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x, (f x) ^ 2 ∂μ) = 1) :
    |actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3| ≤
      Real.sqrt (actualAppellEnergy μ f 3) *
        Real.sqrt (actualAppellEnergy μ f 2 * directCost (actualAppellEnergy μ f 3)) := by
  have hb := Real.abs_le_sqrt (actual_direct_proper_pairing_sq_le_min_unit hμ hf hunit)
  rw [mul_assoc, Real.sqrt_mul (actualAppellEnergy_nonneg μ f 3)] at hb
  exact hb

end KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft

#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.direct_line_difference
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.directCost_le_retained_cost
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.actual_direct_creation_charge_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.actual_direct_proper_pairing_sq_le_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.actual_direct_proper_pairing_sq_le_min_unit
#print axioms KLSConstantImprovement.OriginalUpperRecovery6DirectEnvelopeDraft.actual_direct_proper_pairing_abs_le_unit
