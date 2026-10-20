import KLSConstantImprovement.ActualCubicCreationJointBound
import KLSConstantImprovement.ActualDeficitCurvatureConditionalEndpoint
import ActualProperCubicCreation

/-! The joint cubic bound controls the literal proper creation pairing of
the same original-law unit L2 test. The ordered Appell coefficients, cubic
polynomial, and three-slot creation operator are identified explicitly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix InnerProductSpace
open scoped BigOperators ENNReal ContDiff
namespace KLSConstantImprovement.ActualCubicCreationJointDual
open KLS KLS.DeterministicBridge KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds ActualCubicRepresenter ActualCubicQuadraticRegression
open ActualCubicCreationJointBound ActualDeficitCurvatureConditionalEndpoint
variable {n : ℕ}
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem quadraticGradientPairing_sq_le (μ : Measure (Space n)) (T : Array3 (Fin n))
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (quadraticGradientPairing μ T B)^2≤
      matrixFrobeniusSq B*matrixFrobeniusSq (symmetricAnnihilation μ T) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n×Fin n))
    (fun a => B a.1 a.2) (fun a => symmetricAnnihilation μ T a.1 a.2)
  simpa only [Fintype.sum_prod_type,quadraticGradientPairing,matrixFrobeniusSq] using hs

theorem actual_quadratic_coefficient_matrix_square (μ : Measure (Space n)) (f : Space n→ℝ) :
    matrixFrobeniusSq (fun i j => actualAppellCoefficient μ f 2 ![i,j])=
      actualAppellEnergy μ f 2 := by
  simp only [matrixFrobeniusSq,actualAppellEnergy,sum_fin_two_coordinates]

theorem actual_proper_creation_pairing_eq {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)=
      3*quadraticGradientPairing μ (actualCubicNextArray μ f)
        (fun i j => actualAppellCoefficient μ f 2 ![i,j]) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  rw [dotProduct,sum_fin_three_coordinates]
  simp_rw [actualAppellProperRemainder_three_creation hμ hf]
  have hp := creation_pairing (actualThirdCubicArray μ) (actualCubicNextArray μ f)
    (fun i j => actualAppellCoefficient μ f 2 ![i,j])
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
    (actualAppell_two_swap hμ.logConcave hf)
  change (∑ i,∑ j,∑ k,actualCubicNextArray μ f i j k*
    creation (actualThirdCubicArray μ) (fun i j => actualAppellCoefficient μ f 2 ![i,j]) i j k)=_
  have he : (∑ i,∑ j,∑ k,actualCubicNextArray μ f i j k*
    creation (actualThirdCubicArray μ) (fun i j => actualAppellCoefficient μ f 2 ![i,j]) i j k)=
      tripleSum (fun i j k =>
        creation (actualThirdCubicArray μ) (fun i j => actualAppellCoefficient μ f 2 ![i,j]) i j k*
          actualCubicNextArray μ f i j k) := by
    unfold tripleSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,hp]
  rfl

theorem actual_proper_creation_pairing_sq_le_nine {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2≤
      9*matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f))*actualAppellEnergy μ f 2 := by
  have hs := quadraticGradientPairing_sq_le μ (actualCubicNextArray μ f)
    (fun i j => actualAppellCoefficient μ f 2 ![i,j])
  rw [actual_quadratic_coefficient_matrix_square] at hs
  rw [actual_proper_creation_pairing_eq hμ hf]
  nlinarith [hs]

theorem actual_cubic_creation_joint_charge_unit {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    90*matrixFrobeniusSq (symmetricAnnihilation μ (actualCubicNextArray μ f))≤
      actualAppellEnergy μ f 3*((302262/245 : ℝ)-actualAppellEnergy μ f 3) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  let T := actualCubicNextArray μ f
  have hj := tensorPolynomial_variance_add_ninety_creation_le hμ T
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
  unfold tensorSquare at hj
  rw [actualCubicNextArray_square] at hj
  have hcs := covariance_sq_le_variance_mul_variance (tensorPolynomial_memLp hμ T) hf
  rw [coefficientPolynomial_covariance hμ hf] at hcs
  have hfvar : ProbabilityTheory.variance f μ≤1 := by
    rw [ProbabilityTheory.variance_eq_sub hf]
    change (∫ x,(f x)^2 ∂μ)-(∫ x,f x ∂μ)^2≤1
    rw [hunit]
    nlinarith [sq_nonneg (∫ x,f x ∂μ)]
  have hpaid := mul_le_mul_of_nonneg_left hfvar (ProbabilityTheory.variance_nonneg (tensorPolynomial μ T) μ)
  change 90*matrixFrobeniusSq (symmetricAnnihilation μ T)≤_
  nlinarith [hcs,hpaid,hj]

theorem actual_proper_creation_pairing_sq_le_joint_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2≤
      (1/10 : ℝ)*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
        ((302262/245 : ℝ)-actualAppellEnergy μ f 3) := by
  have hs := actual_proper_creation_pairing_sq_le_nine hμ hf
  have hj := actual_cubic_creation_joint_charge_unit hμ hf hunit
  have hpaid := mul_le_mul_of_nonneg_right hj (actualAppellEnergy_nonneg μ f 2)
  nlinarith [hs,hpaid]

theorem actual_proper_creation_pairing_sq_le_retained {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2≤
      48*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2 := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3→Fin n))
    (actualAppellCoefficient μ f 3) (actualAppellProperRemainder μ f 3)
  change (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2≤
    actualAppellEnergy μ f 3*(∑ a,(actualAppellProperRemainder μ f 3 a)^2) at hs
  have hpaid := mul_le_mul_of_nonneg_left (actualAppellProperRemainder_three_square_le hμ hf)
    (actualAppellEnergy_nonneg μ f 3)
  nlinarith [hs,hpaid]

theorem actual_proper_creation_pairing_sq_le_min_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)^2≤
      actualAppellEnergy μ f 3*actualAppellEnergy μ f 2*
        min 48 (((302262/245 : ℝ)-actualAppellEnergy μ f 3)/10) := by
  by_cases h : (48 : ℝ)≤((302262/245 : ℝ)-actualAppellEnergy μ f 3)/10
  · rw [min_eq_left h]
    nlinarith [actual_proper_creation_pairing_sq_le_retained hμ hf]
  · rw [min_eq_right (le_of_not_ge h)]
    nlinarith [actual_proper_creation_pairing_sq_le_joint_unit hμ hf hunit]

theorem actual_proper_creation_pairing_abs_le_min_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ)
    (hunit : (∫ x,(f x)^2 ∂μ)=1) :
    |actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3|≤
      Real.sqrt (actualAppellEnergy μ f 3)*
        Real.sqrt (actualAppellEnergy μ f 2*
          min 48 (((302262/245 : ℝ)-actualAppellEnergy μ f 3)/10)) := by
  have hb := Real.abs_le_sqrt (actual_proper_creation_pairing_sq_le_min_unit hμ hf hunit)
  rw [mul_assoc,Real.sqrt_mul (actualAppellEnergy_nonneg μ f 3)] at hb
  exact hb

theorem actual_proper_creation_pairing_abs_le_min_Lp_unit {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) :
    |actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3|≤
      Real.sqrt (actualAppellEnergy μ f 3)*
        Real.sqrt (actualAppellEnergy μ f 2*
          min 48 (((302262/245 : ℝ)-actualAppellEnergy μ f 3)/10)) := by
  have hi : (∫ x,(f x)^2 ∂μ)=1 := by
    rw [←actualLp_norm_sq_eq_integral,hunit]
    norm_num
  exact actual_proper_creation_pairing_abs_le_min_unit hμ (Lp.memLp f) hi

end KLSConstantImprovement.ActualCubicCreationJointDual
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.quadraticGradientPairing_sq_le
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_quadratic_coefficient_matrix_square
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_eq
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_sq_le_nine
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_cubic_creation_joint_charge_unit
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_sq_le_joint_unit
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_sq_le_retained
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_sq_le_min_unit
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_abs_le_min_unit
#print axioms KLSConstantImprovement.ActualCubicCreationJointDual.actual_proper_creation_pairing_abs_le_min_Lp_unit
