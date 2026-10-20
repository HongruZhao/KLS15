import ActualFourthCumulantCoordinates

/-! Retaining the actual quadratic-variance defect in the two-slot fourth
cumulant estimate. This is an actual-law inequality, but supplies no smaller
uniform constant without quantitative control of the retained defect. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem actualFourthCumulantFlat_pairing_eq_variance_sub_two
    {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hQ : QuadraticVarianceEight μ) (H : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, H i j * actualFourthCumulantFlat μ H i j) =
      ProbabilityTheory.variance (matrixQuadratic H) μ - 2 * matrixFrobeniusSq H := by
  have hH := memLp_matrixQuadratic_of_coordinateProducts hQ.memLp_coordinate_mul H
  have hp := covariance_matrixQuadratic_eq_pairing hH hQ.memLp_coordinate_mul H
  rw [covariance_self hH.aemeasurable] at hp
  rw [hp]
  simp only [actualFourthCumulantFlat, matrixFrobeniusSq, Finset.mul_sum,
    mul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_fourth_cumulant_flat_square_le_with_variance_defect
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq (actualFourthCumulantFlat μ H) ≤
      36 * matrixFrobeniusSq H -
        4 * (8 * matrixFrobeniusSq H - ProbabilityTheory.variance (matrixQuadratic H) μ) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  let hQ := hμ.quadraticVarianceEight_unconditional
  have hH := memLp_matrixQuadratic_of_coordinateProducts hQ.memLp_coordinate_mul H
  have hz := hQ.quadraticCovariance_frobeniusSq_le_variance hH
  rw [actualFourthCumulantFlat_square_eq hQ H]
  linarith

theorem actual_fourth_cumulant_flat_square_le_signed_pairing
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq (actualFourthCumulantFlat μ H) ≤
      4 * (∑ i, ∑ j, H i j * actualFourthCumulantFlat μ H i j) +
        12 * matrixFrobeniusSq H := by
  let : IsProbabilityMeasure μ := hμ.isProb
  rw [actualFourthCumulantFlat_pairing_eq_variance_sub_two
    hμ.quadraticVarianceEight_unconditional H]
  have hb := actual_fourth_cumulant_flat_square_le_with_variance_defect hμ H
  linarith

theorem actual_fourth_cumulant_tensor_square_le_signed_pairing
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i, ∑ j, (∑ a, ∑ b, actualFourthCumulantArray μ i j a b * H a b)^2) ≤
      4 * (∑ i, ∑ j, H i j *
        (∑ a, ∑ b, actualFourthCumulantArray μ i j a b * H a b)) +
      12 * matrixFrobeniusSq H := by
  have hb := actual_fourth_cumulant_flat_square_le_signed_pairing hμ H
  simpa only [matrixFrobeniusSq,
    actualFourthCumulantFlat_eq_tensor_contraction hμ H hH] using hb

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_square_le_with_variance_defect
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_square_le_signed_pairing
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_tensor_square_le_signed_pairing
