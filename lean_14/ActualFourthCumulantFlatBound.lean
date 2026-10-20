import ActualAppellQuadraticSeed

/-! The actual centered fourth-moment operator on ordered symmetric matrices.
The estimate is a two-slot flattening bound. It does not assert a bound for
one-to-three flattening of the fourth cumulant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- On an isotropic law this is the ordered symmetric-matrix contraction of
its fourth cumulant: covariance of the quadratic observable, minus `2 H`. -/
def actualFourthCumulantFlat (μ : Measure (Space n))
    (H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => quadraticCovarianceMatrix μ (matrixQuadratic H) i j - 2*H i j

theorem actualFourthCumulantFlat_isSymm {μ : Measure (Space n)}
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (actualFourthCumulantFlat μ H).IsSymm := by
  ext i j
  have hZ := quadraticCovarianceMatrix_isSymm μ (matrixQuadratic H)
  change _ - 2*H j i = _ - 2*H i j
  have hZij : quadraticCovarianceMatrix μ (matrixQuadratic H) j i =
      quadraticCovarianceMatrix μ (matrixQuadratic H) i j := by
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hZ i) j
  have hHij : H j i=H i j := by
    simpa only [Matrix.transpose_apply] using congrFun (congrFun hH i) j
  rw [hZij,hHij]

/-- Exact Frobenius expansion; every ordered off-diagonal entry is counted. -/
theorem actualFourthCumulantFlat_square_eq {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hQ : QuadraticVarianceEight μ)
    (H : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq (actualFourthCumulantFlat μ H) =
      matrixFrobeniusSq (quadraticCovarianceMatrix μ (matrixQuadratic H)) -
        4*ProbabilityTheory.variance (matrixQuadratic H) μ + 4*matrixFrobeniusSq H := by
  have hH := memLp_matrixQuadratic_of_coordinateProducts hQ.memLp_coordinate_mul H
  have hp := covariance_matrixQuadratic_eq_pairing hH hQ.memLp_coordinate_mul H
  rw [covariance_self hH.aemeasurable] at hp
  rw [hp]
  simp only [matrixFrobeniusSq,actualFourthCumulantFlat]
  simp only [Finset.mul_sum]
  simp only [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The covariance operator has spectrum in `[0,8]`; subtracting `2 I`
gives norm at most `6`. This proof uses the actual covariance and variance
identities directly, without a spectral assumption. -/
theorem QuadraticVarianceEight.fourthCumulantFlat_square_le
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hQ : QuadraticVarianceEight μ)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    matrixFrobeniusSq (actualFourthCumulantFlat μ H) ≤ 36*matrixFrobeniusSq H := by
  have hHlp := (hQ H hH).1
  have hv := (hQ H hH).2
  have hz := hQ.quadraticCovariance_frobeniusSq_le_variance hHlp
  rw [actualFourthCumulantFlat_square_eq hQ H]
  linarith

/-- Genuine original-class two-slot fourth-cumulant bound. -/
theorem actual_fourth_cumulant_flat_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    matrixFrobeniusSq (actualFourthCumulantFlat μ H) ≤ 36*matrixFrobeniusSq H := by
  let : IsProbabilityMeasure μ := hμ.isProb
  exact QuadraticVarianceEight.fourthCumulantFlat_square_le
    hμ.quadraticVarianceEight_unconditional H hH

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_fourth_cumulant_flat_square_le
