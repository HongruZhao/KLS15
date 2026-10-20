import ActualAppellAffineTransport
import ActualTiltWhitening
import ActualAppellJointContinuity
import KLS.AffinePotentialCutoff
import KLS.TensorCoordinateExpansion
import KLS.FrameHessianAlgebra

/-! The genuine covariance-normalized Appell energy is exactly the Appell
energy of the same affine-transformed law and test function. -/
noncomputable section
open MeasureTheory Set Filter Metric Matrix InnerProductSpace
open scoped Topology ENNReal BigOperators ContDiff
namespace KLS.DeterministicBridgeNext
open KLS.DeterministicBridgeIntegration KLS.TensorEnergy
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

 theorem affineMatrixEquiv_contLinear {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (b : Space n) (hP : P.det ≠ 0) :
    (affineMatrixEquiv P b hP).toContinuousAffineMap.contLinear = matrixAction P := by
  ext x i
  rfl

 theorem rowVector_eq_matrixAction_transpose_single {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    rowVector P i = matrixAction P.transpose (EuclideanSpace.single i 1) := by
  apply PiLp.ext
  intro j
  rw [rowVector_apply,matrixAction_apply]
  simp only [Matrix.transpose_apply,EuclideanSpace.single_apply]
  simp

 theorem actualAppellCoefficient_affineMatrixEquiv {n r : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (P : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hP : P.det ≠ 0)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) (a : Fin r → Fin n) :
    actualAppellCoefficient (μ.map (affineMatrixEquiv P b hP))
      (fun y => f ((affineMatrixEquiv P b hP).symm y)) r a =
      (tensorMatrix P *ᵥ (fun a => actualAppellCoefficient μ f r a)) a := by
  unfold actualAppellCoefficient
  rw [actualAppell_mixed_affine_transport hLC _ hf,
    affineMatrixEquiv_contLinear,← matrixAction_transpose_adjoint]
  change (iteratedFDeriv ℝ r (fun z => ∫ x, f x ∂exponentialTilt μ z) 0)
    (fun i => matrixAction P.transpose (EuclideanSpace.single (a i) 1)) =
    (tensorMatrix P *ᵥ tensorCoordinates
      (iteratedFDeriv ℝ r (fun z => ∫ x, f x ∂exponentialTilt μ z) 0)) a
  simpa only [rowVector_eq_matrixAction_transpose_single] using
    (tensorCoordinates_transform
      (iteratedFDeriv ℝ r (fun z => ∫ x, f x ∂exponentialTilt μ z) 0) P a).symm

 def actualCovarianceAppellEnergy {n : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (r : ℕ) : ℝ :=
  tensorMetric (covarianceMatrix μ) (fun a => actualAppellCoefficient μ f r a)

 def actualWhiteningEquiv {n : ℕ} (μ : Measure (Space n))
    (hp : (covarianceMatrix μ).PosDef) : Space n ≃ᴬ[ℝ] Space n :=
  affineMatrixEquiv (inverseSqrtMatrix (covarianceMatrix μ))
    (-matrixAction (inverseSqrtMatrix (covarianceMatrix μ)) (∫ x, x ∂μ))
    (inverseSqrtMatrix_det_ne_zero_of_posDef hp)

 theorem actualWhiteningEquiv_map_eq {n : ℕ} (μ : Measure (Space n))
    (hp : (covarianceMatrix μ).PosDef) :
    μ.map (actualWhiteningEquiv μ hp) = whitenedMeasure μ := rfl

 theorem actualAppellEnergy_whitening {n r : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hLC : measureLogConcave μ)
    (hp : (covarianceMatrix μ).PosDef) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergy (whitenedMeasure μ)
      (fun y => f ((actualWhiteningEquiv μ hp).symm y)) r =
      actualCovarianceAppellEnergy μ f r := by
  let P := inverseSqrtMatrix (covarianceMatrix μ)
  have hPs : P.transpose = P := (inverseSqrtMatrix_isSymm _).eq
  have hPn : P.det ≠ 0 := inverseSqrtMatrix_det_ne_zero_of_posDef hp
  have hwhite : P*covarianceMatrix μ*P = 1 := by
    simpa only [P,(inverseSqrtMatrix_isSymm (covarianceMatrix μ)).eq] using
      inverseSqrtMatrix_mul_self_mul_transpose hp
  unfold actualCovarianceAppellEnergy
  rw [tensorMetric_eq_whitened (covarianceMatrix μ) P hPs hPn hwhite]
  rw [← actualWhiteningEquiv_map_eq μ hp]
  unfold actualAppellEnergy actualWhiteningEquiv
  simp_rw [actualAppellCoefficient_affineMatrixEquiv hLC _ _ _ hf]
  simp only [dotProduct,pow_two]
  rfl

 theorem actual_whitening_test_memLp {n : ℕ} {μ : Measure (Space n)}
    (hp : (covarianceMatrix μ).PosDef) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun y => f ((actualWhiteningEquiv μ hp).symm y)) 2 (whitenedMeasure μ) := by
  rw [← actualWhiteningEquiv_map_eq μ hp]
  have he := (actualWhiteningEquiv μ hp).toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff
    (μ := μ) (p := (2 : ℝ≥0∞)) (g := fun y => f ((actualWhiteningEquiv μ hp).symm y))
  apply he.mpr
  convert hf using 1
  funext x
  change f ((actualWhiteningEquiv μ hp).symm ((actualWhiteningEquiv μ hp) x)) = f x
  rw [ContinuousAffineEquiv.symm_apply_apply]

 theorem actual_whitening_test_L2_energy {n : ℕ} (μ : Measure (Space n))
    (hp : (covarianceMatrix μ).PosDef) (f : Space n → ℝ) :
    (∫ y, (f ((actualWhiteningEquiv μ hp).symm y))^2 ∂whitenedMeasure μ) =
      ∫ x, (f x)^2 ∂μ := by
  rw [← actualWhiteningEquiv_map_eq μ hp]
  exact actual_affine_L2_energy_transport μ _ f

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppellEnergy_whitening
#print axioms KLS.DeterministicBridgeNext.actual_whitening_test_memLp
