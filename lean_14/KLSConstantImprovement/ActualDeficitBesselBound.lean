import KLSConstantImprovement.ActualDeficitTensorBounds
import KLSConstantImprovement.QuadraticCovarianceCharge

/-! Joint original-law control of the third-cumulant annihilation and the
fourth contraction. All ordered indices and the sign of Tr(A^2) are retained.
The quadratic coordinate covariance is used on the same measure throughout. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDeficitBesselBound
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
open ActualDeficitTensorBounds QuadraticCovarianceCharge
variable {n : ℕ}
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def annihilationSquare (μ : Measure (Space n)) (T : Array3 (Fin n)) : ℝ :=
  ∑ i, ∑ j, (annihilation (actualThirdCubicArray μ) T i j)^2

theorem annihilation_eq_quadratic_covariance {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) (i j : Fin n) :
    annihilation (actualThirdCubicArray μ) T i j =
      covarianceVector μ (matrixQuadratic (T j)) i := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hi (a b : Fin n) : Integrable (fun x : Space n =>
      T j a b*(x a*x b*x i)) μ :=
    (((hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul a b).integrable_mul
      (hμ.isotropic.memLp_coordinate i)).const_mul (T j a b))
  have he : (fun x : Space n => x i*matrixQuadratic (T j) x) =
      fun x => ∑ a, ∑ b, T j a b*(x a*x b*x i) := by
    funext x
    unfold matrixQuadratic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  change _ = ∫ x, x i*matrixQuadratic (T j) x ∂μ
  rw [he, integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ fun b _ => hi a b)]
  unfold annihilation actualThirdCubicArray
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (fun b _ => hi a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, thirdCumulantMatrix_coordinate_eq_cubic]
  have hm : (∫ x : Space n, x b*x i*x a ∂μ) = ∫ x, x a*x b*x i ∂μ := by
    apply integral_congr_ae
    exact .of_forall fun x => by ring
  rw [hm]
  ring

theorem annihilation_column_square_le_variance {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) (j : Fin n) :
    (∑ i, (annihilation (actualThirdCubicArray μ) T i j)^2) ≤
      ProbabilityTheory.variance (matrixQuadratic (T j)) μ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hf := memLp_matrixQuadratic_of_coordinateProducts
    hμ.quadraticVarianceEight_unconditional.memLp_coordinate_mul (T j)
  have hb := covarianceVector_norm_sq_le_variance hμ.isotropic hf
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  simpa only [annihilation_eq_quadratic_covariance hμ T] using hb

theorem annihilationSquare_le_fourth_add_two {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    annihilationSquare μ T ≤ fourthContraction μ T+2*tensorSquare T := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => annihilation_column_square_le_variance hμ T j)
  have hv (j : Fin n) : ProbabilityTheory.variance (matrixQuadratic (T j)) μ =
      (∑ a, ∑ b, T j a b*actualFourthCumulantFlat μ (T j) a b)+
        2*matrixFrobeniusSq (T j) := by
    have hh := actualFourthCumulantFlat_pairing_eq_variance_sub_two
      hμ.quadraticVarianceEight_unconditional (T j)
    linarith
  simp_rw [hv] at hb
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←tensorSquare_eq_sum_slices] at hb
  unfold annihilationSquare
  rw [Finset.sum_comm]
  exact hb

theorem matrix_trace_square_bounds (A : Fin n → Fin n → ℝ) :
    -(∑ i, ∑ j, (A i j)^2) ≤ (∑ i, ∑ j, A i j*A j i) ∧
      (∑ i, ∑ j, A i j*A j i) ≤ ∑ i, ∑ j, (A i j)^2 := by
  have ht : (∑ i, ∑ j, (A j i)^2) = ∑ i, ∑ j, (A i j)^2 := Finset.sum_comm
  have hp : 0 ≤ ∑ i, ∑ j, (A i j+A j i)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm : 0 ≤ ∑ i, ∑ j, (A i j-A j i)^2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have he (s : ℝ) : (∑ i, ∑ j, (A i j+s*A j i)^2) =
      (∑ i, ∑ j, (A i j)^2)+2*s*(∑ i, ∑ j, A i j*A j i)+
        s^2*(∑ i, ∑ j, (A j i)^2) := by
    simp only [Finset.mul_sum, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have heP := he 1
  have heM := he (-1)
  simp only [one_mul, one_pow, mul_one, ht] at heP
  simp only [neg_one_mul, neg_one_sq, one_mul, ht] at heM
  simp only [sub_eq_add_neg] at hm
  constructor <;> nlinarith

theorem signedTraceSquare_bounds_by_annihilationSquare
    (μ : Measure (Space n)) (T : Array3 (Fin n)) :
    -annihilationSquare μ T ≤ signedTraceSquare μ T ∧
      signedTraceSquare μ T ≤ annihilationSquare μ T :=
  matrix_trace_square_bounds (annihilation (actualThirdCubicArray μ) T)

theorem signedTraceSquare_bounds_by_fourth_add_two {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (T : Array3 (Fin n)) :
    -(fourthContraction μ T+2*tensorSquare T) ≤ signedTraceSquare μ T ∧
      signedTraceSquare μ T ≤ fourthContraction μ T+2*tensorSquare T := by
  have hA := annihilationSquare_le_fourth_add_two hμ T
  have hS := signedTraceSquare_bounds_by_annihilationSquare μ T
  constructor <;> linarith

end KLSConstantImprovement.ActualDeficitBesselBound
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.annihilation_eq_quadratic_covariance
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.annihilation_column_square_le_variance
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.annihilationSquare_le_fourth_add_two
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.matrix_trace_square_bounds
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.signedTraceSquare_bounds_by_annihilationSquare
#print axioms KLSConstantImprovement.ActualDeficitBesselBound.signedTraceSquare_bounds_by_fourth_add_two
