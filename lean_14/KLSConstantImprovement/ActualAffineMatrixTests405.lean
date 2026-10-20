import KLSConstantImprovement.ActualBoundedRawSourceCalculus405
import KLSConstantImprovement.ActualQuarticHessianTest405

/-! Literal affine matrix fields A=T_X and AHA are actual bounded weak
tests on the same source. Every raw derivative and metric domain comes
from the proved X/H test algebra, without classical source smoothness. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineMatrixTests405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualBoundedRawTestAlgebra405 ActualQuarticHessianTest405
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualBoundedRawSourceCalculus405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualAffineMatrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, gradient d.potential x i • T i

def affineSliceTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) : BoundedRawTest d :=
  rawTestSum fun i => (BoundedRawTest.const d (T i a b)).mul
    (ActualBoundedRawSourceCalculus405.BoundedRawTest.coordinate d i)

theorem affineSliceTest_value (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) (x : Space n) :
    (affineSliceTest d T a b).value x = actualAffineMatrix d T x a b := by
  change (∑ i, T i a b * gradient d.potential x i) = _
  simp only [actualAffineMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem affineSliceTest_derivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b r : Fin n) (x : Space n) :
    (affineSliceTest d T a b).derivative r x =
      ∑ i, T i a b * coordinateHessian d.potential x r i := by
  change (∑ i, ((0 : ℝ) * gradient d.potential x i +
    T i a b * coordinateHessian d.potential x r i)) = _
  simp only [zero_mul, zero_add]

theorem actualAffineMatrix_symmetric (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) (x : Space n) :
    (actualAffineMatrix d T x).IsSymm := by
  change (∑ i, gradient d.potential x i • T i).transpose = _
  simp only [Matrix.transpose_sum, Matrix.transpose_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [(hT i).eq]

def affineHessianTest (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) : BoundedRawTest d :=
  rawTestSum fun q : Fin n => rawTestSum fun p : Fin n =>
    ((affineSliceTest d T a p).mul (BoundedRawTest.hessian d p q)).mul (affineSliceTest d T q b)

theorem affineHessianTest_value (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) (x : Space n) :
    (affineHessianTest d T a b).value x =
      (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) a b := by
  change (∑ q, ∑ p, ((affineSliceTest d T a p).value x * coordinateHessian d.potential x p q) *
    (affineSliceTest d T q b).value x) = _
  simp only [affineSliceTest_value, Matrix.mul_apply, Finset.sum_mul]

theorem actual_affine_hessian_positive (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x).PosSemidef := by
  filter_upwards [d.hessian_ae_source] with x hx
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
    (actualAffineMatrix_symmetric d T hT x).eq] using
    hx.1.posSemidef.conjTranspose_mul_mul_same (actualAffineMatrix d T x)

theorem actual_affine_global_hessian_test (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b i j : Fin n) :
    (∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun k y => d.third y k i j) r x *
        rawCanonicalMetricDerivative d.potential (affineHessianTest d T a b).derivative r x
          ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) a b
          ∂potentialMeasure d.potential := by
  simpa only [affineHessianTest_value] using (affineHessianTest d T a b).global_hessian_test i j

theorem actual_affine_curvature_pair_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => ((actualAffineMatrix d T x * coordinateHessian d.potential x *
      actualAffineMatrix d T x) * sourceConnectionCurvature d x).trace)
        (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j,
    (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) i j *
      sourceConnectionCurvature d x j i) (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => (affineHessianTest d T i j).value x * sourceConnectionCurvature d x j i)
      1 (potentialMeasure d.potential) := (affineHessianTest d T i j).value_top.mul
        (memLp_one_iff_integrable.mpr (actual_connection_curvature_entry_integrable d j i))
  simpa only [affineHessianTest_value] using hm.integrable le_rfl

theorem actual_affine_curvature_pair_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ ∫ x, ((actualAffineMatrix d T x * coordinateHessian d.potential x *
      actualAffineMatrix d T x) * sourceConnectionCurvature d x).trace
        ∂potentialMeasure d.potential := by
  apply integral_nonneg_of_ae
  filter_upwards [actual_affine_hessian_positive d T hT,
    actual_source_connection_curvature_positive d] with x hx hy
  exact trace_mul_nonneg_of_posSemidef hx hy

end KLSConstantImprovement.ActualAffineMatrixTests405
#print axioms KLSConstantImprovement.ActualAffineMatrixTests405.affineSliceTest_derivative
#print axioms KLSConstantImprovement.ActualAffineMatrixTests405.affineHessianTest
#print axioms KLSConstantImprovement.ActualAffineMatrixTests405.actual_affine_global_hessian_test
#print axioms KLSConstantImprovement.ActualAffineMatrixTests405.actual_affine_curvature_pair_integrable
#print axioms KLSConstantImprovement.ActualAffineMatrixTests405.actual_affine_curvature_pair_nonnegative
