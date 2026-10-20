import KLSConstantImprovement.ActualAffineFiniteExpansion405
import KLSConstantImprovement.ActualAffineGlobalBalance405
import KLSConstantImprovement.ActualSourceRawMetricPair405
import KLSConstantImprovement.ActualSourceDirectCubicBalance405

/-! The accepted bounded weak affine tests have the literal finite
derivatives used in the affine trace identity. No classical derivative
of the actual C1,1 source Hessian is taken. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineRawBindings405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualAffineFiniteExpansion405 ActualAffineMatrixTests405 ActualAffineGlobalBalance405
open ActualSourceHessianEvolution405 ActualSourceRawMetricPair405 ActualSourceQuarticBinding405
open ActualSourceDirectCubicBalance405 ActualQuarticCongruence405 ActualQuarticCompression405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def actualAffineCross (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  affineCross (coordinateHessian d.potential x) (actualAffineMatrix d T x) T (sourceThirdMatrix d x)

def actualAffineSignedConnection (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  affineSignedConnection (coordinateHessian d.potential x)⁻¹ (actualAffineMatrix d T x)
    (sourceThirdMatrix d x)

theorem affine_slice_derivative_omega (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (a b r : Fin n) (x : Space n) :
    (affineSliceTest d T a b).derivative r x =
      ActualQuarticThirdWhitening405.mixFamily (coordinateHessian d.potential x) T r a b := by
  rw [affineSliceTest_derivative]
  simp only [ActualQuarticThirdWhitening405.mixFamily, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem affine_hessian_test_raw_derivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j r : Fin n) (x : Space n) :
    (affineHessianTest d T i j).derivative r x =
      affineHessianDifferential (coordinateHessian d.potential x) (actualAffineMatrix d T x)
        T (sourceThirdMatrix d x) r i j := by
  change (∑ q, ∑ p,
    (((affineSliceTest d T i p).derivative r x * coordinateHessian d.potential x p q +
      (affineSliceTest d T i p).value x * d.third x r p q) * (affineSliceTest d T q j).value x +
      ((affineSliceTest d T i p).value x * coordinateHessian d.potential x p q) *
        (affineSliceTest d T q j).derivative r x)) = _
  simp only [affineSliceTest_value, affine_slice_derivative_omega, affineHessianDifferential,
    sourceThirdMatrix, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem affine_score_test_raw_derivative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (x : Space n) :
    (affineScoreTest d T r).derivative r x =
      affineScoreDifferential (coordinateHessian d.potential x) (actualAffineMatrix d T x)
        T (sourceThirdMatrix d x) r := by
  change (∑ a, ∑ q, ∑ p, ∑ b,
    (((((0 : ℝ) * coordinateHessian d.potential x b p + T r a b * d.third x r b p) *
      (affineSliceTest d T p q).value x + (T r a b * coordinateHessian d.potential x b p) *
        (affineSliceTest d T p q).derivative r x) * coordinateHessian d.potential x q a) +
      ((T r a b * coordinateHessian d.potential x b p) * (affineSliceTest d T p q).value x) *
        d.third x r q a)) = _
  simp only [zero_mul, zero_add, affineSliceTest_value, affine_slice_derivative_omega,
    affineScoreDifferential, sourceThirdMatrix, Matrix.of_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.add_apply, Matrix.mul_apply, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem actual_affine_score_raw_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ i, (affineScoreTest d T i).derivative i x) =
        actualDirectMoment d T x + 2 * actualAffineCross d T x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  simp only [affine_score_test_raw_derivative]
  have hNs (a : Fin n) : (sourceThirdMatrix d x a).IsSymm :=
    Matrix.IsSymm.ext fun i j => (hN a j i).2
  have he := affine_score_expansion (coordinateHessian d.potential x) (actualAffineMatrix d T x)
    T (sourceThirdMatrix d x) hx.1.isHermitian.isSymm (actualAffineMatrix_symmetric d T hT x) hT hNs
  simpa only [actualDirectMoment, rawGram_eq_matrixTraceGram, actualAffineCross] using he

private theorem sum4_exchange (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  have hs : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using hs

theorem actual_affine_metric_raw_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualAffineMetricPair d T x = actualAffineSignedConnection d T x + 2 * actualAffineCross d T x := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  have hp : ∀ᵐ x ∂potentialMeasure d.potential, ∀ i j,
      (∑ r, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (affineHessianTest d T i j).derivative r x) =
      ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b * d.third x a i j *
        (affineHessianTest d T i j).derivative b x :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => actual_raw_metric_pair_ae d
      (fun a y => d.third y a i j) (affineHessianTest d T i j).derivative
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le, hp] with x hx hN hp
  have hNs (a : Fin n) : (sourceThirdMatrix d x a).IsSymm :=
    Matrix.IsSymm.ext fun i j => (hN a j i).2
  have hJH : (coordinateHessian d.potential x)⁻¹ * coordinateHessian d.potential x = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have he := affine_hessian_metric_expansion (coordinateHessian d.potential x)⁻¹
    (coordinateHessian d.potential x) (actualAffineMatrix d T x) hJH T (sourceThirdMatrix d x)
    hx.1.isHermitian.isSymm (actualAffineMatrix_symmetric d T hT x) hT hNs
  change _ = affineSignedConnection _ _ _ + 2 * affineCross _ _ _ _
  rw [← he]
  unfold actualAffineMetricPair
  simp_rw [hp, affine_hessian_test_raw_derivative]
  rw [sum4_exchange]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [← (hNs a).eq, ← entryPair_eq_trace]
  simp only [entryPair, Finset.mul_sum, sourceThirdMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end KLSConstantImprovement.ActualAffineRawBindings405

#print axioms KLSConstantImprovement.ActualAffineRawBindings405.affine_hessian_test_raw_derivative
#print axioms KLSConstantImprovement.ActualAffineRawBindings405.affine_score_test_raw_derivative
#print axioms KLSConstantImprovement.ActualAffineRawBindings405.actual_affine_score_raw_binding
#print axioms KLSConstantImprovement.ActualAffineRawBindings405.actual_affine_metric_raw_binding
