import KLSConstantImprovement.ActualQuarticGradientVariation405
import KLSConstantImprovement.ActualQuarticRawDerivative405
import KLSConstantImprovement.ActualSourceQuarticBinding405
import KLSConstantImprovement.ActualSourceRawMetricPair405

/-! The actual weak A4 derivative pairing is exactly E4+HessG. This
identification uses only the constructed raw weak derivatives. It pays
the signed HessG term through a single actual L2 pairing instead of
assuming an independent integrability statement. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceQuarticVariation405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceTensorGramMetricBinding
open ActualQuarticHessianTest405 ActualQuarticRawDerivative405
open ActualQuarticCompression405 ActualQuarticCongruence405 ActualQuarticPointwise405
open ActualQuarticGradientVariation405 ActualSourceQuarticBinding405 ActualSourceRawMetricPair405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualQuarticGradientRawMatrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (quarticEntryTest d T i j).derivative r x

private theorem entry_product_expansion (H N A B : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (c e : ℝ) :
    (∑ q, ∑ p, (A i p * B q j) * (c * H p q + e * N p q)) =
      c * (A * H * B) i j + e * (A * N * B) i j := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a + b)
  all_goals
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro p _
    ring

theorem actual_quartic_gradient_derivative_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (x : Space n) :
    actualQuarticGradientRawMatrix d T r x =
      rawQuarticGradientVariation (coordinateHessian d.potential x) T (sourceThirdMatrix d x r) := by
  ext i j
  change (quarticEntryTest d T i j).derivative r x = _
  rw [quarticEntryTest_derivative]
  simp_rw [actual_gram_raw_derivative_binding, sourceTensorGramEntry_eq_trace]
  change 2 * (∑ a, ∑ b, ∑ q, ∑ p, (T a i p * T b q j) *
    (rawGramDerivative (coordinateHessian d.potential x) T (sourceThirdMatrix d x r) a b *
      coordinateHessian d.potential x p q + rawGram (coordinateHessian d.potential x) T a b *
        sourceThirdMatrix d x r p q)) = _
  simp_rw [entry_product_expansion]
  simp only [Finset.sum_add_distrib, rawQuarticGradientVariation, weightedSlice,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  ring

private theorem sum4_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
  have he : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, f p.1 p.2 q.1 q.2 := Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using he

theorem matrix_family_pair_reorder (J : Matrix (Fin n) (Fin n) ℝ)
    (N F : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ a, (N a).IsSymm) :
    (∑ i, ∑ j, ∑ a, ∑ b, J a b * N a i j * F b i j) =
      ∑ a, ∑ b, J a b * (N a * F b).trace := by
  rw [sum4_swap]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : (∑ i, ∑ j, N a i j * F b i j) = (N a * F b).trace := by
    calc
      _ = ∑ i, ∑ j, F b i j * N a i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (F b * N a).trace := matrix_entrywise_contraction_eq_trace _ _ (hN a)
      _ = _ := Matrix.trace_mul_comm _ _
  rw [← he]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def actualQuarticWeakPair (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ∑ i, ∑ j, ∑ r,
    rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
      rawCanonicalMetricDerivative d.potential (quarticEntryTest d T i j).derivative r x

theorem actual_quartic_weak_pair_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential, actualQuarticWeakPair d T x =
      quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) +
        quarticRawHessian (coordinateHessian d.potential x) T (sourceThirdMatrix d x) := by
  have hp (i j : Fin n) := actual_raw_metric_pair_ae d
    (fun a y => d.third y a i j) (quarticEntryTest d T i j).derivative
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i),
    d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hNs
  have hN (a : Fin n) : (sourceThirdMatrix d x a).IsSymm :=
    Matrix.IsSymm.ext fun i j => (hNs a j i).2
  calc
    actualQuarticWeakPair d T x = ∑ i, ∑ j, ∑ a, ∑ b,
        (coordinateHessian d.potential x)⁻¹ a b * sourceThirdMatrix d x a i j *
          actualQuarticGradientRawMatrix d T b x i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hx i j
    _ = ∑ a, ∑ b, (coordinateHessian d.potential x)⁻¹ a b *
        (sourceThirdMatrix d x a * actualQuarticGradientRawMatrix d T b x).trace :=
      matrix_family_pair_reorder _ _ _ hN
    _ = _ := by
      simp only [actual_quartic_gradient_derivative_binding, quartic_gradient_variation_pair,
        mul_add, Finset.sum_add_distrib, quarticRawEnergy, quarticRawHessian]

end KLSConstantImprovement.ActualSourceQuarticVariation405
#print axioms KLSConstantImprovement.ActualSourceQuarticVariation405.actual_quartic_gradient_derivative_binding
#print axioms KLSConstantImprovement.ActualSourceQuarticVariation405.actual_quartic_weak_pair_identity
