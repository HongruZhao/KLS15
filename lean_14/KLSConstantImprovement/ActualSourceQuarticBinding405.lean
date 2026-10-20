import KLSConstantImprovement.ActualQuarticPointwise405
import KLSConstantImprovement.ActualQuarticPositiveGradient405
import KLSConstantImprovement.ActualSourceTensorGramMetricBinding

/-! The finite arbitrary-H quartic square on the actual constructed
weak source. The displayed derivatives are the genuine raw weak
derivatives already constructed from SourceData. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceQuarticBinding405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualSourceTensorGramMetricBinding ActualQuarticPositiveGradient405
open ActualQuarticCompression405 ActualQuarticCongruence405 ActualQuarticPointwise405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem rawGram_eq_matrixTraceGram (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : rawGram H T = matrixTraceGram H T := by
  ext i j
  simpa only [rawGram, matrixTraceGram, Matrix.mul_assoc] using
    (Matrix.trace_mul_comm H (T i * H * T j)).symm

theorem rawQuarticGradient_eq_actual (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    rawQuarticGradient H T = quarticMatrixGradient H T := by
  unfold rawQuarticGradient quarticMatrixGradient sliceMatrixContraction
  rw [rawGram_eq_matrixTraceGram]

theorem actual_gram_raw_derivative_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j a : Fin n) (x : Space n) :
    sourceTensorGramRawDerivative d.potential d.third T i j a x =
      rawGramDerivative (coordinateHessian d.potential x) T (sourceThirdMatrix d x a) i j := by
  simp only [sourceTensorGramRawDerivative, rawGramDerivative, sourceThirdMatrix,
    Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℝ => a + b)
  all_goals
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring

private theorem sum4_swap (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, f a b i j) = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  have hs : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2) =
      ∑ q : Fin n × Fin n, ∑ p : Fin n × Fin n, f p.1 p.2 q.1 q.2 :=
    Finset.sum_comm
  simpa only [Fintype.sum_prod_type] using hs

theorem actual_quartic_raw_energy_binding (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) =
      ∑ i, ∑ j, rawInverseHessianGradientForm d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) x := by
  simp only [quarticRawEnergy, entryPair, rawInverseHessianGradientForm,
    actual_gram_raw_derivative_binding, Finset.mul_sum]
  rw [sum4_swap]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem actual_quartic_raw_energy_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => quarticRawEnergy (coordinateHessian d.potential x) T
      (sourceThirdMatrix d x)) (potentialMeasure d.potential) := by
  have hi : Integrable (fun x => ∑ i, ∑ j,
      rawInverseHessianGradientForm d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) x)
      (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => d.tensorGram_raw_energy_integrable T i j
  exact hi.congr (Eventually.of_forall fun x => (actual_quartic_raw_energy_binding d T x).symm)

theorem actual_quartic_pointwise_commutator_square (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (quarticMatrixGradient (coordinateHessian d.potential x) T *
        matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace +
        quarticRawHessian (coordinateHessian d.potential x) T (sourceThirdMatrix d x) -
        quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) =
        (1 / 2 : ℝ) * quarticRawCommutatorCharge (coordinateHessian d.potential x) T
          (sourceThirdMatrix d x) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [d.hessian_ae_source, d.third_symmetric_ae.filter_mono hac.ae_le] with x hx hN
  have hN12 (i j k : Fin n) : sourceThirdMatrix d x i j k = sourceThirdMatrix d x j i k :=
    (hN i j k).1
  have hN23 (i j k : Fin n) : sourceThirdMatrix d x i j k = sourceThirdMatrix d x i k j :=
    (hN i j k).2
  simpa only [rawQuarticGradient_eq_actual, rawGram_eq_matrixTraceGram] using
    quartic_pointwise_commutator_square (coordinateHessian d.potential x) hx.1 T hT
      (sourceThirdMatrix d x) hN12 hN23

theorem actual_quartic_pointwise_energy_le (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) ≤
        (quarticMatrixGradient (coordinateHessian d.potential x) T *
          matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace +
          quarticRawHessian (coordinateHessian d.potential x) T (sourceThirdMatrix d x) := by
  filter_upwards [actual_quartic_pointwise_commutator_square d T hT] with x hx
  have hn := quarticRawCommutatorCharge_nonnegative (coordinateHessian d.potential x) T
    (sourceThirdMatrix d x)
  linarith

end KLSConstantImprovement.ActualSourceQuarticBinding405

#print axioms KLSConstantImprovement.ActualSourceQuarticBinding405.actual_gram_raw_derivative_binding
#print axioms KLSConstantImprovement.ActualSourceQuarticBinding405.actual_quartic_raw_energy_binding
#print axioms KLSConstantImprovement.ActualSourceQuarticBinding405.actual_quartic_raw_energy_integrable
#print axioms KLSConstantImprovement.ActualSourceQuarticBinding405.actual_quartic_pointwise_commutator_square
#print axioms KLSConstantImprovement.ActualSourceQuarticBinding405.actual_quartic_pointwise_energy_le
