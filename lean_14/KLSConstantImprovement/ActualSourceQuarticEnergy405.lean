import KLSConstantImprovement.ActualSourceQuarticVariation405
import KLSConstantImprovement.ActualQuarticGlobalBalance405
import KLSConstantImprovement.ActualSourceTensorGramDefect405

/-! Quartic kinetic control and the bottom BL-defect cap on the actual
weak source. The signed quartic Hessian term is eliminated through the
literal finite-energy weak pairing; no separate absolute-integrability
hypothesis for that signed contraction is imposed. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualSourceQuarticEnergy405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceTensorGramMetricBinding
open ActualQuarticPositiveGradient405 ActualQuarticHessianTest405
open ActualQuarticGlobalBalance405 ActualQuarticPointwise405
open ActualSourceQuarticBinding405 ActualSourceQuarticVariation405
open ActualSourceTensorGramDefect405 ActualSourceBLFilter405 ActualSourceMeanGram405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_quartic_weak_pair_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualQuarticWeakPair d T) (potentialMeasure d.potential) := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  apply integrable_finsetSum Finset.univ
  intro r _
  exact (d.hessian_entry_raw_metric_memLp i j r).integrable_mul
    ((quarticEntryTest d T i j).metric_gradient r)

theorem actual_quartic_weak_pair_integral (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, actualQuarticWeakPair d T x ∂potentialMeasure d.potential) =
      2 * (∫ x, matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T)
        ∂potentialMeasure d.potential) -
      ∫ x, (quarticMatrixGradient (coordinateHessian d.potential x) T *
        sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential := by
  have hi (i j : Fin n) : Integrable (fun x => ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (quarticEntryTest d T i j).derivative r x)
      (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun r _ =>
      (d.hessian_entry_raw_metric_memLp i j r).integrable_mul
        ((quarticEntryTest d T i j).metric_gradient r)
  have hrow (i : Fin n) :
      (∫ x, ∑ j, ∑ r,
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
          rawCanonicalMetricDerivative d.potential (quarticEntryTest d T i j).derivative r x
        ∂potentialMeasure d.potential) = ∑ j, ∫ x, ∑ r,
        rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
          rawCanonicalMetricDerivative d.potential (quarticEntryTest d T i j).derivative r x
        ∂potentialMeasure d.potential :=
    integral_finsetSum Finset.univ fun j _ => hi i j
  unfold actualQuarticWeakPair
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [hrow]
  exact actual_quartic_global_balance d T hT

theorem actual_quartic_gamma_pair_le_curvature (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (quarticMatrixGradient (coordinateHessian d.potential x) T *
        matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace ≤
      (quarticMatrixGradient (coordinateHessian d.potential x) T *
        sourceConnectionCurvature d x).trace := by
  filter_upwards [d.hessian_ae_source, actual_quartic_gradient_positive_ae d T hT] with x hx hA
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (coordinateHessian d.potential x *
      coordinateHessian d.targetPotential (gradient d.potential x) *
        coordinateHessian d.potential x).PosSemidef := by
    simpa only [hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  have hn := trace_mul_nonneg_of_posSemidef hA hP
  simp only [sourceConnectionCurvature, Matrix.mul_add, Matrix.trace_add]
  linarith

theorem actual_quartic_energy_le_moment (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x)
      ∂potentialMeasure d.potential) ≤
      ∫ x, matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T)
        ∂potentialMeasure d.potential := by
  have hp : ∀ᵐ x ∂potentialMeasure d.potential,
      2 * quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x) ≤
        (quarticMatrixGradient (coordinateHessian d.potential x) T *
          sourceConnectionCurvature d x).trace + actualQuarticWeakPair d T x := by
    filter_upwards [actual_quartic_pointwise_energy_le d T hT,
      actual_quartic_gamma_pair_le_curvature d T hT,
      actual_quartic_weak_pair_identity d T] with x hE hC hP
    linarith
  have hi := integral_mono_ae
    ((actual_quartic_raw_energy_integrable d T).const_mul 2)
    ((actual_quartic_curvature_pair_integrable d T).add
      (actual_quartic_weak_pair_integrable d T)) hp
  dsimp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (actual_quartic_curvature_pair_integrable d T)
    (actual_quartic_weak_pair_integrable d T), actual_quartic_weak_pair_integral d T hT] at hi
  linarith

theorem actual_tensorGram_BL_deficit_cap (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ (∑ i, ∑ j, sourceBLDefect d (actualTensorGramForm d T i j)
        (actualTensorGramForm d T i j)) ∧
      (∑ i, ∑ j, sourceBLDefect d (actualTensorGramForm d T i j)
        (actualTensorGramForm d T i j)) ≤ matrixFrobeniusSq (sourceMeanGram d T) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      sourceBLDefect_nonnegative d _
  · rw [actual_tensorGram_BL_deficit_identity]
    have he := actual_quartic_energy_le_moment d T hT
    have hei : (∫ x, quarticRawEnergy (coordinateHessian d.potential x) T (sourceThirdMatrix d x)
        ∂potentialMeasure d.potential) =
      ∑ i, ∑ j, ∫ x, rawInverseHessianGradientForm d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) x ∂potentialMeasure d.potential := by
      simp_rw [actual_quartic_raw_energy_binding]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => d.tensorGram_raw_energy_integrable T i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum Finset.univ fun j _ => d.tensorGram_raw_energy_integrable T i j
    rw [hei] at he
    linarith

end KLSConstantImprovement.ActualSourceQuarticEnergy405
#print axioms KLSConstantImprovement.ActualSourceQuarticEnergy405.actual_quartic_weak_pair_integral
#print axioms KLSConstantImprovement.ActualSourceQuarticEnergy405.actual_quartic_gamma_pair_le_curvature
#print axioms KLSConstantImprovement.ActualSourceQuarticEnergy405.actual_quartic_energy_le_moment
#print axioms KLSConstantImprovement.ActualSourceQuarticEnergy405.actual_tensorGram_BL_deficit_cap
