import KLSConstantImprovement.ActualQuarticHessianTest405
import KLSConstantImprovement.ActualSourceHessianCongruence405
import KLSConstantImprovement.ActualSourceMeanGram405

/-! The bottom BL-defect is the literal tensor-Gram energy minus its
variance on the same actual source. Every scalar form, weak derivative,
mean and global energy domain is constructed. The upper kinetic bound
is a separate quartic commutator theorem. -/
noncomputable section
open Matrix MeasureTheory ProbabilityTheory InnerProductSpace Set Filter
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceTensorGramDefect405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualSourceTensorGramMetricBinding
open ActualQuarticHessianTest405 ActualSourceMeanGram405
open ActualSourceHessianCongruence405 ActualSourceBLFilter405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def actualTensorGramForm (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : CanonicalMetricH1 d.potential :=
  Classical.choose (d.exists_tensorGram_entry_metricH1 T i j)

theorem actualTensorGramForm_value_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (canonicalMetricValue d.potential (actualTensorGramForm d T i j) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x => sourceTensorGramEntry d.potential T i j x -
        ∫ y, sourceTensorGramEntry d.potential T i j y ∂potentialMeasure d.potential :=
  (Classical.choose_spec (d.exists_tensorGram_entry_metricH1 T i j)).1

theorem actualTensorGramForm_gradient_ae (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j r : Fin n) :
    (canonicalMetricGradient d.potential r (actualTensorGramForm d T i j) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) r :=
  (Classical.choose_spec (d.exists_tensorGram_entry_metricH1 T i j)).2 r

theorem actual_tensorGram_total_energy (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, canonicalMetricEnergy d.potential
      (actualTensorGramForm d T i j) (actualTensorGramForm d T i j)) =
    ∑ i, ∑ j, ∫ x, rawInverseHessianGradientForm d.potential
      (sourceTensorGramRawDerivative d.potential d.third T i j) x ∂potentialMeasure d.potential := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact actual_raw_form_self_energy d _ _ (actualTensorGramForm_gradient_ae d T i j)

theorem actual_tensorGram_total_variance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ‖canonicalMetricValue d.potential (actualTensorGramForm d T i j)‖ ^ 2) =
      (∫ x, matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T)
        ∂potentialMeasure d.potential) - matrixFrobeniusSq (sourceMeanGram d T) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hf (i j : Fin n) : MemLp (sourceTensorGramEntry d.potential T i j) 2
      (potentialMeasure d.potential) := (tensorGramTest d T i j).value_top.mono_exponent (by simp)
  have hentry (i j : Fin n) (x : Space n) : sourceTensorGramEntry d.potential T i j x =
      matrixTraceGram (coordinateHessian d.potential x) T i j :=
    (sourceTensorGramEntry_eq_trace d.potential T i j x).trans (traceGram_cyclic _ T i j).symm
  have hmean (i j : Fin n) : (∫ x, sourceTensorGramEntry d.potential T i j x
      ∂potentialMeasure d.potential) = sourceMeanGram d T i j :=
    integral_congr_ae (Eventually.of_forall (hentry i j))
  have he (i j : Fin n) :
      ‖canonicalMetricValue d.potential (actualTensorGramForm d T i j)‖ ^ 2 =
        variance (sourceTensorGramEntry d.potential T i j) (potentialMeasure d.potential) := by
    rw [ProbabilityTheory.variance_eq_integral (hf i j).aemeasurable,
      ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualTensorGramForm_value_ae d T i j] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
  have hv (i j : Fin n) : variance (sourceTensorGramEntry d.potential T i j)
      (potentialMeasure d.potential) =
      (∫ x, sourceTensorGramEntry d.potential T i j x ^ 2 ∂potentialMeasure d.potential) -
        sourceMeanGram d T i j ^ 2 := by
    rw [variance_eq_sub (hf i j), hmean]
    rfl
  simp_rw [he, hv, Finset.sum_sub_distrib]
  change (∑ i, ∑ j, ∫ x, sourceTensorGramEntry d.potential T i j x ^ 2
    ∂potentialMeasure d.potential) - _ = _
  congr 1
  have hrow (i : Fin n) :
      (∑ j, ∫ x, sourceTensorGramEntry d.potential T i j x ^ 2 ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, sourceTensorGramEntry d.potential T i j x ^ 2 ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ (fun j _ => (hf i j).integrable_sq)).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hf i j).integrable_sq))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [matrixFrobeniusSq, hentry]

theorem actual_tensorGram_BL_deficit_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, sourceBLDefect d (actualTensorGramForm d T i j) (actualTensorGramForm d T i j)) =
      (∑ i, ∑ j, ∫ x, rawInverseHessianGradientForm d.potential
        (sourceTensorGramRawDerivative d.potential d.third T i j) x ∂potentialMeasure d.potential) -
      (∫ x, matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T)
        ∂potentialMeasure d.potential) + matrixFrobeniusSq (sourceMeanGram d T) := by
  simp only [sourceBLDefect_apply, real_inner_self_eq_norm_sq, Finset.sum_sub_distrib]
  rw [actual_tensorGram_total_energy, actual_tensorGram_total_variance]
  ring

end KLSConstantImprovement.ActualSourceTensorGramDefect405
#print axioms KLSConstantImprovement.ActualSourceTensorGramDefect405.actual_tensorGram_total_energy
#print axioms KLSConstantImprovement.ActualSourceTensorGramDefect405.actual_tensorGram_total_variance
#print axioms KLSConstantImprovement.ActualSourceTensorGramDefect405.actual_tensorGram_BL_deficit_identity
