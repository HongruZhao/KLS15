import KLSConstantImprovement.ActualSourceDirectCubicBalance405
import KLSConstantImprovement.ActualSourceUnfilteredDeficit405
import Mathlib.Probability.Moments.Covariance

/-! The unfiltered actual Hessian/Gram BL cross is the signed direct
energy minus its literal covariance. This binds the same scalar form,
source and tensor to the direct cubic primitive without a free deficit
or covariance witness. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace ProbabilityTheory Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualDirectDeficitBinding405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405
open ActualSourceBLFilter405 ActualSourceMeanGram405 ActualSourceUnfilteredDeficit405
open ActualSourceDirectCubicEnergy405 ActualSourceDirectCubicBalance405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_base_hessian_value_ae (d : SourceData μ) (i j : Fin n) :
    (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] fun x => coordinateHessian d.potential x i j -
        ∫ y, coordinateHessian d.potential y i j ∂potentialMeasure d.potential := by
  simpa only [hessianCongruence, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
    actualHessianCongruenceForm_value_ae d 1 i j

theorem actual_base_hessian_gradient_ae (d : SourceData μ) (i j r : Fin n) :
    (canonicalMetricGradient d.potential r (actualHessianCongruenceForm d 1 i j) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r := by
  simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    ActualSourceHessianEvolution405.sourceThirdMatrix, Matrix.of_apply] using
    actualHessianCongruenceForm_gradient_ae d 1 i j r

theorem actual_base_HG_total_energy (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, canonicalMetricEnergy d.potential (actualHessianCongruenceForm d 1 i j)
      (actualTensorGramForm d T i j)) =
      ∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential := by
  have hi (i j r : Fin n) : Integrable (fun x =>
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential
          (ActualSourceTensorGramMetricBinding.sourceTensorGramRawDerivative d.potential d.third T i j) r x)
      (potentialMeasure d.potential) :=
    (d.hessian_entry_raw_metric_memLp i j r).integrable_mul (d.tensorGram_raw_metric_memLp T i j r)
  have he (i j r : Fin n) : inner ℝ
      (canonicalMetricGradient d.potential r (actualHessianCongruenceForm d 1 i j))
      (canonicalMetricGradient d.potential r (actualTensorGramForm d T i j)) =
      ∫ x, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential
          (ActualSourceTensorGramMetricBinding.sourceTensorGramRawDerivative d.potential d.third T i j) r x
        ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actual_base_hessian_gradient_ae d i j r,
      actualTensorGramForm_gradient_ae d T i j r] with x hx hy
    simp only [RCLike.inner_apply, conj_trivial, hx, hy]
    ring
  simp_rw [canonicalMetricEnergy_apply, he]
  unfold actualDirectCrossEnergy
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    integrable_finsetSum Finset.univ fun r _ => hi i j r)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ fun r _ => hi i j r)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_finsetSum Finset.univ (fun r _ => hi i j r)).symm

theorem actual_base_HG_total_covariance (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, inner ℝ
      (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
      (canonicalMetricValue d.potential (actualTensorGramForm d T i j))) =
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) - (sourceMeanGram d T).trace := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hHmean (i j : Fin n) : (∫ x, coordinateHessian d.potential x i j ∂potentialMeasure d.potential) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j :=
    integral_actual_hessian_entry_eq_one_C11 d.source_C1 d.gradient_lipschitz (d.pushforward.symm ▸ hiso) i j
  have hGvalue (i j : Fin n) :
      (canonicalMetricValue d.potential (actualTensorGramForm d T i j) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] fun x => matrixTraceGram (coordinateHessian d.potential x) T i j -
          sourceMeanGram d T i j := by
    simpa only [sourceTensorGramEntry_eq_matrixTraceGram, sourceMeanGram] using
      actualTensorGramForm_value_ae d T i j
  have hG (i j : Fin n) : MemLp (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j) 2
      (potentialMeasure d.potential) := (actual_direct_gram_entry_top d T i j).mono_exponent (by simp)
  have he (i j : Fin n) : inner ℝ
      (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
      (canonicalMetricValue d.potential (actualTensorGramForm d T i j)) =
      (∫ x, coordinateHessian d.potential x i j * matrixTraceGram (coordinateHessian d.potential x) T i j
        ∂potentialMeasure d.potential) - (1 : Matrix (Fin n) (Fin n) ℝ) i j * sourceMeanGram d T i j := by
    have hc : inner ℝ
        (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
        (canonicalMetricValue d.potential (actualTensorGramForm d T i j)) =
        covariance (fun x => coordinateHessian d.potential x i j)
          (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j) (potentialMeasure d.potential) := by
      rw [L2.inner_def]
      unfold covariance
      apply integral_congr_ae
      filter_upwards [actual_base_hessian_value_ae d i j, hGvalue i j] with x hx hy
      simp only [RCLike.inner_apply, conj_trivial, hx, hy, sourceMeanGram]
      ring
    rw [hc, covariance_eq_sub (d.hessian_entry_memLp i j 2) (hG i j), hHmean]
    rfl
  simp_rw [he, Finset.sum_sub_distrib]
  have hm : (∑ i, ∑ j, (1 : Matrix (Fin n) (Fin n) ℝ) i j * sourceMeanGram d T i j) =
      (sourceMeanGram d T).trace := by simp [Matrix.one_apply, Matrix.trace]
  rw [hm]
  congr 1
  have hi (i j : Fin n) : Integrable (fun x => coordinateHessian d.potential x i j *
      matrixTraceGram (coordinateHessian d.potential x) T i j) (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j 2).integrable_mul (hG i j)
  have hrow (i : Fin n) : (∑ j, ∫ x, coordinateHessian d.potential x i j *
      matrixTraceGram (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, coordinateHessian d.potential x i j * matrixTraceGram (coordinateHessian d.potential x) T i j
        ∂potentialMeasure d.potential := (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ => hi i j)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => matrix_entrywise_contraction_eq_trace _ _ (matrixTraceGram_symmetric _ T)

theorem actual_direct_unfiltered_deficit_identity (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    actualMatrixBLCross d 1 T =
      (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) -
        (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) + (sourceMeanGram d T).trace := by
  simp only [actualMatrixBLCross, sourceBLDefect_apply, Finset.sum_sub_distrib]
  rw [actual_base_HG_total_energy, actual_base_HG_total_covariance d hiso]
  ring

end KLSConstantImprovement.ActualDirectDeficitBinding405
#print axioms KLSConstantImprovement.ActualDirectDeficitBinding405.actual_base_HG_total_energy
#print axioms KLSConstantImprovement.ActualDirectDeficitBinding405.actual_base_HG_total_covariance
#print axioms KLSConstantImprovement.ActualDirectDeficitBinding405.actual_direct_unfiltered_deficit_identity
