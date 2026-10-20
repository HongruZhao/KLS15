import KLSConstantImprovement.ActualFormMatrixPairing405
import KLSConstantImprovement.ActualDirectDeficitBinding405

/-! Exact dual-frame invariance of the actual unfiltered Hessian/Gram
BL cross. Both scalar form families, their weak gradients, means and
covariances are the genuine constructed fields on the same source. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualMatchedFormInvariance405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405 ActualSourceBLFilter405
open ActualSourceMeanGram405 ActualSourceMeanGramCongruence405 ActualTensorRowCongruence405
open ActualQuarticCompression405 ActualSourceDirectCubicBalance405 ActualSourceUnfilteredDeficit405
open ActualFormMatrixPairing405 ActualMetricMatrixCongruence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_hessian_form_value_matrix (d : SourceData μ) (hiso : IsIsotropic μ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      formValueMatrix d (actualHessianCongruenceForm d R) x =
        R * (coordinateHessian d.potential x - 1) * R.transpose := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm (i j : Fin n) := integral_hessianCongruence_entry_C11 d.source_C1 d.gradient_lipschitz
    (d.pushforward.symm ▸ hiso) R i j
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    actualHessianCongruenceForm_value_ae d R i j] with x hx
  ext i j
  change canonicalMetricValue d.potential (actualHessianCongruenceForm d R i j) x = _
  rw [hx i j, hm i j]
  simp only [hessianCongruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.sub_apply]

theorem actual_gram_form_value_matrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      formValueMatrix d (actualTensorGramForm d T) x =
        matrixTraceGram (coordinateHessian d.potential x) T - sourceMeanGram d T := by
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    actualTensorGramForm_value_ae d T i j] with x hx
  ext i j
  change canonicalMetricValue d.potential (actualTensorGramForm d T i j) x = _
  rw [hx i j]
  simp only [sourceTensorGramEntry_eq_matrixTraceGram, sourceMeanGram, Matrix.sub_apply]

theorem actual_hessian_form_gradient_matrix (d : SourceData μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      formGradientMatrix d (actualHessianCongruenceForm d R) r x =
        R * hessianMetricMatrix d r x * R.transpose := by
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    actualHessianCongruenceForm_gradient_ae d R i j r] with x hx
  ext i j
  change canonicalMetricGradient d.potential r (actualHessianCongruenceForm d R i j) x = _
  rw [hx i j]
  exact ((rawMetricMatrix_apply d
    (fun a y => R * ActualSourceHessianEvolution405.sourceThirdMatrix d y a * R.transpose) r i j x).symm.trans
      (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
        (rawMetricMatrix_congruence d (fun a y => ActualSourceHessianEvolution405.sourceThirdMatrix d y a)
          R R.transpose r x)))

theorem actual_gram_form_gradient_matrix (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (r : Fin n) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      formGradientMatrix d (actualTensorGramForm d T) r x = gramMetricMatrix d T r x := by
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    actualTensorGramForm_gradient_ae d T i j r] with x hx
  ext i j
  change canonicalMetricGradient d.potential r (actualTensorGramForm d T i j) x = _
  rw [hx i j, gramMetricMatrix_apply]

theorem actual_dual_frame_energy_invariance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hSR : S * R = 1) :
    (∑ i, ∑ j, canonicalMetricEnergy d.potential (actualHessianCongruenceForm d R i j)
      (actualTensorGramForm d (rowCongruentSlices T S) i j)) =
      ∑ i, ∑ j, canonicalMetricEnergy d.potential (actualHessianCongruenceForm d 1 i j)
        (actualTensorGramForm d T i j) := by
  rw [actual_form_matrix_energy_pair, actual_form_matrix_energy_pair]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (actual_hessian_form_gradient_matrix d R),
    ae_all_iff.mpr (actual_hessian_form_gradient_matrix d 1),
    ae_all_iff.mpr (actual_gram_form_gradient_matrix d (rowCongruentSlices T S)),
    ae_all_iff.mpr (actual_gram_form_gradient_matrix d T)] with x hH hH0 hG hG0
  apply Finset.sum_congr rfl
  intro r _
  rw [hH r, hH0 r, hG r, hG0 r, gramMetricMatrix_rowCongruence]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  exact entryPair_dual_congruence R S _ _ hSR

theorem actual_dual_frame_covariance_invariance (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hSR : S * R = 1) :
    (∑ i, ∑ j, inner ℝ (canonicalMetricValue d.potential (actualHessianCongruenceForm d R i j))
      (canonicalMetricValue d.potential (actualTensorGramForm d (rowCongruentSlices T S) i j))) =
      ∑ i, ∑ j, inner ℝ (canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
        (canonicalMetricValue d.potential (actualTensorGramForm d T i j)) := by
  rw [actual_form_matrix_value_pair, actual_form_matrix_value_pair]
  apply integral_congr_ae
  filter_upwards [actual_hessian_form_value_matrix d hiso R, actual_hessian_form_value_matrix d hiso 1,
    actual_gram_form_value_matrix d (rowCongruentSlices T S), actual_gram_form_value_matrix d T]
    with x hH hH0 hG hG0
  rw [hH, hH0, hG, hG0, matrixTraceGram_rowCongruentSlices, actual_meanGram_rowCongruentSlices]
  simp only [congruentMeanGram, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact entryPair_dual_congruence R S _ _ hSR

theorem actual_dual_frame_BL_cross_invariance (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hSR : S * R = 1) :
    actualMatrixBLCross d R (rowCongruentSlices T S) = actualMatrixBLCross d 1 T := by
  simp only [actualMatrixBLCross, sourceBLDefect_apply, Finset.sum_sub_distrib]
  rw [actual_dual_frame_energy_invariance d T R S hSR,
    actual_dual_frame_covariance_invariance d hiso T R S hSR]

end KLSConstantImprovement.ActualMatchedFormInvariance405
#print axioms KLSConstantImprovement.ActualMatchedFormInvariance405.actual_hessian_form_gradient_matrix
#print axioms KLSConstantImprovement.ActualMatchedFormInvariance405.actual_dual_frame_energy_invariance
#print axioms KLSConstantImprovement.ActualMatchedFormInvariance405.actual_dual_frame_covariance_invariance
#print axioms KLSConstantImprovement.ActualMatchedFormInvariance405.actual_dual_frame_BL_cross_invariance
