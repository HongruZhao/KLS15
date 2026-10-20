import KLSConstantImprovement.ActualBilinearMatrixCongruence405

/-! The genuine L2 scalar values of the Hessian/Gram forms transform by
constant congruence. Bilinearity therefore transports the SAME scalar
resolvent filter exactly through dual coefficient frames. -/
noncomputable section
open Matrix MeasureTheory Filter InnerProductSpace
open scoped BigOperators
namespace KLSConstantImprovement.ActualFilteredFrameInvariance405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCanonicalMetricResolvent
open ActualSourceMeanGram405 ActualSourceMeanGramCongruence405 ActualTensorRowCongruence405
open ActualSourceHessianCongruence405 ActualSourceTensorGramDefect405 ActualSourceMatchedDeficit405
open ActualFormMatrixPairing405 ActualMatchedFormInvariance405 ActualBilinearMatrixCongruence405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def lpMatrixValue (d : SourceData μ)
    (U : Fin n → Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => U i j x

theorem lp_matrix_congruence_ae (d : SourceData μ)
    (R S : Matrix (Fin n) (Fin n) ℝ)
    (U : Fin n → Fin n → Lp ℝ 2 (potentialMeasure d.potential)) (i j : Fin n) :
    ((linearMatrixCongruence R U S i j : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
      fun x => (R * lpMatrixValue d U x * S) i j := by
  let c : Fin n × Fin n → ℝ := fun p => R i p.1 * S p.2 j
  have hsm : ∀ᵐ x ∂potentialMeasure d.potential, ∀ p : Fin n × Fin n,
      (c p • U p.1 p.2) x = c p * U p.1 p.2 x := ae_all_iff.mpr fun p => by
    filter_upwards [Lp.coeFn_smul (c p) (U p.1 p.2)] with x hx
    exact hx
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun p : Fin n × Fin n => c p • U p.1 p.2), hsm]
    with x hx hs
  change (∑ p : Fin n × Fin n, c p • U p.1 p.2) x = _
  have hx' : (∑ p : Fin n × Fin n, c p • U p.1 p.2) x =
      ∑ p : Fin n × Fin n, (c p • U p.1 p.2) x := by
    simpa only [Finset.sum_apply] using hx
  rw [hx']
  simp_rw [hs]
  simp only [Fintype.sum_prod_type, c, lpMatrixValue, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem actual_hessian_value_L2_congruence (d : SourceData μ) (hiso : IsIsotropic μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    canonicalMetricValue d.potential (actualHessianCongruenceForm d R i j) =
      linearMatrixCongruence R
        (fun a b => canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 a b)) R.transpose i j := by
  apply Lp.ext
  filter_upwards [actual_hessian_form_value_matrix d hiso R, actual_hessian_form_value_matrix d hiso 1,
    lp_matrix_congruence_ae d R R.transpose
      (fun a b => canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 a b)) i j]
    with x hR h1 hc
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h1
  change lpMatrixValue d (fun a b => canonicalMetricValue d.potential
    (actualHessianCongruenceForm d 1 a b)) x = coordinateHessian d.potential x - 1 at h1
  rw [hc, h1]
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hR

theorem actual_gram_value_L2_row_congruence (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    canonicalMetricValue d.potential (actualTensorGramForm d (rowCongruentSlices T S) i j) =
      linearMatrixCongruence S.transpose
        (fun a b => canonicalMetricValue d.potential (actualTensorGramForm d T a b)) S i j := by
  apply Lp.ext
  filter_upwards [actual_gram_form_value_matrix d (rowCongruentSlices T S), actual_gram_form_value_matrix d T,
    lp_matrix_congruence_ae d S.transpose S
      (fun a b => canonicalMetricValue d.potential (actualTensorGramForm d T a b)) i j]
    with x hrow hbase hc
  change lpMatrixValue d (fun a b => canonicalMetricValue d.potential (actualTensorGramForm d T a b)) x =
    matrixTraceGram (coordinateHessian d.potential x) T - sourceMeanGram d T at hbase
  rw [hc, hbase]
  rw [matrixTraceGram_rowCongruentSlices, actual_meanGram_rowCongruentSlices] at hrow
  simp only [congruentMeanGram] at hrow
  rw [← Matrix.sub_mul, ← Matrix.mul_sub] at hrow
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hrow

def filteredScalarPair (d : SourceData μ) :
    Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ]
      Lp ℝ 2 (potentialMeasure d.potential) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _ -
    (2 : ℝ) • canonicalResolvent d.potential (t := 1) zero_lt_one)

theorem filteredScalarPair_apply (d : SourceData μ)
    (u v : Lp ℝ 2 (potentialMeasure d.potential)) :
    filteredScalarPair d u v = inner ℝ u
      (v - (2 : ℝ) • canonicalResolvent d.potential (t := 1) zero_lt_one v) := by
  simp only [filteredScalarPair, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply]

theorem actual_dual_frame_filter_cross_invariance (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (R S : Matrix (Fin n) (Fin n) ℝ) (hSR : S * R = 1) :
    actualMatrixFilterCross d R (rowCongruentSlices T S) = actualMatrixFilterCross d 1 T := by
  simp only [actualMatrixFilterCross, ← filteredScalarPair_apply]
  simp_rw [actual_hessian_value_L2_congruence d hiso R,
    actual_gram_value_L2_row_congruence d T S]
  exact bilinear_dual_matrix_congruence (filteredScalarPair d) R S hSR
    (fun i j => canonicalMetricValue d.potential (actualHessianCongruenceForm d 1 i j))
    (fun i j => canonicalMetricValue d.potential (actualTensorGramForm d T i j))

end KLSConstantImprovement.ActualFilteredFrameInvariance405

#print axioms KLSConstantImprovement.ActualFilteredFrameInvariance405.actual_hessian_value_L2_congruence
#print axioms KLSConstantImprovement.ActualFilteredFrameInvariance405.actual_gram_value_L2_row_congruence
#print axioms KLSConstantImprovement.ActualFilteredFrameInvariance405.actual_dual_frame_filter_cross_invariance
