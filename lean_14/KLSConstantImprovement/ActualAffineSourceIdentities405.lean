import KLSConstantImprovement.ActualAffineRawBindings405

/-! Actual affine trace identities with every global integral paid.
The source Hessian test and source Stein identity are the accepted weak
ones; E1 is retained with its sign. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualAffineSourceIdentities405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
open ActualBoundedRawSourceCalculus405 ActualAffineMatrixTests405 ActualAffineGlobalBalance405
open ActualAffineRawBindings405 ActualSourceDirectCubicBalance405
open ActualSourceCurvatureDomains405 ActualSourceQuarticBinding405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def actualAffineGamma (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
    matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x)).trace

def actualAffineTarget (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
    sourceTargetCurvature d x).trace

theorem actual_affine_score_sum_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => ∑ i, (affineScoreTest d T i).derivative i x) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact integrable_finsetSum Finset.univ fun i _ =>
    (ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp
      (affineScoreTest d T i) i).integrable (by norm_num)

theorem actual_affine_cross_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Integrable (actualAffineCross d T) (potentialMeasure d.potential) := by
  have hi := ((actual_affine_score_sum_integrable d T).sub (actual_direct_moment_integrable d T)).div_const 2
  apply hi.congr
  filter_upwards [actual_affine_score_raw_binding d T hT] with x hx
  change ((∑ i, (affineScoreTest d T i).derivative i x) - actualDirectMoment d T x) / 2 = _
  linarith

theorem actual_affine_signed_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    Integrable (actualAffineSignedConnection d T) (potentialMeasure d.potential) := by
  have hi := (actual_affine_metric_pair_integrable d T).sub
    ((actual_affine_cross_integrable d T hT).const_mul 2)
  apply hi.congr
  filter_upwards [actual_affine_metric_raw_binding d T hT] with x hx
  change actualAffineMetricPair d T x - 2 * actualAffineCross d T x = _
  linarith

theorem actual_affine_gamma_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualAffineGamma d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j,
    (actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) i j *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) j i)
        (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => (affineHessianTest d T i j).value x *
      matrixTraceGram (coordinateHessian d.potential x)⁻¹ (sourceThirdMatrix d x) j i) 1
      (potentialMeasure d.potential) :=
    (affineHessianTest d T i j).value_top.mul
      (memLp_one_iff_integrable.mpr (actual_third_gram_entry_integrable d j i))
  simpa only [affineHessianTest_value] using hm.integrable le_rfl

theorem actual_affine_curvature_split (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
      sourceConnectionCurvature d x).trace = actualAffineTarget d T x + actualAffineGamma d T x := by
  simp only [actualAffineTarget, actualAffineGamma, sourceConnectionCurvature,
    sourceTargetCurvature, Matrix.mul_add, Matrix.trace_add]

theorem actual_affine_target_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualAffineTarget d T) (potentialMeasure d.potential) := by
  apply ((actual_affine_curvature_pair_integrable d T).sub (actual_affine_gamma_integrable d T)).congr
  exact Eventually.of_forall fun x => by
    change ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
      sourceConnectionCurvature d x).trace - actualAffineGamma d T x = _
    rw [actual_affine_curvature_split]
    ring

theorem actual_affine_main_cross_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, actualAffineMainCost d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
      2 * ∫ x, actualAffineCross d T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  rw [actual_affine_global_score_balance,
    ← integral_finsetSum Finset.univ (fun i _ =>
      (ActualBoundedRawSourceCalculus405.BoundedRawTest.ordinary_derivative_memLp
        (affineScoreTest d T i) i).integrable (by norm_num)),
    integral_congr_ae (actual_affine_score_raw_binding d T hT),
    integral_add (actual_direct_moment_integrable d T) ((actual_affine_cross_integrable d T hT).const_mul 2),
    integral_const_mul]

theorem actual_affine_connection_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) =
      (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential) +
      (∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential) +
      ∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential := by
  have hmain := actual_affine_main_cross_identity d T hT
  have hp := actual_affine_global_hessian_balance d T hT
  have hm : (∫ x, actualAffineMetricPair d T x ∂potentialMeasure d.potential) =
      (∫ x, actualAffineSignedConnection d T x ∂potentialMeasure d.potential) +
      2 * ∫ x, actualAffineCross d T x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (actual_affine_metric_raw_binding d T hT),
      integral_add (actual_affine_signed_integrable d T hT) ((actual_affine_cross_integrable d T hT).const_mul 2),
      integral_const_mul]
  have hc : (∫ x, ((actualAffineMatrix d T x * coordinateHessian d.potential x * actualAffineMatrix d T x) *
      sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential) =
      (∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential) +
      ∫ x, actualAffineGamma d T x ∂potentialMeasure d.potential := by
    simp_rw [actual_affine_curvature_split]
    exact integral_add (actual_affine_target_integrable d T) (actual_affine_gamma_integrable d T)
  linarith

theorem actual_affine_target_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ ∫ x, actualAffineTarget d T x ∂potentialMeasure d.potential := by
  apply integral_nonneg_of_ae
  filter_upwards [actual_affine_hessian_positive d T hT, d.hessian_ae_source] with x hA hx
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  exact trace_mul_nonneg_of_posSemidef hA hP

end KLSConstantImprovement.ActualAffineSourceIdentities405

#print axioms KLSConstantImprovement.ActualAffineSourceIdentities405.actual_affine_cross_integrable
#print axioms KLSConstantImprovement.ActualAffineSourceIdentities405.actual_affine_signed_integrable
#print axioms KLSConstantImprovement.ActualAffineSourceIdentities405.actual_affine_main_cross_identity
#print axioms KLSConstantImprovement.ActualAffineSourceIdentities405.actual_affine_connection_identity
#print axioms KLSConstantImprovement.ActualAffineSourceIdentities405.actual_affine_target_nonnegative
