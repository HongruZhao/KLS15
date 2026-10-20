import KLSConstantImprovement.ActualSourceDirectCubicEnergy405
import KLSConstantImprovement.ActualQuarticHessianTest405

/-! Exact global direct cubic balance on the actual C1,1 source. The
literal Gram entry is an already constructed bounded raw weak test of
the Hessian evolution. The signed canonical cross energy is retained. -/
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualSourceDirectCubicBalance405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceTensorGramMetricBinding
open ActualSourceCurvatureDomains405 ActualSourceHessianPolynomialTests405
open ActualQuarticHessianTest405 ActualSourceQuarticBinding405
open ActualSourceDirectCubicEnergy405 ActualDirectCubicPointwise405
variable {n : ℕ} {μ : Measure (Space n)}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def actualDirectMoment (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * matrixTraceGram (coordinateHessian d.potential x) T).trace

def actualDirectFullCurvature (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (matrixTraceGram (coordinateHessian d.potential x) T * sourceConnectionCurvature d x).trace

def actualDirectTargetCurvature (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (matrixTraceGram (coordinateHessian d.potential x) T * sourceTargetCurvature d x).trace

theorem matrixTraceGram_symmetric (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : (matrixTraceGram H T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simpa only [matrixTraceGram, Matrix.mul_assoc] using Matrix.trace_mul_comm (H * T j) (H * T i)

theorem sourceTensorGramEntry_eq_matrixTraceGram (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (x : Space n) :
    sourceTensorGramEntry d.potential T i j x = matrixTraceGram (coordinateHessian d.potential x) T i j := by
  rw [sourceTensorGramEntry_eq_trace]
  change ActualQuarticCongruence405.rawGram (coordinateHessian d.potential x) T i j = _
  rw [rawGram_eq_matrixTraceGram]

theorem actual_direct_moment_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualDirectMoment d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hg : Continuous (fun H : Matrix (Fin n) (Fin n) ℝ => (H * matrixTraceGram H T).trace) := by
    unfold matrixTraceGram
    fun_prop
  obtain ⟨hm, B, hb⟩ := actual_hessian_polynomial_bounded d _ hg
  exact (memLp_top_of_bound hm B (Eventually.of_forall hb)).integrable (by simp)

theorem actual_direct_full_curvature_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualDirectFullCurvature d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  change Integrable (fun x => ∑ i, ∑ j,
    matrixTraceGram (coordinateHessian d.potential x) T i j * sourceConnectionCurvature d x j i)
      (potentialMeasure d.potential)
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hm : MemLp (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j *
      sourceConnectionCurvature d x j i) 1 (potentialMeasure d.potential) :=
    (actual_direct_gram_entry_top d T i j).mul
      (memLp_one_iff_integrable.mpr (actual_connection_curvature_entry_integrable d j i))
  exact hm.integrable le_rfl

theorem actual_direct_full_curvature_split (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    actualDirectFullCurvature d T x = actualDirectTargetCurvature d T x + actualDirectGammaEnergy d T x := by
  simp only [actualDirectFullCurvature, actualDirectTargetCurvature, actualDirectGammaEnergy,
    sourceConnectionCurvature, sourceTargetCurvature, Matrix.mul_add, Matrix.trace_add]

theorem actual_direct_target_curvature_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualDirectTargetCurvature d T) (potentialMeasure d.potential) := by
  apply ((actual_direct_full_curvature_integrable d T).sub (actual_direct_gamma_integrable d T)).congr
  exact Eventually.of_forall fun x => by
    change actualDirectFullCurvature d T x - actualDirectGammaEnergy d T x = _
    rw [actual_direct_full_curvature_split]
    ring

theorem actual_direct_global_hessian_test (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∫ x, ∑ r, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
      rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x
        ∂potentialMeasure d.potential) =
      ∫ x, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        matrixTraceGram (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential := by
  simpa only [tensorGramTest, sourceTensorGramEntry_eq_matrixTraceGram] using
    (tensorGramTest d T i j).global_hessian_test i j

theorem actual_direct_global_balance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) -
      ∫ x, actualDirectFullCurvature d T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hpair (i j : Fin n) : Integrable (fun x => ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x)
      (potentialMeasure d.potential) := integrable_finsetSum Finset.univ fun r _ =>
        (d.hessian_entry_raw_metric_memLp i j r).integrable_mul (d.tensorGram_raw_metric_memLp T i j r)
  have hi (i j : Fin n) : Integrable (fun x =>
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        matrixTraceGram (coordinateHessian d.potential x) T i j) (potentialMeasure d.potential) := by
    have hHC := ((d.hessian_entry_memLp i j 1).integrable le_rfl).sub
      (actual_connection_curvature_entry_integrable d i j)
    have hm : MemLp (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j *
        (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j)) 1
        (potentialMeasure d.potential) :=
      (actual_direct_gram_entry_top d T i j).mul (memLp_one_iff_integrable.mpr hHC)
    exact (hm.integrable le_rfl).congr (Eventually.of_forall fun x => mul_comm _ _)
  have hrow (i : Fin n) : (∫ x, ∑ j, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x
          ∂potentialMeasure d.potential) =
      ∑ j, ∫ x, ∑ r, rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x *
        rawCanonicalMetricDerivative d.potential (sourceTensorGramRawDerivative d.potential d.third T i j) r x
          ∂potentialMeasure d.potential := integral_finsetSum Finset.univ fun j _ => hpair i j
  unfold actualDirectCrossEnergy
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hpair i j))]
  simp_rw [hrow, actual_direct_global_hessian_test]
  have hrowR (i : Fin n) : (∑ j, ∫ x,
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        matrixTraceGram (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        matrixTraceGram (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ fun j _ => hi i j).symm
  simp_rw [hrowR]
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  have he (x : Space n) : (∑ i, ∑ j,
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        matrixTraceGram (coordinateHessian d.potential x) T i j) =
      actualDirectMoment d T x - actualDirectFullCurvature d T x := by
    change (∑ i, ∑ j, (coordinateHessian d.potential x - sourceConnectionCurvature d x) i j *
      matrixTraceGram (coordinateHessian d.potential x) T i j) = _
    rw [matrix_entrywise_contraction_eq_trace _ _ (matrixTraceGram_symmetric _ _),
      Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm (sourceConnectionCurvature d x)]
    rfl
  calc
    _ = ∫ x, actualDirectMoment d T x - actualDirectFullCurvature d T x ∂potentialMeasure d.potential :=
      integral_congr_ae (Eventually.of_forall he)
    _ = _ := integral_sub (actual_direct_moment_integrable d T) (actual_direct_full_curvature_integrable d T)

theorem actual_direct_cubic_primitive_identity (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      (∫ x, actualDirectGammaEnergy d T x ∂potentialMeasure d.potential) +
      ∫ x, actualDirectCrossEnergy d T x ∂potentialMeasure d.potential := by
  have hb := actual_direct_global_balance d T
  have hs : (∫ x, actualDirectFullCurvature d T x ∂potentialMeasure d.potential) =
      (∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential) +
      ∫ x, actualDirectGammaEnergy d T x ∂potentialMeasure d.potential := by
    simp_rw [actual_direct_full_curvature_split]
    exact integral_add (actual_direct_target_curvature_integrable d T) (actual_direct_gamma_integrable d T)
  rw [hs] at hb
  linarith

theorem actual_direct_target_curvature_nonnegative (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    0 ≤ ∫ x, actualDirectTargetCurvature d T x ∂potentialMeasure d.potential := by
  apply integral_nonneg_of_ae
  filter_upwards [d.hessian_ae_source] with x hx
  have hG := matrixTraceGram_posSemidef hx.1.posSemidef T hT
  have hV := coordinateHessian_posSemidef_of_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential (gradient d.potential x)
  have hP : (sourceTargetCurvature d x).PosSemidef := by
    simpa only [sourceTargetCurvature, hx.1.isHermitian.eq] using
      hV.conjTranspose_mul_mul_same (coordinateHessian d.potential x)
  exact trace_mul_nonneg_of_posSemidef hG hP

end KLSConstantImprovement.ActualSourceDirectCubicBalance405

#print axioms KLSConstantImprovement.ActualSourceDirectCubicBalance405.actual_direct_global_hessian_test
#print axioms KLSConstantImprovement.ActualSourceDirectCubicBalance405.actual_direct_global_balance
#print axioms KLSConstantImprovement.ActualSourceDirectCubicBalance405.actual_direct_cubic_primitive_identity
#print axioms KLSConstantImprovement.ActualSourceDirectCubicBalance405.actual_direct_target_curvature_nonnegative
