import KLSConstantImprovement.ActualQuarticHessianTest405

/-! Exact global quartic Hessian balance on the constructed weak source.
The literal cubic-in-H matrix gradient is an already paid weak PDE test.
The curvature contraction is L1 and the quartic moment is bounded. The
finite positive commutator comparison is not assumed by this identity. -/
noncomputable section
open Matrix MeasureTheory Set Filter
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualQuarticGlobalBalance405
open KLS ActualBoundedCanonicalSource ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceCurvatureDomains405
open ActualSourceHessianPolynomialTests405 ActualQuarticPositiveGradient405
open ActualQuarticHessianTest405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem quartic_gradient_euler (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (H * quarticMatrixGradient H T).trace = 2 * matrixFrobeniusSq (matrixTraceGram H T) := by
  simp only [quarticMatrixGradient, sliceMatrixContraction, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul,
    matrixFrobeniusSq, matrixTraceGram, pow_two, Matrix.mul_assoc]

theorem actual_quartic_moment_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T))
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let g : Matrix (Fin n) (Fin n) ℝ → ℝ := fun H => matrixFrobeniusSq (matrixTraceGram H T)
  have hg : Continuous g := by
    dsimp [g, matrixFrobeniusSq, matrixTraceGram]
    fun_prop
  obtain ⟨hm, B, hb⟩ := actual_hessian_polynomial_bounded d g hg
  exact (memLp_top_of_bound hm B (Eventually.of_forall hb)).integrable (by simp)

theorem actual_quartic_global_balance (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    (∑ i, ∑ j, ∫ x, ∑ r,
      rawCanonicalMetricDerivative d.potential (fun k y => d.third y k i j) r x *
        rawCanonicalMetricDerivative d.potential (quarticEntryTest d T i j).derivative r x
          ∂potentialMeasure d.potential) =
      2 * (∫ x, matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T)
        ∂potentialMeasure d.potential) -
      ∫ x, (quarticMatrixGradient (coordinateHessian d.potential x) T *
        sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i j : Fin n) : Integrable (fun x =>
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        quarticMatrixGradient (coordinateHessian d.potential x) T i j)
      (potentialMeasure d.potential) := by
    have hHC := ((d.hessian_entry_memLp i j 1).integrable le_rfl).sub
      (actual_connection_curvature_entry_integrable d i j)
    have hm : MemLp (fun x => quarticMatrixGradient (coordinateHessian d.potential x) T i j *
        (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j)) 1
        (potentialMeasure d.potential) :=
      (actual_quartic_gradient_entry_top d T i j).mul (memLp_one_iff_integrable.mpr hHC)
    exact hm.integrable le_rfl |>.congr (Eventually.of_forall fun x => mul_comm _ _)
  simp_rw [actual_quartic_global_hessian_test]
  have hrow (i : Fin n) : (∑ j, ∫ x,
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        quarticMatrixGradient (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        quarticMatrixGradient (coordinateHessian d.potential x) T i j ∂potentialMeasure d.potential :=
    (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm
  simp_rw [hrow]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  have hinside : (fun x => ∑ i, ∑ j,
      (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
        quarticMatrixGradient (coordinateHessian d.potential x) T i j)
      =ᵐ[potentialMeasure d.potential] fun x =>
        2 * matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T) -
          (quarticMatrixGradient (coordinateHessian d.potential x) T *
            sourceConnectionCurvature d x).trace := by
    filter_upwards [actual_quartic_gradient_positive_ae d T hT] with x hx
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [matrix_entrywise_contraction_eq_trace _ _ hx.isHermitian.isSymm,
      matrix_entrywise_contraction_eq_trace _ _ hx.isHermitian.isSymm,
      quartic_gradient_euler, Matrix.trace_mul_comm (sourceConnectionCurvature d x)]
  calc
    _ = ∫ x, ∑ i, ∑ j,
        (coordinateHessian d.potential x i j - sourceConnectionCurvature d x i j) *
          quarticMatrixGradient (coordinateHessian d.potential x) T i j
            ∂potentialMeasure d.potential := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => rfl
    _ = ∫ x, 2 * matrixFrobeniusSq (matrixTraceGram (coordinateHessian d.potential x) T) -
        (quarticMatrixGradient (coordinateHessian d.potential x) T *
          sourceConnectionCurvature d x).trace ∂potentialMeasure d.potential := integral_congr_ae hinside
    _ = _ := by
      rw [integral_sub ((actual_quartic_moment_integrable d T).const_mul 2)
        (actual_quartic_curvature_pair_integrable d T), integral_const_mul]

end KLSConstantImprovement.ActualQuarticGlobalBalance405
#print axioms KLSConstantImprovement.ActualQuarticGlobalBalance405.quartic_gradient_euler
#print axioms KLSConstantImprovement.ActualQuarticGlobalBalance405.actual_quartic_moment_integrable
#print axioms KLSConstantImprovement.ActualQuarticGlobalBalance405.actual_quartic_global_balance
