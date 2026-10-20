import KLSConstantImprovement.ActualResponseHessianPair405
import KLSConstantImprovement.ActualSourceDirectCubicBalance405

/-! Exact same-source H-tested response production. Every integral is
literal and globally integrable. Only the explicit quadratic natural
mass gate remains in the hypotheses. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseGlobalHBalance405
open KLS ActualBoundedCanonicalSource ActualResponseHessianPair405 ActualResponseProductionDomain405
open ActualSourceResponseProduction405 ActualQuadraticResponseField405 ActualQuadraticResponseGram405
open ActualQuadraticRowCurvature405 ActualAffineResponseHilbert405 ActualSourceDirectCubicBalance405
open ActualSourceCurvatureDomains405 ActualSourceTensorGramMetricBinding ActualSourceHessianEvolution405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {n : ℕ} {μ : Measure (Space n)}
section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h23 hC hM in
theorem actual_response_matrix_cost_integrable :
    Integrable (actualResponseMatrixCost d T) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hW := actual_quadratic_response_gram_memLp_top_of_mass_bound d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM
  have hm := memLp_matrix_trace_entries (memLp_matrix_mul_entries (p := ∞) (q := ∞) (r := ∞)
    (fun a b => d.hessian_entry_memLp a b ∞) hW)
  apply (hm.integrable (by simp)).congr
  exact Eventually.of_forall fun x => by
    simp only [actualResponseMatrixCost, quadraticResponseGram, Matrix.mul_assoc]

include h12 h23 hC hM in
theorem actual_response_global_H_balance :
    2 * (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) =
      2 * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) +
        (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) -
          ∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let H := coordinateHessian d.potential
  let W := quadraticResponseGram d T
  let S := sourceConnectionCurvature d
  let B := actualResponseProduction d hn hμ T
  let G := fun x => matrixTraceGram (H x) T
  let A := fun x => (2 : ℝ) • G x - W x - B x
  have hWtop := actual_quadratic_response_gram_memLp_top_of_mass_bound d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM
  have hA1 (i j : Fin n) : MemLp (fun x => A x i j) 1 (potentialMeasure d.potential) := by
    apply (memLp_congr_ae ?_).mp (memLp_one_iff_integrable.mpr
      (actual_response_production_rhs_integrable d hn hμ T h12 h23 hC hM i j))
    exact Eventually.of_forall fun x => by
      change 2 * sourceTensorGramEntry d.potential T i j x - W x i j - B x i j = _
      rw [sourceTensorGramEntry_eq_matrixTraceGram]
      rfl
  have hAH (i j : Fin n) : Integrable (fun x => A x i j * H x j i) (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => A x i j * H x j i) 1 (potentialMeasure d.potential) :=
      (hA1 i j).mul (d.hessian_entry_memLp j i ∞)
    exact hm.integrable le_rfl
  have hWS (i j : Fin n) : Integrable (fun x => W x i j * (H x j i - S x j i)) (potentialMeasure d.potential) := by
    have hb : Integrable (fun x => H x j i - S x j i) (potentialMeasure d.potential) :=
      ((d.hessian_entry_memLp j i ∞).integrable (by simp)).sub (actual_connection_curvature_entry_integrable d j i)
    have hm : MemLp (fun x => W x i j * (H x j i - S x j i)) 1 (potentialMeasure d.potential) :=
      (hWtop i j).mul (memLp_one_iff_integrable.mpr hb)
    exact hm.integrable le_rfl
  have htrace : (∫ x, (A x * H x).trace ∂potentialMeasure d.potential) =
      ∫ x, (W x * (H x - S x)).trace ∂potentialMeasure d.potential := by
    rw [integral_trace_mul A H hAH, integral_trace_mul W (fun x => H x - S x) hWS]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ x, (2 * sourceTensorGramEntry d.potential T i j x - W x i j - B x i j) * H x j i
          ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change _ = (2 * sourceTensorGramEntry d.potential T i j x - W x i j - B x i j) * H x j i
          rw [sourceTensorGramEntry_eq_matrixTraceGram]
          rfl
      _ = ∫ x, (H x j i - S x j i) * W x i j ∂potentialMeasure d.potential :=
        actual_response_hessian_entry_pair d hn hμ T h12 h23 hC hM i j
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hWH (x : Space n) : (W x * H x).trace = actualResponseMatrixCost d T x := by
    have he := Matrix.trace_mul_comm (W x) (H x)
    simpa only [W, H, quadraticResponseGram, actualResponseMatrixCost, Matrix.mul_assoc] using he
  have hleft (x : Space n) : (A x * H x).trace =
      2 * actualDirectMoment d T x - actualResponseMatrixCost d T x - actualResponseXi d hn hμ T x := by
    simp only [A, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    rw [hWH, Matrix.trace_mul_comm (G x) (H x), Matrix.trace_mul_comm (B x) (H x)]
    rfl
  have hright (x : Space n) : (W x * (H x - S x)).trace =
      actualResponseMatrixCost d T x - actualRowCurvature d (quadraticResponseMatrix d T) x := by
    rw [Matrix.mul_sub, Matrix.trace_sub, hWH]
    rfl
  have hMi := actual_response_matrix_cost_integrable d T h23 hC hM
  have hWi := actual_direct_moment_integrable d T
  have hXi := actualResponseXi_integrable d hn hμ T h12 h23 hC hM
  have hθ := actual_response_row_curvature_integrable d T
    (fun i => Matrix.IsSymm.ext fun a b => h23 i b a) hC hM
  have hl : (∫ x, (A x * H x).trace ∂potentialMeasure d.potential) =
      2 * (∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential) -
        (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) -
          ∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hleft)]
    have h2 : Integrable (fun x => 2 * actualDirectMoment d T x) (potentialMeasure d.potential) := hWi.const_mul 2
    have hs : Integrable (fun x => 2 * actualDirectMoment d T x - actualResponseMatrixCost d T x)
        (potentialMeasure d.potential) := h2.sub hMi
    calc
      _ = (∫ x, 2 * actualDirectMoment d T x - actualResponseMatrixCost d T x ∂potentialMeasure d.potential) -
          ∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential := integral_sub hs hXi
      _ = _ := by rw [integral_sub h2 hMi, integral_const_mul]
  have hr : (∫ x, (W x * (H x - S x)).trace ∂potentialMeasure d.potential) =
      (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) -
        ∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hright), integral_sub hMi hθ]
  linarith only [htrace, hl, hr]

end Fixed
end KLSConstantImprovement.ActualResponseGlobalHBalance405

#print axioms KLSConstantImprovement.ActualResponseGlobalHBalance405.actual_response_matrix_cost_integrable
#print axioms KLSConstantImprovement.ActualResponseGlobalHBalance405.actual_response_global_H_balance
