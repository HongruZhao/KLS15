import KLSConstantImprovement.ActualQuadraticGramGlobalForm405
import KLSConstantImprovement.ActualQuadraticForcingTrace405
import KLSConstantImprovement.ActualResponseHessianPair405

/-! Exact global whole-row H-production balance on the actual law.
Every boundary passage is already paid by the genuine bounded weak
form construction; the forcing is the literal quadratic-affine cross. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticGlobalHBalance405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticGramGlobalForm405
open ActualQuadraticProductionDomain405 ActualQuadraticForcingTrace405 ActualResponseHessianPair405
open ActualQuadraticHilbertMatrix405 ActualQuadraticRowCurvature405 ActualQuadraticCyclicAdjoint405
open ActualSourceCurvatureDomains405 ActualSourceHessianEvolution405
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_quadratic_global_H_balance (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C) :
    2 * (∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential) =
      2 * (∫ x, actualQuadraticAffineCrossCost d T x ∂potentialMeasure d.potential) +
        (∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential) -
          ∫ x, actualQuadraticProductionXi d hn hμ T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let H := coordinateHessian d.potential
  let W := actualQuadraticGram d T
  let S := sourceConnectionCurvature d
  let B := actualQuadraticProduction d hn hμ T
  let Q := actualQuadraticForcingMatrix d T
  let A := fun x => Q x - W x - B x
  have hWtop := actualQuadraticGram_top_of_mass_bound d T hM
  have hA1 (i j : Fin n) : MemLp (fun x => A x i j) 1 (potentialMeasure d.potential) :=
    memLp_one_iff_integrable.mpr (actualQuadraticProductionRHS_integrable d hn hμ T hC hM i j)
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
      _ = ∫ x, (H x j i - S x j i) * W x i j ∂potentialMeasure d.potential :=
        actual_quadratic_hessian_entry_pair d hn hμ T hC hM i j
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hWH (x : Space n) : (W x * H x).trace = actualQuadraticMatrixCost d T x := by
    have he := Matrix.trace_mul_comm (W x) (H x)
    simpa only [W, H, actualQuadraticGram, actualQuadraticMatrixCost, Matrix.mul_assoc] using he
  have hleft (x : Space n) : (A x * H x).trace = actualQuadraticForcingTrace d T x -
      actualQuadraticMatrixCost d T x - actualQuadraticProductionXi d hn hμ T x := by
    simp only [A, Matrix.sub_mul, Matrix.trace_sub]
    rw [hWH, Matrix.trace_mul_comm (Q x) (H x), Matrix.trace_mul_comm (B x) (H x)]
    rfl
  have hright (x : Space n) : (W x * (H x - S x)).trace = actualQuadraticMatrixCost d T x -
      actualRowCurvature d (actualQuadraticFluxMatrix d T) x := by
    rw [Matrix.mul_sub, Matrix.trace_sub, hWH]
    rfl
  have hMi := actual_quadratic_matrix_cost_integrable d T
  have hXi := actualQuadraticProductionXi_integrable d hn hμ T hC hM
  have hθ := actual_quadratic_row_curvature_integrable d T hM
  have hQh (i j : Fin n) : MemLp (fun x => H x i j * Q x j i) 1 (potentialMeasure d.potential) :=
    (d.hessian_entry_memLp i j ∞).mul (memLp_one_iff_integrable.mpr (actual_quadratic_raw_forcing_integrable d T j i))
  have hQi : Integrable (actualQuadraticForcingTrace d T) (potentialMeasure d.potential) :=
    integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ => (hQh i j).integrable le_rfl
  have hl : (∫ x, (A x * H x).trace ∂potentialMeasure d.potential) =
      (∫ x, actualQuadraticForcingTrace d T x ∂potentialMeasure d.potential) -
        (∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential) -
          ∫ x, actualQuadraticProductionXi d hn hμ T x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hleft)]
    have hs : Integrable (fun x => actualQuadraticForcingTrace d T x - actualQuadraticMatrixCost d T x)
        (potentialMeasure d.potential) := hQi.sub hMi
    calc
      _ = (∫ x, actualQuadraticForcingTrace d T x - actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential) -
          ∫ x, actualQuadraticProductionXi d hn hμ T x ∂potentialMeasure d.potential := integral_sub hs hXi
      _ = _ := by rw [integral_sub hQi hMi]
  have hr : (∫ x, (W x * (H x - S x)).trace ∂potentialMeasure d.potential) =
      (∫ x, actualQuadraticMatrixCost d T x ∂potentialMeasure d.potential) -
        ∫ x, actualRowCurvature d (actualQuadraticFluxMatrix d T) x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hright), integral_sub hMi hθ]
  have hforce : (∫ x, actualQuadraticForcingTrace d T x ∂potentialMeasure d.potential) =
      2 * ∫ x, actualQuadraticAffineCrossCost d T x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (actual_quadratic_forcing_trace_ae d T h12 h23), integral_const_mul]
  linarith only [htrace, hl, hr, hforce]

end KLSConstantImprovement.ActualQuadraticGlobalHBalance405

#print axioms KLSConstantImprovement.ActualQuadraticGlobalHBalance405.actual_quadratic_global_H_balance
