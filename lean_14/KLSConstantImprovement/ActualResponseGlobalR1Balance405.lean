import KLSConstantImprovement.ActualResponseResolventPair405
import KLSConstantImprovement.ActualResponseGlobalHBalance405
import KLSConstantImprovement.ActualSourceHessianResolventLower405

/-! Exact same-law unit-resolvent response production and its
nonnegative extra. All H/K/production pairings are globally L1;
K>=H/2 is the actual conservative L1-forcing comparison. -/
noncomputable section
open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualResponseGlobalR1Balance405
open KLS ActualBoundedCanonicalSource ActualResponseResolventPair405 ActualResponseGlobalHBalance405
open ActualResponseHessianPair405 ActualResponseProductionDomain405 ActualSourceResponseProduction405
open ActualSourceMatrixResolvent405 ActualSourceHessianResolventLower405
open ActualQuadraticResponseField405 ActualQuadraticResponseGram405 ActualQuadraticRowCurvature405
open ActualSourceDirectCubicBalance405 ActualSourceMeanGram405 ActualSourceTensorGramMetricBinding
open ActualAffineResponseHilbert405 ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {n : ℕ} {μ : Measure (Space n)}

def actualHessianResolventMatrix (d : SourceData μ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  matrixFieldValue d (sourceMatrixResolvent d (sourceHessianLp d)) x

def actualResponseShiftedMoment (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (actualHessianResolventMatrix d x * matrixTraceGram (coordinateHessian d.potential x) T).trace

def actualResponseShiftedProduction (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (actualHessianResolventMatrix d x * actualResponseProduction d hn hμ T x).trace

def actualResponseExtra (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (((2 : ℝ) • actualHessianResolventMatrix d x - coordinateHessian d.potential x) *
    actualResponseProduction d hn hμ T x).trace

theorem actualHessianResolventMatrix_entry_top (d : SourceData μ) (i j : Fin n) :
    MemLp (fun x => actualHessianResolventMatrix d x i j) ∞ (potentialMeasure d.potential) :=
  memLp_top_of_bound (Lp.memLp _).aestronglyMeasurable _ (actualHessianResolvent_entry_bound d i j)

theorem bounded_left_trace_integrable (d : SourceData μ)
    (A B : Space n → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, MemLp (fun x => A x i j) ∞ (potentialMeasure d.potential))
    (hB : ∀ i j, Integrable (fun x => B x i j) (potentialMeasure d.potential)) :
    Integrable (fun x => (A x * B x).trace) (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hm (i j : Fin n) : MemLp (fun x => (A x * B x) i j) 1 (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries (p := ∞) (q := 1) (r := 1) hA
      (fun a b => memLp_one_iff_integrable.mpr (hB a b)) i j
  exact (memLp_matrix_trace_entries hm).integrable le_rfl

theorem actualResponseShiftedMoment_integrable (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Integrable (actualResponseShiftedMoment d T) (potentialMeasure d.potential) :=
  bounded_left_trace_integrable d _ _ (actualHessianResolventMatrix_entry_top d) (actual_traceGram_integrable d T)

section Fixed
variable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)

include h12 h23 hC hM in
theorem actualResponseShiftedProduction_integrable :
    Integrable (actualResponseShiftedProduction d hn hμ T) (potentialMeasure d.potential) :=
  bounded_left_trace_integrable d _ _ (actualHessianResolventMatrix_entry_top d)
    (actualResponseProduction_entry_integrable d hn hμ T h12 h23 hC hM)

include h12 h23 hC hM in
theorem actualResponseExtra_integrable : Integrable (actualResponseExtra d hn hμ T) (potentialMeasure d.potential) := by
  have he (i j : Fin n) : MemLp (fun x => ((2 : ℝ) • actualHessianResolventMatrix d x -
      coordinateHessian d.potential x) i j) ∞ (potentialMeasure d.potential) :=
    ((actualHessianResolventMatrix_entry_top d i j).const_mul 2).sub (d.hessian_entry_memLp i j ∞)
  exact bounded_left_trace_integrable d _ _ he (actualResponseProduction_entry_integrable d hn hμ T h12 h23 hC hM)

include h12 h23 in
theorem actualResponseExtra_nonnegative_ae :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualResponseExtra d hn hμ T x := by
  filter_upwards [actualHessianResolvent_twice_sub_H_posSemidef d,
    actualResponseProduction_posSemidef_ae d hn hμ T h12 h23] with x hk hb
  exact trace_mul_nonneg_of_posSemidef hk hb

include h12 h23 hC hM in
theorem actual_response_global_R1_balance :
    (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) =
      2 * (∫ x, actualResponseShiftedMoment d T x ∂potentialMeasure d.potential) -
        ∫ x, actualResponseShiftedProduction d hn hμ T x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let H := coordinateHessian d.potential
  let K := actualHessianResolventMatrix d
  let W := quadraticResponseGram d T
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
  have hAK (i j : Fin n) : Integrable (fun x => A x i j * K x j i) (potentialMeasure d.potential) := by
    have hm : MemLp (fun x => A x i j * K x j i) 1 (potentialMeasure d.potential) :=
      (hA1 i j).mul (actualHessianResolventMatrix_entry_top d j i)
    exact hm.integrable le_rfl
  have hWK (i j : Fin n) : Integrable (fun x => W x i j * (H x j i - K x j i)) (potentialMeasure d.potential) := by
    have hd : MemLp (fun x => H x j i - K x j i) ∞ (potentialMeasure d.potential) :=
      (d.hessian_entry_memLp j i ∞).sub (actualHessianResolventMatrix_entry_top d j i)
    have hm : MemLp (fun x => W x i j * (H x j i - K x j i)) ∞ (potentialMeasure d.potential) := (hWtop i j).mul hd
    exact hm.integrable (by simp)
  have htrace : (∫ x, (A x * K x).trace ∂potentialMeasure d.potential) =
      ∫ x, (W x * (H x - K x)).trace ∂potentialMeasure d.potential := by
    rw [integral_trace_mul A K hAK, integral_trace_mul W (fun x => H x - K x) hWK]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ x, (2 * sourceTensorGramEntry d.potential T i j x - W x i j - B x i j) * K x j i
          ∂potentialMeasure d.potential := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change A x i j * K x j i =
            (2 * sourceTensorGramEntry d.potential T i j x - W x i j - B x i j) * K x j i
          rw [sourceTensorGramEntry_eq_matrixTraceGram]
          rfl
      _ = ∫ x, (H x j i - K x j i) * W x i j ∂potentialMeasure d.potential :=
        actual_response_resolvent_entry_pair d hn hμ T h12 h23 hC hM i j
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hMi := actual_response_matrix_cost_integrable d T h23 hC hM
  have hGi := actualResponseShiftedMoment_integrable d T
  have hBi := actualResponseShiftedProduction_integrable d hn hμ T h12 h23 hC hM
  have hWKi : Integrable (fun x => (W x * K x).trace) (potentialMeasure d.potential) :=
    (bounded_left_trace_integrable d K W (actualHessianResolventMatrix_entry_top d)
      (fun i j => (hWtop i j).integrable (by simp))).congr
        (Eventually.of_forall fun x => Matrix.trace_mul_comm _ _)
  have hleft (x : Space n) : (A x * K x).trace = 2 * actualResponseShiftedMoment d T x -
      (W x * K x).trace - actualResponseShiftedProduction d hn hμ T x := by
    simp only [A, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    rw [Matrix.trace_mul_comm (G x) (K x), Matrix.trace_mul_comm (B x) (K x)]
    rfl
  have hright (x : Space n) : (W x * (H x - K x)).trace = actualResponseMatrixCost d T x - (W x * K x).trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_mul_comm (W x) (H x)]
    simp only [W, H, quadraticResponseGram, actualResponseMatrixCost, Matrix.mul_assoc]
  have hl : (∫ x, (A x * K x).trace ∂potentialMeasure d.potential) =
      2 * (∫ x, actualResponseShiftedMoment d T x ∂potentialMeasure d.potential) -
        (∫ x, (W x * K x).trace ∂potentialMeasure d.potential) -
          ∫ x, actualResponseShiftedProduction d hn hμ T x ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hleft)]
    have h2 : Integrable (fun x => 2 * actualResponseShiftedMoment d T x) (potentialMeasure d.potential) := hGi.const_mul 2
    have hs : Integrable (fun x => 2 * actualResponseShiftedMoment d T x - (W x * K x).trace)
        (potentialMeasure d.potential) := h2.sub hWKi
    calc
      _ = (∫ x, 2 * actualResponseShiftedMoment d T x - (W x * K x).trace ∂potentialMeasure d.potential) -
          ∫ x, actualResponseShiftedProduction d hn hμ T x ∂potentialMeasure d.potential := integral_sub hs hBi
      _ = _ := by rw [integral_sub h2 hWKi, integral_const_mul]
  have hr : (∫ x, (W x * (H x - K x)).trace ∂potentialMeasure d.potential) =
      (∫ x, actualResponseMatrixCost d T x ∂potentialMeasure d.potential) -
        ∫ x, (W x * K x).trace ∂potentialMeasure d.potential := by
    rw [integral_congr_ae (Eventually.of_forall hright), integral_sub hMi hWKi]
  linarith only [htrace, hl, hr]

include h12 h23 hC hM in
theorem actual_response_curvature_extra_identity :
    (∫ x, actualRowCurvature d (quadraticResponseMatrix d T) x ∂potentialMeasure d.potential) +
      (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) =
        4 * (∫ x, actualResponseShiftedMoment d T x ∂potentialMeasure d.potential) -
          2 * ∫ x, actualDirectMoment d T x ∂potentialMeasure d.potential := by
  have hh := actual_response_global_H_balance d hn hμ T h12 h23 hC hM
  have hk := actual_response_global_R1_balance d hn hμ T h12 h23 hC hM
  have he : (∫ x, actualResponseExtra d hn hμ T x ∂potentialMeasure d.potential) =
      2 * (∫ x, actualResponseShiftedProduction d hn hμ T x ∂potentialMeasure d.potential) -
        ∫ x, actualResponseXi d hn hμ T x ∂potentialMeasure d.potential := by
    have hpoint (x : Space n) : actualResponseExtra d hn hμ T x =
        2 * actualResponseShiftedProduction d hn hμ T x - actualResponseXi d hn hμ T x := by
      simp only [actualResponseExtra, actualResponseShiftedProduction, actualResponseXi,
        Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    rw [integral_congr_ae (Eventually.of_forall hpoint),
      integral_sub ((actualResponseShiftedProduction_integrable d hn hμ T h12 h23 hC hM).const_mul 2)
        (actualResponseXi_integrable d hn hμ T h12 h23 hC hM), integral_const_mul]
  linarith only [hh, hk, he]

end Fixed
end KLSConstantImprovement.ActualResponseGlobalR1Balance405

#print axioms KLSConstantImprovement.ActualResponseGlobalR1Balance405.actualResponseExtra_nonnegative_ae
#print axioms KLSConstantImprovement.ActualResponseGlobalR1Balance405.actual_response_global_R1_balance
#print axioms KLSConstantImprovement.ActualResponseGlobalR1Balance405.actual_response_curvature_extra_identity
