import KLSConstantImprovement.ActualQuadraticGramProduction405
import KLSConstantImprovement.ActualQuadraticCyclicAdjoint405
import KLSConstantImprovement.ActualSourceMeanGram405

/-! The actual whole-row Hessian square completed against the same
literal cubic tensor. The signed cyclic term is kept with its original
orientation. Global production testing is supplied by a separate proof. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualQuadraticProductionCompletion405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405
open ActualQuadraticCyclicAdjoint405 ActualQuadraticHessianDomains405
open ActualQuadraticJacobianEnergy405 ActualQuadraticRowCurvature405
open ActualQuadraticResponseField405 ActualQuadraticHilbertMatrix405
open ActualSourceQuadraticEta405 ActualSourceNaturalHessian405
open ActualSourceMeanGram405 ActualResponseProductionAlgebra405 ActualSourceDirectCubicBalance405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem trace_compatible_gram (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (H * compatibleTraceGram A).trace = ∑ i, ∑ j, H i j * (A i * A j).trace := by
  change (∑ i, ∑ j, H i j * (A j * A i).trace) = _
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [Matrix.trace_mul_comm]

theorem weighted_hessian_completion (H J : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsSymm) (hHJ : H * J = 1)
    (C T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (H * compatibleTraceGram (fun i => J * C i)).trace =
      (H * compatibleTraceGram (fun i => J * C i - T i * H)).trace +
        2 * (∑ i, ∑ j, H i j * (T i * C j).trace) - (H * matrixTraceGram H T).trace := by
  have hleft (i j : Fin n) : ((T i * H) * (J * C j)).trace = (T i * C j).trace := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (T i) H J, hHJ, Matrix.mul_one]
  have hright (i j : Fin n) : ((J * C i) * (T j * H)).trace = (T j * C i).trace := by
    calc
      _ = (H * (J * C i * T j)).trace := by
        simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (J * C i * T j) H
      _ = (C i * T j).trace := by
        simp only [← Matrix.mul_assoc, hHJ, Matrix.one_mul]
      _ = _ := Matrix.trace_mul_comm _ _
  have hc (i j : Fin n) : ((J * C i - T i * H) * (J * C j - T j * H)).trace =
      ((J * C i) * (J * C j)).trace - (T j * C i).trace -
        (T i * C j).trace + (T i * H * T j * H).trace := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, hleft, hright]
    simp only [Matrix.mul_assoc]
    ring
  have hswap : (∑ i, ∑ j, H i j * (T j * C i).trace) =
      ∑ i, ∑ j, H i j * (T i * C j).trace := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hH.apply j i]
  have hgram : (H * matrixTraceGram H T).trace =
      ∑ i, ∑ j, H i j * (T i * H * T j * H).trace := by
    change (∑ i, ∑ j, H i j * matrixTraceGram H T j i) = _
    simp_rw [traceGram_cyclic]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (T j * H) (T i * H)
  rw [trace_compatible_gram, trace_compatible_gram, hgram]
  simp_rw [hc, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hswap]
  ring

def actualQuadraticResidualFactor (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  actualQuadraticHessianFactor d hn hμ T i x - T i * coordinateHessian d.potential x

def actualQuadraticResidualCost (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * compatibleTraceGram
    (fun i => actualQuadraticResidualFactor d hn hμ T i x)).trace

def actualQuadraticJacobianRowCost (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * compatibleTraceGram
    (fun i => quadraticJacobianMatrix d hn hμ (T i) x)).trace

def actualQuadraticTargetRowCost (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Space n) : ℝ :=
  (coordinateHessian d.potential x * (actualQuadraticFluxMatrix d T x *
    ActualSourceCurvatureDomains405.sourceTargetCurvature d x * (actualQuadraticFluxMatrix d T x).transpose)).trace

theorem actual_quadratic_production_completion_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      actualQuadraticProductionXi d hn hμ T x = actualQuadraticTargetRowCost d T x +
        actualQuadraticResidualCost d hn hμ T x + actualQuadraticJacobianRowCost d hn hμ T x +
          2 * actualQuadraticHessianPair d hn hμ T x - actualDirectMoment d T x := by
  filter_upwards [d.hessian_ae_source] with x hx
  have hHJ := Matrix.mul_nonsing_inv (coordinateHessian d.potential x)
    ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  have he := weighted_hessian_completion (coordinateHessian d.potential x)
    (coordinateHessian d.potential x)⁻¹ hx.1.isHermitian.isSymm hHJ
      (fun i => actualQuadraticHessian d hn hμ (T i) x) T
  change (coordinateHessian d.potential x *
    (actualQuadraticFluxMatrix d T x * ActualSourceCurvatureDomains405.sourceTargetCurvature d x *
      (actualQuadraticFluxMatrix d T x).transpose +
      compatibleTraceGram (fun i => (coordinateHessian d.potential x)⁻¹ * actualQuadraticHessian d hn hμ (T i) x) +
      compatibleTraceGram (fun i => quadraticJacobianMatrix d hn hμ (T i) x))).trace = _
  simp only [Matrix.mul_add, Matrix.trace_add]
  rw [he]
  dsimp only [actualQuadraticTargetRowCost, actualQuadraticResidualCost,
    actualQuadraticResidualFactor, actualQuadraticHessianFactor, actualQuadraticJacobianRowCost,
    actualQuadraticHessianPair, actualDirectMoment, actualQuadraticHessian]
  ring

theorem actual_quadratic_residual_nonnegative_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) :
    ∀ᵐ x ∂potentialMeasure d.potential, 0 ≤ actualQuadraticResidualCost d hn hμ T x := by
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr fun i =>
    naturalCanonicalHessian_isSymm_ae d (quadraticSourceDatum d (T i))
      (quadraticFluxJacobian d hn hμ (T i)) (quadraticFluxJacobian_compatible_volume_ae d hn hμ (T i))]
      with x hx hC
  have hHJ := Matrix.mul_nonsing_inv (coordinateHessian d.potential x)
    ((Matrix.isUnit_iff_isUnit_det _).mp hx.1.isUnit)
  apply trace_mul_nonneg_of_posSemidef hx.1.posSemidef
  apply compatibleTraceGram_posSemidef _ hx.1
  intro i
  change (coordinateHessian d.potential x *
    ((coordinateHessian d.potential x)⁻¹ * actualQuadraticHessian d hn hμ (T i) x -
      T i * coordinateHessian d.potential x)).IsSymm
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, hHJ, Matrix.one_mul]
  have hTH : (coordinateHessian d.potential x * T i * coordinateHessian d.potential x).IsSymm := by
    change (coordinateHessian d.potential x * T i * coordinateHessian d.potential x).transpose = _
    simp only [Matrix.transpose_mul, hx.1.isHermitian.isSymm.eq, (hT i).eq, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc, actualQuadraticHessian] using (hC i).sub hTH

end KLSConstantImprovement.ActualQuadraticProductionCompletion405
#print axioms KLSConstantImprovement.ActualQuadraticProductionCompletion405.weighted_hessian_completion
#print axioms KLSConstantImprovement.ActualQuadraticProductionCompletion405.actual_quadratic_production_completion_ae
#print axioms KLSConstantImprovement.ActualQuadraticProductionCompletion405.actual_quadratic_residual_nonnegative_ae
