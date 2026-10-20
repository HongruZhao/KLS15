import KLSConstantImprovement.ActualQuadraticGramProduction405
import KLSConstantImprovement.ActualResponseProductionDomain405

/-! The actual whole-row Hessian factor has the same global L2 white
coordinates as the actual Poisson Hessian, using the same chosen Du. -/
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticHessianFactorDomain405
open KLS ActualBoundedCanonicalSource ActualQuadraticGramProduction405 ActualQuadraticJacobianEnergy405
open ActualResponseProductionDomain405 ActualWhitenedWeakMatrixDomain405 ActualSourceNaturalWhitenedHessian405
open ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false

theorem unroot_mul_inverseHessian_at {φ : Space n → ℝ} {x : Space n}
    (hp : (coordinateHessian φ x).PosDef) :
    canonicalMetricUnroot φ x * (coordinateHessian φ x)⁻¹ = canonicalMetricRoot φ x := by
  have hR : (canonicalMetricRoot φ x).IsSymm := inverseSqrtMatrix_isSymm _
  have hRR := canonicalMetricRoot_gram_at hp
  rw [hR.eq] at hRR
  rw [← hRR, ← Matrix.mul_assoc, canonicalMetricUnroot_mul_root_at hp, Matrix.one_mul]

theorem actualQuadraticHessianFactor_white_memLp (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i a b : Fin n) :
    MemLp (fun x => sourceWhitenedJacobian d (actualQuadraticHessianFactor d hn hμ T i) x a b)
      2 (potentialMeasure d.potential) := by
  apply (memLp_congr_ae ?_).mp (quadraticCanonicalHessian_white_memLp_of_mass_bound d hn hμ (T i) hC (hM i) a b)
  filter_upwards [d.hessian_ae_source] with x hx
  let K := ActualSourceNaturalHessian405.naturalCanonicalHessian d (quadraticSourceDatum d (T i))
    (ActualQuadraticResponseField405.quadraticFluxJacobian d hn hμ (T i)) x
  change (canonicalMetricRoot d.potential x * K * canonicalMetricRoot d.potential x) a b =
    (canonicalMetricUnroot d.potential x * ((coordinateHessian d.potential x)⁻¹ * K) * canonicalMetricRoot d.potential x) a b
  rw [← Matrix.mul_assoc (canonicalMetricUnroot d.potential x), unroot_mul_inverseHessian_at hx.1]

theorem actual_quadratic_hessian_gram_entry_integrable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ i, ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d (T i))) x ≤ C)
    (i j : Fin n) :
    Integrable (fun x => (actualQuadraticHessianFactor d hn hμ T i x *
      actualQuadraticHessianFactor d hn hμ T j x).trace) (potentialMeasure d.potential) :=
  compatibleTraceGram_entry_integrable_of_white d (actualQuadraticHessianFactor d hn hμ T)
    (actualQuadraticHessianFactor_white_memLp d hn hμ T hC hM) i j

theorem actual_quadratic_jacobian_gram_entry_integrable (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (fun x => (quadraticJacobianMatrix d hn hμ (T i) x *
      quadraticJacobianMatrix d hn hμ (T j) x).trace) (potentialMeasure d.potential) :=
  compatibleTraceGram_entry_integrable_of_white d (fun i => quadraticJacobianMatrix d hn hμ (T i))
    (fun i => quadraticFluxJacobian_white_memLp d hn hμ (T i)) i j

end KLSConstantImprovement.ActualQuadraticHessianFactorDomain405

#print axioms KLSConstantImprovement.ActualQuadraticHessianFactorDomain405.actualQuadraticHessianFactor_white_memLp
#print axioms KLSConstantImprovement.ActualQuadraticHessianFactorDomain405.actual_quadratic_hessian_gram_entry_integrable
