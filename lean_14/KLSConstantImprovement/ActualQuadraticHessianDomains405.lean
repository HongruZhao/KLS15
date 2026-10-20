import KLSConstantImprovement.ActualQuadraticJacobianEnergy405

/-! Ordinary L2 Hessian coordinates and genuine weak derivatives for
the same chosen quadratic inverse used in the response production. -/
noncomputable section
open MeasureTheory Matrix
namespace KLSConstantImprovement.ActualQuadraticHessianDomains405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceLocalizedGaffney405
open ActualSourceQuadraticEta405 ActualQuadraticResponseField405 ActualQuadraticJacobianEnergy405
open ActualSourceNaturalHessian405 ActualSourceNaturalWhitenedHessian405 ActualSourceNaturalTargetCurvatureDomain405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false

def actualQuadraticHessian (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  naturalCanonicalHessian d (quadraticSourceDatum d B) (quadraticFluxJacobian d hn hμ B) x

theorem actualQuadraticHessian_memLp (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C) (i j : Fin n) :
    MemLp (fun x => actualQuadraticHessian d hn hμ B x i j) 2 (potentialMeasure d.potential) := by
  exact naturalCanonicalHessian_entry_memLp d (quadraticSourceDatum d B) (quadraticFluxJacobian d hn hμ B)
    (naturalCanonicalHessian_local_L2 d _ hC hM _
      (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE))
    (naturalCanonicalHessian_isSymm_ae d _ _ (quadraticFluxJacobian_compatible_volume_ae d hn hμ B))
    (quadraticCanonicalHessianEnergy_integrable_of_mass_bound d hn hμ B hC hM) i j

theorem actualQuadraticHessian_weak (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C) (i j : Fin n) :
    HasLocalWeakCoordinateDerivative (naturalCanonicalRawGradient d (quadraticSourceDatum d B) i)
      (fun x => actualQuadraticHessian d hn hμ B x i j) j :=
  naturalCanonicalRawGradient_hasLocalWeakDerivative d _ hC hM _
    (fun a _ hE => quadratic_row_flux_local_L2 d hn hμ B a hE)
    (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE)
    (quadratic_flux_jacobian_weak d hn hμ B) i j

end KLSConstantImprovement.ActualQuadraticHessianDomains405
#print axioms KLSConstantImprovement.ActualQuadraticHessianDomains405.actualQuadraticHessian_memLp
#print axioms KLSConstantImprovement.ActualQuadraticHessianDomains405.actualQuadraticHessian_weak
