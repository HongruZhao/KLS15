import KLSConstantImprovement.ActualWhitenedWeakMatrixDomain405
import KLSConstantImprovement.ActualQuadraticResponseField405

/-! Global domains for the same chosen quadratic-row Jacobian used in
F and its production. The Gaffney and bounded-mass Bochner proofs are
instantiated internally; no alternative existential choice is substituted. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ENNReal
namespace KLSConstantImprovement.ActualQuadraticJacobianEnergy405
open KLS ActualBoundedCanonicalSource ActualSourceQuadraticEta405 ActualSourceNaturalGaffney405
open ActualQuadraticResponseField405 ActualSourceLocalizedGaffney405 ActualSourceNaturalHessian405
open ActualSourceBoundedMassBochner405 ActualSourceNaturalWhitenedHessian405
open ActualWhitenedWeakMatrixDomain405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def quadraticJacobianMatrix (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => quadraticFluxJacobian d hn hμ B a b x

theorem quadraticFluxJacobian_compatible_volume_ae (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    ∀ᵐ x ∂(volume : Measure (Space n)), (coordinateHessian d.potential x * quadraticJacobianMatrix d hn hμ B x).IsSymm :=
  (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))).2.2.2.1

theorem quadraticFluxJacobian_energy_integrable (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (sourceVectorJacobianEnergy (quadraticFluxJacobian d hn hμ B)) (potentialMeasure d.potential) :=
  (Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))).2.2.2.2.2.1

theorem quadraticFluxJacobian_white_memLp (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    MemLp (fun x => sourceWhitenedJacobian d (quadraticJacobianMatrix d hn hμ B) x i j)
      2 (potentialMeasure d.potential) := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) := withDensity_absolutelyContinuous _ _
  have hQi : Integrable (fun x => (quadraticJacobianMatrix d hn hμ B x *
      quadraticJacobianMatrix d hn hμ B x).trace) (potentialMeasure d.potential) :=
    quadraticFluxJacobian_energy_integrable d hn hμ B
  exact sourceWhitenedJacobian_entry_memLp d (quadraticJacobianMatrix d hn hμ B)
    (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE)
    ((quadraticFluxJacobian_compatible_volume_ae d hn hμ B).filter_mono hac.ae_le) hQi i j

theorem quadraticCanonicalHessianEnergy_integrable_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C) :
    Integrable (naturalCanonicalHessianEnergy d (quadraticSourceDatum d B) (quadraticFluxJacobian d hn hμ B))
      (potentialMeasure d.potential) := by
  have hs := Classical.choose_spec (exists_naturalCanonicalFlux_gaffney d hn (quadraticSourceDatum d B)
    (quadraticSourceDatum_mean_zero d hμ B))
  exact (actual_natural_bochner_identity_of_mass_bound d (quadraticSourceDatum d B) hC hM
    (quadraticFluxJacobian d hn hμ B) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1
    hs.2.2.2.2.1 hs.2.2.2.2.2.1).1

theorem quadraticCanonicalHessian_white_memLp_of_mass_bound (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C)
    (i j : Fin n) :
    MemLp (fun x => naturalWhitenedHessian d (quadraticSourceDatum d B) (quadraticFluxJacobian d hn hμ B) x i j)
      2 (potentialMeasure d.potential) :=
  naturalWhitenedHessian_entry_memLp d (quadraticSourceDatum d B) (quadraticFluxJacobian d hn hμ B)
    (naturalCanonicalHessian_local_L2 d (quadraticSourceDatum d B) hC hM (quadraticFluxJacobian d hn hμ B)
      (fun a b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE))
    (naturalCanonicalHessian_isSymm_ae d _ _ (quadraticFluxJacobian_compatible_volume_ae d hn hμ B))
    (quadraticCanonicalHessianEnergy_integrable_of_mass_bound d hn hμ B hC hM) i j

end KLSConstantImprovement.ActualQuadraticJacobianEnergy405

#print axioms KLSConstantImprovement.ActualQuadraticJacobianEnergy405.quadraticFluxJacobian_white_memLp
#print axioms KLSConstantImprovement.ActualQuadraticJacobianEnergy405.quadraticCanonicalHessianEnergy_integrable_of_mass_bound
#print axioms KLSConstantImprovement.ActualQuadraticJacobianEnergy405.quadraticCanonicalHessian_white_memLp_of_mass_bound
