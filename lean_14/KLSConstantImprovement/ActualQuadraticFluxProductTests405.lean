import KLSConstantImprovement.ActualQuadraticRowWeakTests405
import KLSConstantImprovement.ActualLocalCompactWeakTests405
import KLSConstantImprovement.ActualSourceRawHessianEvolution405

/-! The actual compact tests needed for row production: theta*u_j and
theta*u_i*u_j. The only extra analytic hypothesis is the displayed
natural quadratic mass bound. Literal derivatives use the same actual
Gaffney Jacobians; no row PDE or global metric test domain is supplied. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualQuadraticFluxProductTests405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405 ActualSourceQuadraticEta405
open ActualSourceLocalizedGaffney405 ActualSourceBoundedMassCutoffs405
open ActualQuadraticResponseField405 ActualQuadraticRowWeakTests405
open ActualLocalBoundedWeakAlgebra405 ActualLocalCompactWeakTests405
open ActualSourceHessianEvolution405 ActualSourceRawHessianEvolution405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ} {μ : Measure (Space n)}

def quadraticFluxLocalTest (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C)
    (a : Fin n) : LocalRawTest n where
  value := naturalCanonicalFlux d (quadraticSourceDatum d B) a
  derivative := quadraticFluxJacobian d hn hμ B a
  value_local_top := fun _ hE => naturalCanonicalFlux_local_top_of_mass_bound d _ hC hM a hE
  derivative_local := fun b _ hE => quadratic_flux_jacobian_local_L2 d hn hμ B a b hE
  weak_derivative := quadratic_flux_jacobian_weak d hn hμ B a

theorem actual_quadratic_row_times_flux_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B Q : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d Q)) x ≤ C)
    (a b : Fin n) {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∀ r, Integrable (fun x => quadraticFluxJacobian d hn hμ B r a x *
      (coordinateDerivative θ r x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x +
        θ x * quadraticFluxJacobian d hn hμ Q b r x)) (potentialMeasure d.potential)) ∧
      Integrable (fun x => quadraticRowDrift d B a x *
        (θ x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x)) (potentialMeasure d.potential) ∧
      (∑ r : Fin n, ∫ x, quadraticFluxJacobian d hn hμ B r a x *
        (coordinateDerivative θ r x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x +
          θ x * quadraticFluxJacobian d hn hμ Q b r x) ∂potentialMeasure d.potential) =
        ∫ x, quadraticRowDrift d B a x * (θ x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x)
          ∂potentialMeasure d.potential := by
  let f := cutoffLocalRawTest hθ (quadraticFluxLocalTest d hn hμ Q hC hM b)
  have hfc : HasCompactSupport f.value := hc.mul_right
  obtain ⟨D, hD⟩ := compact_localRawTest_bound f hfc
  exact actual_quadratic_row_compact_rawH1_test d hn hμ B a f.value_local hfc hD
    f.derivative_local f.weak_derivative

def quadraticFluxProductDerivative (d : SourceData μ) (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (B Q : Matrix (Fin n) (Fin n) ℝ) (θ : Space n → ℝ) (a b r : Fin n) (x : Space n) : ℝ :=
  coordinateDerivative θ r x *
    (naturalCanonicalFlux d (quadraticSourceDatum d B) a x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x) +
  θ x * (quadraticFluxJacobian d hn hμ B a r x * naturalCanonicalFlux d (quadraticSourceDatum d Q) b x +
    naturalCanonicalFlux d (quadraticSourceDatum d B) a x * quadraticFluxJacobian d hn hμ Q b r x)

theorem actual_hessian_times_quadratic_flux_product_test (d : SourceData μ) (hn : 1 ≤ n)
    (hμ : admissibleMeasure μ) (B Q : Matrix (Fin n) (Fin n) ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hMB : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d B)) x ≤ C)
    (hMQ : ∀ᵐ x ∂potentialMeasure d.potential,
      sourceVectorMass d.potential (naturalCanonicalFlux d (quadraticSourceDatum d Q)) x ≤ D)
    (a b i j : Fin n) {θ : Space n → ℝ} (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∀ r, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) r j *
      quadraticFluxProductDerivative d hn hμ B Q θ a b r x) (potentialMeasure d.potential)) ∧
      Integrable (fun x => (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        (θ x * (naturalCanonicalFlux d (quadraticSourceDatum d B) a x *
          naturalCanonicalFlux d (quadraticSourceDatum d Q) b x))) (potentialMeasure d.potential) ∧
      -(∑ r : Fin n, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) r j *
        quadraticFluxProductDerivative d hn hμ B Q θ a b r x ∂potentialMeasure d.potential) =
        ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
          (θ x * (naturalCanonicalFlux d (quadraticSourceDatum d B) a x *
            naturalCanonicalFlux d (quadraticSourceDatum d Q) b x)) ∂potentialMeasure d.potential := by
  let v := (quadraticFluxLocalTest d hn hμ B hC hMB a).mul
    (quadraticFluxLocalTest d hn hμ Q hD hMQ b)
  let f := cutoffLocalRawTest hθ v
  have hfc : HasCompactSupport f.value := hc.mul_right
  obtain ⟨E, hE⟩ := compact_localRawTest_bound f hfc
  exact actual_compact_raw_hessian_evolution d f.value_local hfc hE
    f.derivative_local f.weak_derivative i j

end KLSConstantImprovement.ActualQuadraticFluxProductTests405

#print axioms KLSConstantImprovement.ActualQuadraticFluxProductTests405.actual_quadratic_row_times_flux_test
#print axioms KLSConstantImprovement.ActualQuadraticFluxProductTests405.actual_hessian_times_quadratic_flux_product_test
