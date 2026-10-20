import KLSConstantImprovement.ActualKatoNonlinearDomains405

/-! Exact expansion of the same common joint multiplier in the actual
Bochner identity. The joint derivative error is the metric regularized
mass flux times the derivative of the common compact bump. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualKatoJointExpansion405
open KLS ActualBoundedCanonicalSource ActualKatoNonlinearDomains405 ActualKatoLocalDomains405
open ActualSmoothKatoRegularizer405 ActualNaturalMassWeakDerivative405 ActualSourceNaturalGaffney405
open ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem finite_joint_Kato_expansion (ψ b f s L : ℝ) (z r v h : Fin n → ℝ) :
    ψ * (b * (2 * f)) * L +
      (∑ a : Fin n, (r a / 2) * ((b * (2 * f)) * v a +
        ψ * (b * (2 * s) * z a + (2 * f) * h a))) =
      b * (ψ * (2 * f * L + s * (∑ a : Fin n, z a * r a)) +
        (∑ a : Fin n, (f * r a) * v a)) +
          ψ * (∑ a : Fin n, (f * r a) * h a) := by
  have hp (a : Fin n) :
      (r a / 2) * ((b * (2 * f)) * v a + ψ * (b * (2 * s) * z a + (2 * f) * h a)) =
        b * ((f * r a) * v a) + (b * ψ * s) * (z a * r a) + ψ * ((f * r a) * h a) := by ring
  simp_rw [hp, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

theorem naturalKatoMetricFlux_eq (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (ε : ℝ) (a : Fin n) (x : Space n) :
    naturalKatoMetricFlux d g Du ε a x =
      katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) *
        ((coordinateHessian d.potential x)⁻¹ *ᵥ (fun b => naturalMassRawDerivative d g Du b x)) a := by
  unfold naturalKatoMetricFlux
  change ((coordinateHessian d.potential x)⁻¹ *ᵥ
    (katoFirst ε (sourceVectorMass d.potential (naturalCanonicalFlux d g) x) •
      (fun b => naturalMassRawDerivative d g Du b x))) a = _
  rw [Matrix.mulVec_smul]
  rfl

end KLSConstantImprovement.ActualKatoJointExpansion405
#print axioms KLSConstantImprovement.ActualKatoJointExpansion405.finite_joint_Kato_expansion
#print axioms KLSConstantImprovement.ActualKatoJointExpansion405.naturalKatoMetricFlux_eq
