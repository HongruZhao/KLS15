import KLSConstantImprovement.ActualDualMultiplierLift405
import KLSConstantImprovement.ActualJointWeakBochner405

/-! The actual common-joint weak Bochner identity in (u,p), with the same
natural flux and genuine weak Hessian throughout. The compact lift is
identically one in the actual H range; weak uniqueness transfers literal
values and derivatives. No nonlinear truncation limit is claimed here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualDualWeakBochner405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualNaturalDualJoint405 ActualDualMultiplierLift405 ActualJointWeakBochner405
open ActualJointMultiplierWeakTests405 ActualJointBochnerContractions405
open ActualSourceNaturalHessian405 ActualSourceConnectionFields405 ActualSourceLocalizedGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def dualEffectiveDerivative (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (η : (DualIndex n → ℝ) → ℝ)
    (ψ : Space n → ℝ) (a : Fin n) (x : Space n) : ℝ :=
  dualSource d g η x * coordinateDerivative ψ a x + ψ x * dualSourceDerivative d g Du η a x

def dualBochnerIntegrand (d : SourceData μ) (g : Lp ℝ 2 (potentialMeasure d.potential))
    (Du : Fin n → Fin n → Space n → ℝ) (η : (DualIndex n → ℝ) → ℝ)
    (ψ : Space n → ℝ) (x : Space n) : ℝ :=
  ψ x * dualSource d g η x * sourceBochnerDensity d (naturalCanonicalFlux d g) Du x +
    ∑ a : Fin n, sourceHalfMassFlux d (naturalCanonicalFlux d g) Du a x *
      dualEffectiveDerivative d g Du η ψ a x

theorem actual_dual_weak_Bochner (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    (hC : ∀ i b E, IsCompact E → MemLp (fun x => naturalCanonicalHessian d g Du x i b) 2 (volume.restrict E))
    (hMi : Integrable (sourceVectorMass d.potential (naturalCanonicalFlux d g)) (potentialMeasure d.potential))
    (Dg : Fin n → Space n → ℝ)
    (hgw : ∀ j, HasLocalWeakCoordinateDerivative (g : Space n → ℝ) (Dg j) j)
    (hDg : ∀ j, MemLp (Dg j) 2 (potentialMeasure d.potential))
    {η : (DualIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (dualBochnerIntegrand d g Du η ψ) (potentialMeasure d.potential) ∧
      Integrable (fun x => ψ x * dualSource d g η x *
        (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x)) (potentialMeasure d.potential) ∧
      (∫ x, dualBochnerIntegrand d g Du η ψ x ∂potentialMeasure d.potential) =
        ∫ x, ψ x * dualSource d g η x *
          (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x) ∂potentialMeasure d.potential := by
  obtain ⟨ζ, hζ, hcζ, hv, hD⟩ := exists_actual_dual_multiplier_lift d g Du hu hDu hw hC hη hcη
  obtain ⟨hJ, hF, he⟩ := actual_joint_weak_Bochner d hn g hg Du hu hDu hw hMi Dg hgw hDg
    hζ hcζ hψ hc
  have hEq : jointBochnerIntegrand d (naturalCanonicalFlux d g) Du ζ ψ
      =ᵐ[potentialMeasure d.potential] dualBochnerIntegrand d g Du η ψ := by
    filter_upwards [hv, ae_all_iff.mpr hD] with x hx hdx
    simp only [jointBochnerIntegrand, dualBochnerIntegrand, jointEffectiveDerivative,
      dualEffectiveDerivative, hx, hdx]
  have hFeq : (fun x => ψ x * jointSource d (naturalCanonicalFlux d g) ζ x *
      (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x))
      =ᵐ[potentialMeasure d.potential]
        (fun x => ψ x * dualSource d g η x *
          (∑ j : Fin n, Dg j x * naturalCanonicalFlux d g j x)) := by
    filter_upwards [hv] with x hx
    rw [hx]
  exact ⟨hJ.congr hEq, hF.congr hFeq, (integral_congr_ae hEq).symm.trans
    (he.trans (integral_congr_ae hFeq))⟩

end KLSConstantImprovement.ActualDualWeakBochner405
#print axioms KLSConstantImprovement.ActualDualWeakBochner405.actual_dual_weak_Bochner
