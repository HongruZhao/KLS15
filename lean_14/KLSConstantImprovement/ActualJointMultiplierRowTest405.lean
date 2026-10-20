import KLSConstantImprovement.ActualJointMultiplierWeakTests405

/-! The actual differentiated natural equation tested by the bounded
compact joint row multiplier psi*eta(u,H)*u_j. This is a concrete weak
boundary/domain statement, before nonlinear joint truncations are removed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualJointMultiplierRowTest405
open KLS ActualBoundedCanonicalSource ActualSourceNaturalGaffney405
open ActualIntrinsicJointWeakTests405 ActualJointMultiplierWeakTests405
open ActualNaturalRowEnergyLocal405 ActualBoundedRawMetricDomain
open ActualSourceNaturalTargetCurvatureDomain405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_joint_row_equation (d : SourceData μ) (hn : 1 ≤ n)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    (hg : (∫ x, g x ∂potentialMeasure d.potential) = 0)
    (Du : Fin n → Fin n → Space n → ℝ)
    (hu : ∀ i E, IsCompact E → MemLp (naturalCanonicalFlux d g i) 2 (volume.restrict E))
    (hDu : ∀ i b E, IsCompact E → MemLp (Du i b) 2 (volume.restrict E))
    (hw : ∀ i b, HasLocalWeakCoordinateDerivative (naturalCanonicalFlux d g i) (Du i b) b)
    {Dg : Space n → ℝ} {j : Fin n}
    (hgw : HasLocalWeakCoordinateDerivative (g : Space n → ℝ) Dg j)
    (hDg : MemLp Dg 2 (potentialMeasure d.potential))
    {η : (JointIndex n → ℝ) → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∀ a, Integrable (fun x => Du a j x *
      rawCutoffDerivative ψ (jointSource d (naturalCanonicalFlux d g) (jointRow η j))
        (jointSourceDerivative d (naturalCanonicalFlux d g) Du (jointRow η j)) a x)
          (potentialMeasure d.potential)) ∧
      Integrable (fun x => (Dg x - naturalCanonicalRawGradient d g j x) *
        (ψ x * jointSource d (naturalCanonicalFlux d g) (jointRow η j) x)) (potentialMeasure d.potential) ∧
      (∑ a : Fin n, ∫ x, Du a j x *
        rawCutoffDerivative ψ (jointSource d (naturalCanonicalFlux d g) (jointRow η j))
          (jointSourceDerivative d (naturalCanonicalFlux d g) Du (jointRow η j)) a x
            ∂potentialMeasure d.potential) =
        ∫ x, (Dg x - naturalCanonicalRawGradient d g j x) *
          (ψ x * jointSource d (naturalCanonicalFlux d g) (jointRow η j) x)
            ∂potentialMeasure d.potential := by
  have he := jointRow_contDiff_compact hη hcη j
  obtain ⟨hv, hcc, _hb, hD, hW⟩ := actual_compact_joint_multiplier_test d hu hDu hw he.1 he.2 hψ hc
  exact natural_row_unbounded_compact_rawH1_test d hn g hg Du hu hDu hw hgw hDg hv hcc hD hW

end KLSConstantImprovement.ActualJointMultiplierRowTest405
#print axioms KLSConstantImprovement.ActualJointMultiplierRowTest405.actual_joint_row_equation
