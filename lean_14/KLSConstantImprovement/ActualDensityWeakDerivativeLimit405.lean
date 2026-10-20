import KLSConstantImprovement.ActualDensityGradientPair405
import KLSConstantImprovement.ActualCenteredFamilyPotentialBound405

/-! The density-weighted actual inverse weak limit has its genuine raw
weak derivatives. Every compact derivative test is passed using the
constructed scalar and actual-Hessian coefficient pairings. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
namespace KLSConstantImprovement.ActualDensityWeakDerivativeLimit405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualDensityLimitInverseIdentification405 ActualDensityGradientPair405
open ActualDensityWeakScalarPair405 ActualFiniteFamilyWeakPassage405
open ActualCenteredFamilyPotentialBound405 ActualWeakCanonicalMetricInverse
open ActualSourceNaturalHessian405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ν : ℕ → Measure (Space n)} {μ : Measure (Space n)}

theorem actual_density_limit_raw_weak_derivatives
    (d : ∀ k, SourceData (ν k)) (d₀ : SourceData μ)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (W : DensityInverseAmbient n) {C κ : ℝ}
    (hκ : 0 < κ) (hk : ∀ k, κ ≤ (d k).targetConvexityConstant)
    (hgrad0 : ∀ k, gradient (d k).potential 0 = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (d₀.potential x)))
    (hH : ∀ᵐ x ∂(volume : Measure (Space n)), Tendsto
      (fun k => coordinateHessian (d k).potential x) atTop (𝓝 (coordinateHessian d₀.potential x)))
    (hb : ∀ k, ‖actualDensityInverseField (d k) (g k)‖ ≤ C)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y)
        atTop (𝓝 (inner ℝ W Y))) :
    ∀ i, HasLocalWeakCoordinateDerivative
      (densityLimitScalar d₀ W) (densityLimitRawGradient d₀ W i) i := by
  intro i ψ hψ hc
  obtain ⟨P, hP⟩ := actual_centered_family_compact_potential_upper
    d hκ hk hgrad0 (hφ 0) hc.isBounded
  have hfnorm (k : ℕ) : ‖sourceMetricInverse (d k) (g k)‖ ≤ C := by
    have h := (PiLp.norm_apply_le (actualDensityInverseField (d k) (g k)) 0).trans (hb k)
    simpa only [actualDensityInverseField, PiLp.toLp_apply, Fin.cases_zero, toVolumeL2_norm] using h
  have hw0 (Y : Lp ℝ 2 (volume : Measure (Space n))) :
      Tendsto (fun k => inner ℝ (toVolumeL2 (d k).source_C1.continuous
        (sourceMetricInverse (d k) (g k))) Y) atTop (𝓝 (inner ℝ (W 0) Y)) :=
    finite_family_weak_coordinate_tendsto hw 0 Y
  have hleft := raw_scalar_pair_tendsto_of_density_weak
    (fun k => (d k).source_C1.continuous) d₀.source_C1.continuous hφ
    (fun k => sourceMetricInverse (d k) (g k)) (W 0) hfnorm hw0
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i)
    (fun k x hx => hP k x (tsupport_coordinateDerivative_subset ψ i hx))
  have hright := actual_raw_gradient_pair_tendsto d d₀ g W hκ hk hφ hH hb hw
    hψ.continuous hc hP i
  exact tendsto_nhds_unique hleft (hright.neg.congr fun k =>
    (naturalCanonicalRawGradient_is_weak_derivative (d k) (g k) i ψ hψ hc).symm)

end KLSConstantImprovement.ActualDensityWeakDerivativeLimit405
#print axioms KLSConstantImprovement.ActualDensityWeakDerivativeLimit405.actual_density_limit_raw_weak_derivatives
