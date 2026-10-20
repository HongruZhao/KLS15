import KLSConstantImprovement.ActualSignedCoordinateExcess405
import KLSConstantImprovement.ActualFamilyTargetCutoffPlateau405
import KLSConstantImprovement.ActualDensityLimitInverseIdentification405
import KLSConstantImprovement.ActualFiniteFamilyWeakPassage405

/-! Actual local mass excess estimates on the expanding target family
give finite natural mass on its fixed original source.  The excess input
is literal, including the actual pullback target cutoffs and source
measure.  Its analytic Kato proof remains separate. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal BigOperators
namespace KLSConstantImprovement.ActualDensityMassFromLocalExcess405
open KLS ActualBoundedCanonicalSource ActualDensityWeightedL2405 ActualDensityInverseWeakCompactness405
open ActualCompactSignedWeakBound405 ActualSignedCoordinateExcess405 ActualDensityGradientCoefficient405
open ActualFamilyTargetCutoffPlateau405 ActualDensityLimitInverseIdentification405
open ActualFiniteFamilyWeakPassage405 ActualCanonicalMetricEnergyGraph ActualWeakCanonicalMetricInverse
open ActualSourceLocalizedGaffney405 ActualSourceNaturalGaffney405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {μ : Measure (Space n)} {ν : ℕ → Measure (Space n)}

theorem actual_density_limit_coordinate_bound_of_local_excess
    (d : ∀ k, SourceData (ν k)) (e : SourceData μ)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (hg0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hgrad : TendstoLocallyUniformly (fun k => gradient (d k).potential) (gradient e.potential) atTop)
    (W : DensityInverseAmbient n)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y) atTop
        (𝓝 (inner ℝ W Y)))
    {B D : ℝ}
    (hexcess : ∀ m : ℕ, ∀ᶠ k in atTop,
      Integrable (fun x => smoothCutoff n m (gradient (d k).potential x) ^ 2 *
        naturalMassExcess (d k) (g k) B x ^ 2) (potentialMeasure (d k).potential) ∧
      (∫ x, smoothCutoff n m (gradient (d k).potential x) ^ 2 *
        naturalMassExcess (d k) (g k) B x ^ 2 ∂potentialMeasure (d k).potential)
          ≤ D * (cutoffScale m) ^ 2) :
    ∀ i : Fin n, ∀ᵐ x ∂(volume : Measure (Space n)),
      |W i.succ x| ≤ B * densityHalf e.potential x := by
  obtain ⟨A, hA⟩ := actual_centered_family_global_potential_lower d hg0 (hφ 0)
  intro i
  let f (k : ℕ) := toVolumeL2 (d k).source_C1.continuous
    (canonicalMetricGradient (d k).potential i (sourceMetricInverseH1 (d k) (g k)))
  have hweak (z : Lp ℝ 2 (volume : Measure (Space n))) :
      Tendsto (fun k => inner ℝ (f k) z) atTop (𝓝 (inner ℝ (W i.succ) z)) := by
    simpa only [f, actualDensityInverseField, PiLp.toLp_apply, Fin.cases_succ] using
      finite_family_weak_coordinate_tendsto hw i.succ z
  apply ae_abs_le_of_compact_signed_excess (fun k => (d k).source_C1.continuous)
    e.source_C1.continuous hφ hA hweak
  intro r s hs ε hε
  let E := Metric.closedBall (0 : Space n) (r : ℝ)
  have hE : IsCompact E := isCompact_closedBall _ _
  obtain ⟨N, hN⟩ := actual_family_target_cutoff_plateau_on_compact d e hgrad E hE
  have ht : Tendsto (fun m => D * (cutoffScale m)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
      (cutoffScale_tendsto_zero.pow 2).const_mul D
  have hevent : ∀ᶠ m in atTop, D * (cutoffScale m)^2 < ε^2 :=
    ht.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨m, hmN, hmε⟩ := ((eventually_ge_atTop N).and hevent).exists
  filter_upwards [hexcess m, hN m hmN] with k hk hplateau
  have hb := actual_signed_compact_residual_norm_sq_le_cutoff_excess (d k) (g k)
    E hE i s B hs (fun x => smoothCutoff n m (gradient (d k).potential x)) hplateau hk.1
  apply (sq_le_sq₀ (norm_nonneg _) hε.le).mp
  exact hb.trans (hk.2.trans hmε.le)

theorem actual_density_limit_mass_bound_of_local_excess
    (d : ∀ k, SourceData (ν k)) (e : SourceData μ)
    (g : ∀ k, Lp ℝ 2 (potentialMeasure (d k).potential))
    (g₀ : Lp ℝ 2 (potentialMeasure e.potential))
    (hg0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hgrad : TendstoLocallyUniformly (fun k => gradient (d k).potential) (gradient e.potential) atTop)
    (W : DensityInverseAmbient n)
    (hw : ∀ Y : DensityInverseAmbient n,
      Tendsto (fun k => inner ℝ (actualDensityInverseField (d k) (g k)) Y) atTop
        (𝓝 (inner ℝ W Y)))
    (hid : ∀ i, (canonicalMetricGradient e.potential i (sourceMetricInverseH1 e g₀) : Space n → ℝ)
      =ᵐ[potentialMeasure e.potential]
        (fromVolumeL2 e.source_C1.continuous (W i.succ) : Space n → ℝ))
    {B D : ℝ} (hB : 0 ≤ B)
    (hexcess : ∀ m : ℕ, ∀ᶠ k in atTop,
      Integrable (fun x => smoothCutoff n m (gradient (d k).potential x) ^ 2 *
        naturalMassExcess (d k) (g k) B x ^ 2) (potentialMeasure (d k).potential) ∧
      (∫ x, smoothCutoff n m (gradient (d k).potential x) ^ 2 *
        naturalMassExcess (d k) (g k) B x ^ 2 ∂potentialMeasure (d k).potential)
          ≤ D * (cutoffScale m) ^ 2) :
    ∀ᵐ x ∂potentialMeasure e.potential,
      sourceVectorMass e.potential (naturalCanonicalFlux e g₀) x ≤ n * B ^ 2 :=
  actual_natural_mass_bound_of_density_coordinate_bound e g₀ W hid hB
    (actual_density_limit_coordinate_bound_of_local_excess d e g hg0 hφ hgrad W hw hexcess)

end KLSConstantImprovement.ActualDensityMassFromLocalExcess405
#print axioms KLSConstantImprovement.ActualDensityMassFromLocalExcess405.actual_density_limit_coordinate_bound_of_local_excess
#print axioms KLSConstantImprovement.ActualDensityMassFromLocalExcess405.actual_density_limit_mass_bound_of_local_excess
