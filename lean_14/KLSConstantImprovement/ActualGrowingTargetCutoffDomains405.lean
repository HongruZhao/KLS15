import KLSConstantImprovement.ActualCenteredTargetForcing405
import KLS.WeightedFaithfulCutoff

/-! Every fixed target cutoff eventually pulls back to a genuine compact
source test along the actual growing-target family.  A single bump bound
gives uniform metric energy of order cutoffScale squared. -/
noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualGrowingTargetCutoffDomains405
open KLS ActualBoundedCanonicalSource ActualTargetInteriorPullbackSupport405
open ActualTargetPullbackCutoffEnergy405 ActualSourcePullbackMetricGradient405
open ActualCenteredTargetForcing405 ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {ρ : ℕ → Measure (Space n)}

theorem actual_target_pullback_eventually_compact
    (d : ∀ k, SourceData (ρ k)) (hadm : ∀ k, admissibleMeasure (ρ k))
    (hball : ∀ R : ℝ, ∀ᶠ k in atTop,
      closedBall (0 : Space n) R ⊆ interior (d k).targetSet)
    {χ : Space n → ℝ} (hcχ : HasCompactSupport χ) :
    ∀ᶠ k in atTop, HasCompactSupport (fun x => χ (gradient (d k).potential x)) := by
  obtain ⟨R, _hR, hR⟩ := hcχ.isBounded.exists_pos_norm_le
  filter_upwards [hball R] with k hk
  apply actual_target_pullback_compact (d k) (hadm k) hcχ
  intro y hy
  apply hk
  simpa only [mem_closedBall, dist_zero_right] using hR y hy

theorem actual_growing_target_cutoff_domains
    (d : ∀ k, SourceData (ρ k)) (hadm : ∀ k, admissibleMeasure (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hball : ∀ R : ℝ, ∀ᶠ k in atTop,
      closedBall (0 : Space n) R ⊆ interior (d k).targetSet) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, ∀ᶠ k in atTop,
      HasCompactSupport (fun x => smoothCutoff n m (gradient (d k).potential x)) ∧
      LocallyLipschitz (fun x => smoothCutoff n m (gradient (d k).potential x)) ∧
      (∀ i, HasLocalWeakCoordinateDerivative
        (fun x => smoothCutoff n m (gradient (d k).potential x))
        (pullbackRawGradient (d k) (smoothCutoff n m) i) i) ∧
      (∀ i E, IsCompact E → MemLp
        (pullbackRawGradient (d k) (smoothCutoff n m) i) 2 (volume.restrict E)) ∧
      ∀ᵐ x ∂potentialMeasure (d k).potential,
        pullbackMetricSquare (d k) (smoothCutoff n m) x ≤
          (16/c)*K^2*(cutoffScale m)^2 := by
  obtain ⟨K, hK, hgrad⟩ := smoothCutoff_gradient_bound (n := n)
  refine ⟨K, hK, fun m => ?_⟩
  let L : ℝ≥0 := ⟨cutoffScale m*K, mul_nonneg (cutoffScale_pos m).le hK⟩
  have hLip : LipschitzWith L (smoothCutoff n m) := by
    apply lipschitzWith_of_nnnorm_fderiv_le
      ((smoothCutoff_contDiff m).differentiable (by norm_num))
    intro x
    change ‖fderiv ℝ (smoothCutoff n m) x‖ ≤ cutoffScale m*K
    rw [← norm_gradient_eq_norm_fderiv]
    exact hgrad m x
  filter_upwards [actual_target_pullback_eventually_compact d hadm hball
    (smoothCutoff_hasCompactSupport m)] with k hk
  refine ⟨hk, (hLip.comp (d k).gradient_lipschitz).locallyLipschitz,
    (d k).pullback_hasLocalWeakCoordinateDerivative (smoothCutoff_contDiff m), ?_, ?_⟩
  · exact fun i E hE => (centeredTargetDatum_derivative_domains (d k)
      (smoothCutoff_contDiff m)).1 i E hE
  · have hγ := centeredTargetDatum_metric_square_uniform (d k) (smoothCutoff_contDiff m)
      hc (hκ k) (mul_nonneg (cutoffScale_pos m).le hK) (hgrad m)
    have he : (16/c)*(cutoffScale m*K)^2 = (16/c)*K^2*(cutoffScale m)^2 := by ring
    simpa only [pullbackMetricSquare, he] using hγ

end KLSConstantImprovement.ActualGrowingTargetCutoffDomains405
#print axioms KLSConstantImprovement.ActualGrowingTargetCutoffDomains405.actual_target_pullback_eventually_compact
#print axioms KLSConstantImprovement.ActualGrowingTargetCutoffDomains405.actual_growing_target_cutoff_domains
