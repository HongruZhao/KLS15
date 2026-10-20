import KLSConstantImprovement.ActualCenteredSourceData405
import KLSConstantImprovement.ActualC11SourceCompactness405
import KLSConstantImprovement.ActualMomentMapLimit405
import KLSConstantImprovement.ActualInteriorCapConfinement405
import KLSConstantImprovement.ActualC11MomentSourceRealization405

/-! A genuine subsequential original-law SourceData from uniformly C1,1
actual bounded-target sources.  Every inverse field is to be placed on the
displayed centeredCanonicalSource, not on the uncentered input source. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualCenteredSourceLimit405
open KLS ActualBoundedCanonicalSource ActualSourceCentering405 ActualCenteredSourceTransport405
open ActualCenteredSourceData405 ActualC11SourceCompactness405 ActualMomentMapLimit405
open ActualInteriorCapConfinement405 ActualC11MomentSourceRealization405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_centered_sourceData_subseq_limit
    (d₀ : SourceData μ) (hn : 1 ≤ n) [IsProbabilityMeasure μ]
    {ρ : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ρ k))
    {c : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hweak : ∀ (v : Space n → ℝ), Continuous v → ∀ B : ℝ, (∀ x, ‖v x‖ ≤ B) →
      Tendsto (fun k => ∫ y, v y ∂ρ k) atTop (𝓝 (∫ y, v y ∂μ))) :
    ∃ (s : ℕ → ℕ) (e : SourceData μ), StrictMono s ∧
      e.targetPotential = d₀.targetPotential ∧ e.targetSet = d₀.targetSet ∧
      e.targetConvexityConstant = d₀.targetConvexityConstant ∧
      TendstoLocallyUniformly (fun k => gradient (centeredCanonicalSource (d (s k))).potential)
        (gradient e.potential) atTop ∧
      (∀ x, Tendsto (fun k => (centeredCanonicalSource (d (s k))).potential x) atTop
        (𝓝 (e.potential x))) := by
  letI : ∀ k, IsProbabilityMeasure (ρ k) := fun k => by
    letI : IsProbabilityMeasure (potentialMeasure (d k).potential) := (d k).source_probability
    have hm : (potentialMeasure (d k).potential).map (gradient (d k).potential) = ρ k := (d k).pushforward
    rw [← hm]
    infer_instance
  let f : ℕ → Space n → ℝ := fun k => centeredSourcePotential (d k)
  let L : ℝ≥0 := ⟨16/c, div_nonneg (by norm_num) hc.le⟩
  have hL (k : ℕ) : LipschitzWith L (gradient (f k)) := by
    apply (centeredSourcePotential_gradient_lipschitz (d k)).weaken
    change 16/(d k).targetConvexityConstant ≤ 16/c
    exact div_le_div_of_nonneg_left (by norm_num) hc (hκ k)
  obtain ⟨ψ, s, hs, hψ, hcψ, hψ0, hgψ0, hgψ, hflim, hglim⟩ :=
    exists_subseq_centered_C11_potentials L f
      (fun k => centeredSourcePotential_C1 (d k))
      (fun k => centeredSourcePotential_convex (d k))
      (fun k => centeredSourcePotential_zero (d k))
      (fun k => centeredSourcePotential_gradient_zero (d k)) hL
  have hE (k : ℕ) : momentDualEnergy (ρ (s k)) (f (s k)) ≤ ENNReal.ofReal n :=
    centeredSourcePotential_dualEnergy (d (s k))
  have hweakS (v : Space n → ℝ) (hv : Continuous v) (B : ℝ) (hb : ∀ x, ‖v x‖ ≤ B) :
      Tendsto (fun k => ∫ y, v y ∂ρ (s k)) atTop (𝓝 (∫ y, v y ∂μ)) :=
    (hweak v hv B hb).comp hs.tendsto_atTop
  have hcompact (v : Space n → ℝ) (hv : Continuous v) (hvc : HasCompactSupport v) :
      Tendsto (fun k => ∫ y, v y ∂ρ (s k)) atTop (𝓝 (∫ y, v y ∂μ)) := by
    obtain ⟨B, hB⟩ := hvc.exists_bound_of_continuous hv
    exact hweakS v hv B hB
  obtain ⟨a, B, ha, hB, hcone⟩ := actual_bounded_target_limit_uniform_cone d₀ hn
    (by positivity : 0 ≤ (n : ℝ)) hE hcompact
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcone
  let t : ℕ → ℕ := fun k => N+k
  have ht : StrictMono t := fun i j hij => Nat.add_lt_add_left hij N
  let F : ℕ → Space n → ℝ := fun k => f (s (t k))
  have hFc (k : ℕ) (x : Space n) : a*‖x‖-B ≤ F k x :=
    hN (N+k) (Nat.le_add_right N k) x
  have hFp (x : Space n) : Tendsto (fun k => F k x) atTop (𝓝 (ψ x)) :=
    (hflim x).comp ht.tendsto_atTop
  have hGp (x : Space n) : Tendsto (fun k => gradient (F k) x) atTop (𝓝 (gradient ψ x)) :=
    (hglim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)).comp ht.tendsto_atTop
  have hmap (k : ℕ) : (potentialMeasure (normalizedMomentPotential (F k))).map
      (gradient (normalizedMomentPotential (F k))) = ρ (s (t k)) :=
    centeredSourcePotential_pushforward (d (s (t k)))
  have htarget := gradient_pushforward_normalized_limit
    (fun k => centeredSourcePotential_C1 (d (s (t k)))) hψ ha hFc hFp hGp hmap
    (fun v => (hweakS v v.continuous ‖v‖ v.norm_coe_le_norm).comp ht.tendsto_atTop)
  have hiψ := integrable_exp_neg_of_linear_coercivity hψ.continuous.aestronglyMeasurable
    ha (limit_linear_cone hFc hFp)
  have hnorm : ContDiff ℝ 1 (normalizedMomentPotential ψ) := by
    unfold normalizedMomentPotential
    exact hψ.add contDiff_const
  have hconv : ConvexOn ℝ univ (normalizedMomentPotential ψ) := by
    change ConvexOn ℝ univ (fun x => ψ x + Real.log (momentPartitionFunction ψ))
    exact hcψ.add_const _
  let e := realizeC11MomentSource d₀ (normalizedMomentPotential ψ) hnorm hconv
    (isProbabilityMeasure_normalizedMomentPotential hiψ) htarget
  have he : e.potential = normalizedMomentPotential ψ :=
    realizeC11MomentSource_potential _ _ _ _ _ _
  have heTarget := realizeC11MomentSource_target d₀ (normalizedMomentPotential ψ) hnorm hconv
    (isProbabilityMeasure_normalizedMomentPotential hiψ) htarget
  have hloc : TendstoLocallyUniformly (fun k => gradient (F k)) (gradient ψ) atTop := by
    intro u hu x
    obtain ⟨E, hE, hev⟩ := hglim u hu x
    exact ⟨E, hE, ht.tendsto_atTop.eventually hev⟩
  have hZ := tendsto_partition_of_common_linear_cone
    (fun k => (centeredSourcePotential_C1 (d (s (t k)))).continuous) ha hFc hFp
  have hlog := (Real.continuousAt_log (integral_exp_pos hiψ).ne').tendsto.comp hZ
  refine ⟨fun k => s (t k), e, hs.comp ht, heTarget.1, heTarget.2.1, heTarget.2.2, ?_, ?_⟩
  · rw [he]
    simp_rw [centeredCanonicalSource_potential, gradient_normalizedMomentPotential]
    exact hloc
  · intro x
    rw [he]
    simpa only [centeredCanonicalSource_potential, normalizedMomentPotential, momentPartitionFunction,
      Function.comp_def, F, f] using (hFp x).add hlog

end KLSConstantImprovement.ActualCenteredSourceLimit405
#print axioms KLSConstantImprovement.ActualCenteredSourceLimit405.exists_centered_sourceData_subseq_limit
