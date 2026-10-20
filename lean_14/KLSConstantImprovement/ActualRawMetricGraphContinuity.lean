import KLSConstantImprovement.ActualCompactRawMetricGraph

/-! Closure of actual raw weak-gradient pairs in the canonical form graph. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualRawMetricGraphContinuity
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem rawCenteredMetricPair_tendsto {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    {F : ℕ → Fin n → Space n → ℝ} {G : Fin n → Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 (potentialMeasure φ))
    (hfd : ∀ k i, MemLp (rawCanonicalMetricDerivative φ (F k) i) 2 (potentialMeasure φ))
    (hg : MemLp g 2 (potentialMeasure φ))
    (hgd : ∀ i, MemLp (rawCanonicalMetricDerivative φ G i) 2 (potentialMeasure φ))
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 (potentialMeasure φ)) atTop (𝓝 0))
    (hdconv : ∀ i, Tendsto (fun k => eLpNorm
      (rawCanonicalMetricDerivative φ (F k) i - rawCanonicalMetricDerivative φ G i) 2
        (potentialMeasure φ)) atTop (𝓝 0)) :
    Tendsto (fun k => rawCenteredMetricPair (hf k) (hfd k))
      atTop (𝓝 (rawCenteredMetricPair hg hgd)) := by
  unfold rawCenteredMetricPair
  apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (continuous_centeredL2_center (potentialMeasure φ)).continuousAt.tendsto.comp
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv)
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k => rawCanonicalMetricDerivative φ (F k) i) (fun k => hfd k i)
      (rawCanonicalMetricDerivative φ G i) (hgd i)).mpr (hdconv i)

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_raw_metric_pair_mem
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    {E : Set (Space n)} (hE : IsCompact E)
    (hfE : tsupport f ⊆ E) (hFE : ∀ j, tsupport (F j) ⊆ E)
    (hf2 : MemLp f 2 (potentialMeasure d.potential))
    (hF2 : ∀ j, MemLp (F j) 2 (potentialMeasure d.potential))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j)
    (hd2 : ∀ i, MemLp (rawCanonicalMetricDerivative d.potential F i) 2
      (potentialMeasure d.potential)) :
    letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
    rawCenteredMetricPair hf2 hd2 ∈ canonicalMetricGraph d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨U, hu, hud⟩ := d.exists_metricH1_of_compact_rawWeak hE hfE hFE hf2 hF2 hFw
  have he : rawCenteredMetricPair hf2 hd2 = (U : WeightedEnergyAmbient d.potential) := by
    apply PiLp.ext
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · apply Lp.ext
      exact (rawCenteredMetricPair_value_ae hf2 hd2).trans hu.symm
    · apply Lp.ext
      exact (rawCenteredMetricPair_derivative_ae hf2 hd2 i).trans (hud i).symm
  rw [he]
  exact U.property

end KLSConstantImprovement.ActualRawMetricGraphContinuity
#print axioms KLSConstantImprovement.ActualRawMetricGraphContinuity.rawCenteredMetricPair_tendsto
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_raw_metric_pair_mem
