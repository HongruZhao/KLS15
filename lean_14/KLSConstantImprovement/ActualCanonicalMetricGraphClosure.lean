import KLSConstantImprovement.ActualWeakCanonicalMetricSmoothing
import KLS.WeightedFaithfulGraph

/-!
Actual centered metric-gradient pairs and their closure. Compact locally
Lipschitz functions belong to the same canonical metric graph using the
proved weak-source metric mollifiers, without a C4 source hypothesis.
-/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualCanonicalMetricGraphClosure
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricSmoothing
variable {n : ℕ}

def centeredMetricPair {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (canonicalMetricDerivative φ f i) 2 (potentialMeasure φ)) :
    WeightedEnergyAmbient φ :=
  WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure φ) (hf.toLp f))
    (fun i => (hd i).toLp (canonicalMetricDerivative φ f i)))

theorem centeredMetricPair_value_ae {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (canonicalMetricDerivative φ f i) 2 (potentialMeasure φ)) :
    ((centeredMetricPair hf hd 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => f x - ∫ y, f y ∂potentialMeasure φ := by
  have hi : (∫ x, (hf.toLp f) x ∂potentialMeasure φ) = ∫ x, f x ∂potentialMeasure φ :=
    integral_congr_ae hf.coeFn_toLp
  filter_upwards [CenteredL2.center_ae (potentialMeasure φ) (hf.toLp f), hf.coeFn_toLp]
    with x hx hy
  change CenteredL2.center (potentialMeasure φ) (hf.toLp f) x = _
  rw [hx, hi, hy]

theorem centeredMetricPair_derivative_ae {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i : Fin n, MemLp (canonicalMetricDerivative φ f i) 2 (potentialMeasure φ))
    (i : Fin n) :
    ((centeredMetricPair hf hd i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] canonicalMetricDerivative φ f i := (hd i).coeFn_toLp

/-- Strong convergence of actual values and actual metric derivatives is
strong convergence in the existing centered canonical metric ambient graph. -/
theorem centeredMetricPair_tendsto {φ : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] {f : ℕ → Space n → ℝ} {g : Space n → ℝ}
    (hf : ∀ k, MemLp (f k) 2 (potentialMeasure φ))
    (hfd : ∀ k (i : Fin n), MemLp (canonicalMetricDerivative φ (f k) i) 2 (potentialMeasure φ))
    (hg : MemLp g 2 (potentialMeasure φ))
    (hgd : ∀ i : Fin n, MemLp (canonicalMetricDerivative φ g i) 2 (potentialMeasure φ))
    (hconv : Tendsto (fun k => eLpNorm (f k - g) 2 (potentialMeasure φ)) atTop (𝓝 0))
    (hdconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (canonicalMetricDerivative φ (f k) i - canonicalMetricDerivative φ g i) 2
        (potentialMeasure φ)) atTop (𝓝 0)) :
    Tendsto (fun k => centeredMetricPair (hf k) (hfd k))
      atTop (𝓝 (centeredMetricPair hg hgd)) := by
  unfold centeredMetricPair
  apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
  apply tendsto_pi_nhds.mpr
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (continuous_centeredL2_center (potentialMeasure φ)).continuousAt.tendsto.comp
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mpr hconv)
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun k => canonicalMetricDerivative φ (f k) i) (fun k => hfd k i)
      (canonicalMetricDerivative φ g i) (hgd i)).mpr (hdconv i)

/-- Compact locally Lipschitz tests lie in the actual canonical metric
graph by the proved metric mollification; no numerical or closure premise. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_pair_mem {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f)
    (hf2 : MemLp f 2 (potentialMeasure d.potential))
    (hd2 : ∀ i : Fin n, MemLp (canonicalMetricDerivative d.potential f i) 2
      (potentialMeasure d.potential)) :
    letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
    centeredMetricPair hf2 hd2 ∈ canonicalMetricGraph d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨_, hm, hv, hd⟩ := d.compact_metric_smoothing hf hc
  have hpair := centeredMetricPair_tendsto
    (fun k => (hm k).2.2.1) (fun k => (hm k).2.2.2) hf2 hd2 hv (fun i => (hd i).2)
  have hclosed : IsClosed (canonicalMetricGraph d.potential : Set (WeightedEnergyAmbient d.potential)) :=
    Submodule.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hpair
  exact Eventually.of_forall fun k => Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨mollify k f, (hm k).1, (hm k).2.1,
      centeredMetricPair_value_ae (hm k).2.2.1 (hm k).2.2.2,
      centeredMetricPair_derivative_ae (hm k).2.2.1 (hm k).2.2.2⟩)

/-- Every compact locally Lipschitz test has its actual value and actual
metric derivatives in the same constructed canonical form domain. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metricH1_of_compact {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    ∃ U : CanonicalMetricH1 d.potential,
      ((canonicalMetricValue d.potential U : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
      ∀ i : Fin n,
        ((canonicalMetricGradient d.potential i U : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
          =ᵐ[potentialMeasure d.potential] canonicalMetricDerivative d.potential f i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨hf2, _, _, hd⟩ := d.compact_metric_smoothing hf hc
  exact ⟨⟨_, d.compact_metric_pair_mem hf hc hf2 (fun i => (hd i).1)⟩,
    centeredMetricPair_value_ae hf2 (fun i => (hd i).1),
    centeredMetricPair_derivative_ae hf2 (fun i => (hd i).1)⟩

end KLSConstantImprovement.ActualCanonicalMetricGraphClosure
#print axioms KLSConstantImprovement.ActualCanonicalMetricGraphClosure.centeredMetricPair_value_ae
#print axioms KLSConstantImprovement.ActualCanonicalMetricGraphClosure.centeredMetricPair_derivative_ae
#print axioms KLSConstantImprovement.ActualCanonicalMetricGraphClosure.centeredMetricPair_tendsto
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_pair_mem
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metricH1_of_compact
