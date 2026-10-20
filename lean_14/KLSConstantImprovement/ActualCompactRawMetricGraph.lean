import KLSConstantImprovement.ActualCanonicalMetricGraphClosure
import KLSConstantImprovement.ActualCompactWeakH1Smoothing

/-!
The actual canonical form graph of a compact raw H1 function.

Metric coordinates are computed from its genuine weak derivatives F, not
from an unproved classical derivative of the function. This distinction is
essential for Hessian entries, whose actual source derivatives are the weak
third tensor. Membership is in the closed first-order form graph only.
-/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualCompactRawMetricGraph
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricGraphClosure ActualCompactWeakH1Smoothing
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def rawCanonicalMetricDerivative (φ : Space n → ℝ) (F : Fin n → Space n → ℝ)
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ j, canonicalMetricRoot φ x i j * F j x

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_raw_metric_smoothing
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    {E₀ : Set (Space n)} (hE₀ : IsCompact E₀)
    (hfE : tsupport f ⊆ E₀) (hFE : ∀ j, tsupport (F j) ⊆ E₀)
    (hf2 : MemLp f 2 (potentialMeasure d.potential))
    (hF2 : ∀ j, MemLp (F j) 2 (potentialMeasure d.potential))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j) :
    (∀ k, ContDiff ℝ 3 (mollify k f) ∧ HasCompactSupport (mollify k f) ∧
      MemLp (mollify k f) 2 (potentialMeasure d.potential) ∧
      ∀ i, MemLp (canonicalMetricDerivative d.potential (mollify k f) i) 2
        (potentialMeasure d.potential)) ∧
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 (potentialMeasure d.potential))
      atTop (𝓝 0) ∧
    ∀ i, MemLp (rawCanonicalMetricDerivative d.potential F i) 2
      (potentialMeasure d.potential) ∧
      Tendsto (fun k => eLpNorm
        (canonicalMetricDerivative d.potential (mollify k f) i -
          rawCanonicalMetricDerivative d.potential F i) 2 (potentialMeasure d.potential))
        atTop (𝓝 0) := by
  have hfc : HasCompactSupport f := hE₀.of_isClosed_subset (isClosed_tsupport f) hfE
  have hFc (j : Fin n) : HasCompactSupport (F j) :=
    hE₀.of_isClosed_subset (isClosed_tsupport (F j)) (hFE j)
  obtain ⟨hs, hv, hd⟩ := compact_rawWeak_weighted_smoothing
    d.source_C1.continuous hfc hf2 hF2 hFc hFw
  let E : Set (Space n) := mollifierEnlargement (tsupport f) ∪ E₀
  have hE : IsCompact E := (isCompact_mollifierEnlargement hfc).union hE₀
  have hFE' (j : Fin n) : tsupport (F j) ⊆ E := (hFE j).trans subset_union_right
  have hmE (k : ℕ) : tsupport (mollify k f) ⊆ E :=
    (tsupport_mollify_subset hfc k).trans subset_union_left
  have hF0 (j : Fin n) {x : Space n} (hx : x ∉ E) : F j x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hFE' j h))
  have hDm0 (k : ℕ) (j : Fin n) {x : Space n} (hx : x ∉ E) :
      coordinateDerivative (mollify k f) j x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (hmE k (tsupport_coordinateDerivative_subset (mollify k f) j h)))
  refine ⟨?_, hv, ?_⟩
  · intro k
    exact ⟨(hs k).1, (hs k).2.1, (hs k).2.2.1, fun i =>
      d.metric_derivative_memLp ((hs k).1.of_le (by norm_num)) (hs k).2.1 i⟩
  · intro i
    let a : Fin n → Space n → ℝ := fun j =>
      E.indicator (fun x => canonicalMetricRoot d.potential x i j)
    have ha (j : Fin n) : MemLp (a j) ∞ (potentialMeasure d.potential) :=
      d.compact_metricRoot_entry_top hE i j
    have heq : rawCanonicalMetricDerivative d.potential F i =
        fun x => ∑ j, a j x * F j x := by
      funext x
      by_cases hx : x ∈ E
      · simp only [rawCanonicalMetricDerivative, a, indicator_of_mem hx]
      · simp only [rawCanonicalMetricDerivative, a, indicator_of_notMem hx, hF0 _ hx,
          mul_zero, zero_mul, Finset.sum_const_zero]
    have hraw : MemLp (rawCanonicalMetricDerivative d.potential F i) 2
        (potentialMeasure d.potential) := by
      rw [heq]
      exact memLp_finsetSum Finset.univ fun j _ => (ha j).mul (hF2 j)
    have heqdiff (k : ℕ) :
        canonicalMetricDerivative d.potential (mollify k f) i -
          rawCanonicalMetricDerivative d.potential F i =
        fun x => ∑ j, a j x * (coordinateDerivative (mollify k f) j x - F j x) := by
      funext x
      by_cases hx : x ∈ E
      · simp only [canonicalMetricDerivative, rawCanonicalMetricDerivative, a,
          indicator_of_mem hx, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      · simp only [canonicalMetricDerivative, rawCanonicalMetricDerivative, a,
          indicator_of_notMem hx, Pi.sub_apply, hF0 _ hx, hDm0 _ _ hx,
          mul_zero, zero_mul, sub_self, Finset.sum_const_zero]
    have hb (k : ℕ) : eLpNorm
        (canonicalMetricDerivative d.potential (mollify k f) i -
          rawCanonicalMetricDerivative d.potential F i) 2 (potentialMeasure d.potential) ≤
        ∑ j, eLpNorm (a j) ∞ (potentialMeasure d.potential) *
          eLpNorm (coordinateDerivative (mollify k f) j - F j) 2 (potentialMeasure d.potential) := by
      rw [heqdiff]
      calc
        _ = eLpNorm (∑ j : Fin n, fun x => a j x *
            (coordinateDerivative (mollify k f) j x - F j x)) 2
            (potentialMeasure d.potential) := by
          congr 1
          funext x
          simp only [Finset.sum_apply]
        _ ≤ ∑ j, eLpNorm (fun x => a j x *
            (coordinateDerivative (mollify k f) j x - F j x)) 2
            (potentialMeasure d.potential) := eLpNorm_sum_le (by norm_num)
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have hmul := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
            (μ := potentialMeasure d.potential) (φ := a j)
            (f := coordinateDerivative (mollify k f) j - F j)
            2 (ha j).aestronglyMeasurable
          change eLpNorm (fun x => a j x *
            (coordinateDerivative (mollify k f) j x - F j x)) 2
            (potentialMeasure d.potential) ≤ _ at hmul
          exact hmul
    have ht : Tendsto (fun k => ∑ j,
        eLpNorm (a j) ∞ (potentialMeasure d.potential) *
          eLpNorm (coordinateDerivative (mollify k f) j - F j) 2
            (potentialMeasure d.potential)) atTop (𝓝 0) := by
      have hh := tendsto_finsetSum Finset.univ fun j _ =>
        ENNReal.Tendsto.const_mul (hd j) (Or.inr (ha j).eLpNorm_ne_top)
      simpa only [mul_zero, Finset.sum_const_zero] using hh
    exact ⟨hraw, tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ht (fun _ => bot_le) hb⟩

def rawCenteredMetricPair {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i, MemLp (rawCanonicalMetricDerivative φ F i) 2 (potentialMeasure φ)) :
    WeightedEnergyAmbient φ :=
  WithLp.toLp 2 (Fin.cases (CenteredL2.center (potentialMeasure φ) (hf.toLp f))
    (fun i => (hd i).toLp (rawCanonicalMetricDerivative φ F i)))

theorem rawCenteredMetricPair_value_ae {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i, MemLp (rawCanonicalMetricDerivative φ F i) 2 (potentialMeasure φ)) :
    ((rawCenteredMetricPair hf hd 0 : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] fun x => f x - ∫ y, f y ∂potentialMeasure φ := by
  have hi : (∫ x, (hf.toLp f) x ∂potentialMeasure φ) = ∫ x, f x ∂potentialMeasure φ :=
    integral_congr_ae hf.coeFn_toLp
  filter_upwards [CenteredL2.center_ae (potentialMeasure φ) (hf.toLp f), hf.coeFn_toLp]
    with x hx hy
  change CenteredL2.center (potentialMeasure φ) (hf.toLp f) x = _
  rw [hx, hi, hy]

theorem rawCenteredMetricPair_derivative_ae {φ f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)]
    (hf : MemLp f 2 (potentialMeasure φ))
    (hd : ∀ i, MemLp (rawCanonicalMetricDerivative φ F i) 2 (potentialMeasure φ)) (i : Fin n) :
    ((rawCenteredMetricPair hf hd i.succ : Lp ℝ 2 (potentialMeasure φ)) : Space n → ℝ)
      =ᵐ[potentialMeasure φ] rawCanonicalMetricDerivative φ F i := (hd i).coeFn_toLp

theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metricH1_of_compact_rawWeak
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    {E : Set (Space n)} (hE : IsCompact E)
    (hfE : tsupport f ⊆ E) (hFE : ∀ j, tsupport (F j) ⊆ E)
    (hf2 : MemLp f 2 (potentialMeasure d.potential))
    (hF2 : ∀ j, MemLp (F j) 2 (potentialMeasure d.potential))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j) :
    ∃ U : CanonicalMetricH1 d.potential,
      ((canonicalMetricValue d.potential U : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
      ∀ i, ((canonicalMetricGradient d.potential i U : Lp ℝ 2 (potentialMeasure d.potential)) : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨hs, hv, hd⟩ := d.compact_raw_metric_smoothing hE hfE hFE hf2 hF2 hFw
  have hpair : Tendsto
      (fun k => centeredMetricPair (hs k).2.2.1 (hs k).2.2.2)
      atTop (𝓝 (rawCenteredMetricPair hf2 (fun i => (hd i).1))) := by
    unfold centeredMetricPair rawCenteredMetricPair
    apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact (continuous_centeredL2_center (potentialMeasure d.potential)).continuousAt.tendsto.comp
        ((Lp.tendsto_Lp_iff_tendsto_eLpNorm''
          (fun k => mollify k f) (fun k => (hs k).2.2.1) f hf2).mpr hv)
    · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun k => canonicalMetricDerivative d.potential (mollify k f) i)
        (fun k => (hs k).2.2.2 i) (rawCanonicalMetricDerivative d.potential F i)
        (hd i).1).mpr (hd i).2
  have hmem : rawCenteredMetricPair hf2 (fun i => (hd i).1) ∈ canonicalMetricGraph d.potential := by
    have hclosed : IsClosed (canonicalMetricGraph d.potential : Set (WeightedEnergyAmbient d.potential)) :=
      Submodule.isClosed_topologicalClosure _
    apply hclosed.mem_of_tendsto hpair
    exact Eventually.of_forall fun k => Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨mollify k f, (hs k).1, (hs k).2.1,
        centeredMetricPair_value_ae (hs k).2.2.1 (hs k).2.2.2,
        centeredMetricPair_derivative_ae (hs k).2.2.1 (hs k).2.2.2⟩)
  exact ⟨⟨_, hmem⟩, rawCenteredMetricPair_value_ae hf2 (fun i => (hd i).1),
    rawCenteredMetricPair_derivative_ae hf2 (fun i => (hd i).1)⟩

end KLSConstantImprovement.ActualCompactRawMetricGraph
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_raw_metric_smoothing
#print axioms KLSConstantImprovement.ActualCompactRawMetricGraph.rawCenteredMetricPair_value_ae
#print axioms KLSConstantImprovement.ActualCompactRawMetricGraph.rawCenteredMetricPair_derivative_ae
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.exists_metricH1_of_compact_rawWeak
