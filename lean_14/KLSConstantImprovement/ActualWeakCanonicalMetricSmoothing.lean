import KLSConstantImprovement.ActualWeakCanonicalMetricCore
import KLS.AbsolutelyContinuousCompactSmoothing

/-!
Actual metric Sobolev smoothing on a common compact source support. The
inverse-root multiplier is locally essentially bounded by the actual AE MA
equation. Ordinary compact Sobolev mollification therefore converges in
the actual inverse-Hessian metric, without any C2/C4 source assumption.
-/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology NNReal ENNReal MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWeakCanonicalMetricSmoothing
open KLS ActualBoundedCanonicalSource ActualWeakCanonicalMetricCore
open ActualCanonicalMetricEnergyGraph
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

/-- The actual inverse-root entries, localized to any compact set, are
essentially bounded in the original source law. No continuous Hessian or
global inverse bound is assumed. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metricRoot_entry_top {μ : Measure (Space n)} (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (i j : Fin n) :
    MemLp (E.indicator (fun x => canonicalMetricRoot d.potential x i j)) ∞
      (potentialMeasure d.potential) := by
  have hinv := memLp_inverseHessian_top_on_compact_of_ae_equation d.source_lipschitz
    d.gradient_lipschitz d.target_smooth.continuous
    (d.hessian_ae.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hE j j
  have hess : eLpNormEssSup (fun x => (coordinateHessian d.potential x)⁻¹ j j)
      (volume.restrict E) < (∞ : ℝ≥0∞) := by
    rw [← eLpNorm_exponent_top hinv.aestronglyMeasurable]
    exact hinv
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hess
  have hb : ∀ᵐ x ∂volume.restrict E,
      ‖canonicalMetricRoot d.potential x i j‖ ≤ Real.sqrt (C : ℝ) := by
    filter_upwards [hC, ae_restrict_of_ae d.hessian_ae] with x hx hp
    have hi : ‖(coordinateHessian d.potential x)⁻¹ j j‖ ≤ (C : ℝ) := by
      exact_mod_cast hx
    have hgram := canonicalMetricRoot_gram_at hp.1
    have hsum : (∑ k : Fin n, canonicalMetricRoot d.potential x k j ^ 2) =
        (coordinateHessian d.potential x)⁻¹ j j := by
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
        congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j j) hgram
    have hs : canonicalMetricRoot d.potential x i j ^ 2 ≤
        (coordinateHessian d.potential x)⁻¹ j j := by
      rw [← hsum]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n => canonicalMetricRoot d.potential x k j ^ 2)
        (fun k _ => sq_nonneg (canonicalMetricRoot d.potential x k j))
        (Finset.mem_univ i)
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs, sq_abs] using
      hs.trans ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hi))
  have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
  have hbμ := (hac.restrict E).ae_le hb
  have hm := inverseSqrtMatrix_aestronglyMeasurable_of_ae_posDef
    (measurable_coordinateHessian d.potential) (d.hessian_ae_source.mono fun _ hx => hx.1)
  have hentry : AEStronglyMeasurable (fun x => canonicalMetricRoot d.potential x i j)
      (potentialMeasure d.potential) :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hm)
  apply memLp_top_of_bound (hentry.indicator hE.measurableSet) (Real.sqrt (C : ℝ))
  filter_upwards [(ae_restrict_iff' hE.measurableSet).mp hbμ] with x hx
  by_cases hxE : x ∈ E
  · simpa only [indicator_of_mem hxE] using hx hxE
  · rw [indicator_of_notMem hxE, norm_zero]
    exact Real.sqrt_nonneg _

/-- A compact locally Lipschitz test has genuine compact smooth mollifiers
converging in value and in every actual inverse-root-Hessian gradient
coordinate. The inverse metric is controlled only on the common compact
support, so no uniform global lower Hessian bound is needed. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_smoothing {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} (hf : LocallyLipschitz f) (hc : HasCompactSupport f) :
    MemLp f 2 (potentialMeasure d.potential) ∧
    (∀ k, ContDiff ℝ 3 (mollify k f) ∧ HasCompactSupport (mollify k f) ∧
      MemLp (mollify k f) 2 (potentialMeasure d.potential) ∧
      ∀ i : Fin n, MemLp (canonicalMetricDerivative d.potential (mollify k f) i) 2
        (potentialMeasure d.potential)) ∧
    Tendsto (fun k => eLpNorm (mollify k f - f) 2 (potentialMeasure d.potential))
      atTop (𝓝 0) ∧
    ∀ i : Fin n, MemLp (canonicalMetricDerivative d.potential f i) 2
      (potentialMeasure d.potential) ∧
      Tendsto (fun k => eLpNorm
        (canonicalMetricDerivative d.potential (mollify k f) i -
          canonicalMetricDerivative d.potential f i) 2 (potentialMeasure d.potential))
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
  have hs := compact_locallyLipschitz_absolutelyContinuous_smoothing hac hf hc
  have hf2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hf.continuous hc
  obtain ⟨C, hC, hderiv⟩ := compact_locallyLipschitz_coordinateDerivative_bound hf hc
  have hd2 (j : Fin n) : MemLp (coordinateDerivative f j) 2 (potentialMeasure d.potential) :=
    MemLp.of_bound (measurable_coordinateDerivative f j).aestronglyMeasurable C
      (Eventually.of_forall (hderiv j))
  let E := mollifierEnlargement (tsupport f)
  have hE : IsCompact E := isCompact_mollifierEnlargement hc
  have hfE : tsupport f ⊆ E := subset_mollifierEnlargement _
  have hmE (k : ℕ) : tsupport (mollify k f) ⊆ E := tsupport_mollify_subset hc k
  have hDf0 (j : Fin n) {x : Space n} (hx : x ∉ E) : coordinateDerivative f j x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hfE (tsupport_coordinateDerivative_subset f j h)))
  have hDm0 (k : ℕ) (j : Fin n) {x : Space n} (hx : x ∉ E) :
      coordinateDerivative (mollify k f) j x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (hmE k (tsupport_coordinateDerivative_subset (mollify k f) j h)))
  refine ⟨hf2, ?_, hs.2.1, ?_⟩
  · intro k
    exact ⟨(hs.1 k).1, (hs.1 k).2.1, (hs.1 k).2.2.1, fun i =>
      d.metric_derivative_memLp ((hs.1 k).1.of_le (by norm_num)) (hs.1 k).2.1 i⟩
  · intro i
    let a : Fin n → Space n → ℝ := fun j =>
      E.indicator (fun x => canonicalMetricRoot d.potential x i j)
    have ha (j : Fin n) : MemLp (a j) ∞ (potentialMeasure d.potential) :=
      d.compact_metricRoot_entry_top hE i j
    have heq : canonicalMetricDerivative d.potential f i =
        fun x => ∑ j : Fin n, a j x * coordinateDerivative f j x := by
      funext x
      by_cases hx : x ∈ E
      · simp only [canonicalMetricDerivative, a, indicator_of_mem hx]
      · simp only [canonicalMetricDerivative, a, indicator_of_notMem hx, hDf0 _ hx,
          mul_zero, zero_mul, Finset.sum_const_zero]
    have hfmetric : MemLp (canonicalMetricDerivative d.potential f i) 2
        (potentialMeasure d.potential) := by
      rw [heq]
      exact memLp_finsetSum Finset.univ fun j _ => (ha j).mul (hd2 j)
    have heqdiff (k : ℕ) :
        canonicalMetricDerivative d.potential (mollify k f) i - canonicalMetricDerivative d.potential f i =
        fun x => ∑ j : Fin n, a j x *
          (coordinateDerivative (mollify k f) j x - coordinateDerivative f j x) := by
      funext x
      by_cases hx : x ∈ E
      · simp only [canonicalMetricDerivative, a, indicator_of_mem hx, Pi.sub_apply,
          mul_sub, Finset.sum_sub_distrib]
      · simp only [canonicalMetricDerivative, a, indicator_of_notMem hx, Pi.sub_apply,
          hDf0 _ hx, hDm0 _ _ hx, mul_zero, zero_mul, sub_self, Finset.sum_const_zero]
    have hbound (k : ℕ) : eLpNorm
        (canonicalMetricDerivative d.potential (mollify k f) i -
          canonicalMetricDerivative d.potential f i) 2 (potentialMeasure d.potential) ≤
        ∑ j : Fin n, eLpNorm (a j) ∞ (potentialMeasure d.potential) *
          eLpNorm (coordinateDerivative (mollify k f) j - coordinateDerivative f j) 2
            (potentialMeasure d.potential) := by
      rw [heqdiff]
      calc
        _ = eLpNorm (∑ j : Fin n, fun x => a j x *
            (coordinateDerivative (mollify k f) j x - coordinateDerivative f j x)) 2
            (potentialMeasure d.potential) := by
          congr 1
          funext x
          simp only [Finset.sum_apply]
        _ ≤ ∑ j : Fin n, eLpNorm (fun x => a j x *
            (coordinateDerivative (mollify k f) j x - coordinateDerivative f j x)) 2
            (potentialMeasure d.potential) := eLpNorm_sum_le (by norm_num)
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          have hmul := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm
            (μ := potentialMeasure d.potential) (φ := a j)
            (f := coordinateDerivative (mollify k f) j - coordinateDerivative f j)
            2 (ha j).aestronglyMeasurable
          change eLpNorm (fun x => a j x *
            (coordinateDerivative (mollify k f) j x - coordinateDerivative f j x)) 2
            (potentialMeasure d.potential) ≤ _ at hmul
          exact hmul
    have hlim : Tendsto (fun k => ∑ j : Fin n,
        eLpNorm (a j) ∞ (potentialMeasure d.potential) *
          eLpNorm (coordinateDerivative (mollify k f) j - coordinateDerivative f j) 2
            (potentialMeasure d.potential)) atTop (𝓝 0) := by
      have hh := tendsto_finsetSum Finset.univ fun j _ =>
        ENNReal.Tendsto.const_mul (hs.2.2 j) (Or.inr (ha j).ne)
      simpa only [mul_zero, Finset.sum_const_zero] using hh
    exact ⟨hfmetric, tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hlim (fun _ => bot_le) hbound⟩

end KLSConstantImprovement.ActualWeakCanonicalMetricSmoothing
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metricRoot_entry_top
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.compact_metric_smoothing
