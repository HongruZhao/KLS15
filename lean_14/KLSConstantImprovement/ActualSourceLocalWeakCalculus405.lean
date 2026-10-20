import KLSConstantImprovement.ActualSourceMetricFaithfulness405
import KLSConstantImprovement.ActualBoundedRawMetricDomain

/-!
Actual local weak calculus of every canonical variational form element.
The weak gradient comes from the ordinary graph embedding. Compact C1
multiplication is proved in the canonical form itself, with its literal
product rule. No second derivative or strong generator core is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceLocalWeakCalculus405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualWeakCanonicalMetricCore ActualWeakCanonicalMetricSmoothing
open ActualWeakCanonicalMetricOrdinaryGraph ActualSourceMetricFaithfulness405
open ActualCompactRawMetricGraph ActualBoundedRawMetricDomain
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def sourceWeakGradient (d : SourceData μ) (U : CanonicalMetricH1 d.potential)
    (i : Fin n) : Space n → ℝ :=
  weightedH1Derivative d.potential i (sourceOrdinaryH1Embedding d U)

def sourceWeakFlux (d : SourceData μ) (U : CanonicalMetricH1 d.potential)
    (i : Fin n) (x : Space n) : ℝ :=
  ∑ j : Fin n, canonicalMetricRoot d.potential x i j *
    canonicalMetricGradient d.potential j U x

theorem sourceWeakGradient_hasLocalWeakDerivative (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n) :
    HasLocalWeakCoordinateDerivative (canonicalMetricValue d.potential U)
      (sourceWeakGradient d U i) i := by
  intro ψ hψ hc
  exact sourceMetricH1_unweighted_weak_identity d U hψ hc i

theorem raw_metric_sourceWeakGradient_ae (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n) :
    rawCanonicalMetricDerivative d.potential (sourceWeakGradient d U) i
      =ᵐ[potentialMeasure d.potential] canonicalMetricGradient d.potential i U := by
  have hp : ∀ᵐ x ∂potentialMeasure d.potential, ∀ j : Fin n,
      sourceWeakGradient d U j x = ∑ k : Fin n,
        canonicalMetricUnroot d.potential x j k * canonicalMetricGradient d.potential k U x :=
    ae_all_iff.mpr (fun j => sourceOrdinaryH1Embedding_derivative_ae d U j)
  filter_upwards [hp, d.hessian_ae_source] with x hx hpos
  unfold rawCanonicalMetricDerivative
  simp_rw [hx]
  change (canonicalMetricRoot d.potential x *ᵥ
    (canonicalMetricUnroot d.potential x *ᵥ
      (fun k => canonicalMetricGradient d.potential k U x))) i = _
  rw [Matrix.mulVec_mulVec, canonicalMetricRoot_mul_unroot_at hpos.1, Matrix.one_mulVec]

theorem sourceWeakFlux_local_L2 (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n)
    {E : Set (Space n)} (hE : IsCompact E) :
    MemLp (sourceWeakFlux d U i) 2 ((potentialMeasure d.potential).restrict E) := by
  have hr (j : Fin n) : MemLp (fun x => canonicalMetricRoot d.potential x i j) ∞
      ((potentialMeasure d.potential).restrict E) := by
    have hm := d.compact_metricRoot_entry_top hE i j
    have he := (memLp_indicator_iff_restrict hE.measurableSet.nullMeasurableSet).mp hm
    exact he
  exact memLp_finsetSum Finset.univ fun j _ =>
    (hr j).mul ((Lp.memLp (canonicalMetricGradient d.potential j U)).restrict E)

theorem sourceWeakFlux_eq_inverse_gradient_ae (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (i : Fin n) :
    sourceWeakFlux d U i =ᵐ[potentialMeasure d.potential] fun x =>
      ∑ j : Fin n, (coordinateHessian d.potential x)⁻¹ i j * sourceWeakGradient d U j x := by
  have hp : ∀ᵐ x ∂potentialMeasure d.potential, ∀ j : Fin n,
      sourceWeakGradient d U j x = ∑ k : Fin n,
        canonicalMetricUnroot d.potential x j k * canonicalMetricGradient d.potential k U x :=
    ae_all_iff.mpr (fun j => sourceOrdinaryH1Embedding_derivative_ae d U j)
  filter_upwards [hp, d.hessian_ae_source] with x hx hpos
  have hsym : (canonicalMetricRoot d.potential x).IsSymm :=
    inverseSqrtMatrix_isSymm _
  have hgram := canonicalMetricRoot_gram_at hpos.1
  rw [hsym.eq] at hgram
  unfold sourceWeakFlux
  simp_rw [hx]
  change (canonicalMetricRoot d.potential x *ᵥ
    (fun k => canonicalMetricGradient d.potential k U x)) i =
    ((coordinateHessian d.potential x)⁻¹ *ᵥ
      (canonicalMetricUnroot d.potential x *ᵥ
        (fun k => canonicalMetricGradient d.potential k U x))) i
  rw [← hgram, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (fun k => canonicalMetricGradient d.potential k U x)
    (canonicalMetricRoot d.potential x) (canonicalMetricUnroot d.potential x),
    canonicalMetricRoot_mul_unroot_at hpos.1, Matrix.one_mulVec]

theorem compact_metric_derivative_top (d : SourceData μ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) (i : Fin n) :
    MemLp (canonicalMetricDerivative d.potential χ i) ∞ (potentialMeasure d.potential) := by
  let E := tsupport χ
  have hd (j : Fin n) : MemLp (coordinateDerivative χ j) ∞ (potentialMeasure d.potential) := by
    obtain ⟨C, hC⟩ := (hasCompactSupport_coordinateDerivative hc j).exists_bound_of_continuous
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous
    exact memLp_top_of_bound (measurable_coordinateDerivative χ j).aestronglyMeasurable C
      (Eventually.of_forall hC)
  have he : canonicalMetricDerivative d.potential χ i = fun x =>
      ∑ j : Fin n, E.indicator (fun y => canonicalMetricRoot d.potential y i j) x *
        coordinateDerivative χ j x := by
    funext x
    by_cases hx : x ∈ E
    · simp only [canonicalMetricDerivative, indicator_of_mem hx]
    · have hz (j : Fin n) : coordinateDerivative χ j x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_coordinateDerivative_subset χ j h))
      simp only [canonicalMetricDerivative, indicator_of_notMem hx, hz, mul_zero,
        Finset.sum_const_zero]
  rw [he]
  exact memLp_finsetSum Finset.univ fun j _ =>
    (d.compact_metricRoot_entry_top hc i j).mul (hd j)

/-- Genuine compact multiplication in the actual canonical form domain.
The output has the exact raw weak-gradient product rule. -/
theorem exists_metricH1_compact_mul (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∃ V : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential V : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => χ x * canonicalMetricValue d.potential U x -
          ∫ y, χ y * canonicalMetricValue d.potential U y ∂potentialMeasure d.potential) ∧
      ∀ i : Fin n, (canonicalMetricGradient d.potential i V : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] fun x =>
          χ x * canonicalMetricGradient d.potential i U x +
            canonicalMetricValue d.potential U x * canonicalMetricDerivative d.potential χ i x := by
  let u : Space n → ℝ := canonicalMetricValue d.potential U
  let p := sourceWeakGradient d U
  let F := rawCutoffDerivative χ u p
  have hχtop : MemLp χ ∞ (potentialMeasure d.potential) := by
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ.continuous
    exact memLp_top_of_bound hχ.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  have hχdtop (j : Fin n) : MemLp (coordinateDerivative χ j) ∞ (potentialMeasure d.potential) := by
    obtain ⟨C, hC⟩ := (hasCompactSupport_coordinateDerivative hc j).exists_bound_of_continuous
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous
    exact memLp_top_of_bound (measurable_coordinateDerivative χ j).aestronglyMeasurable C
      (Eventually.of_forall hC)
  have hu : MemLp u 2 (potentialMeasure d.potential) := Lp.memLp _
  have hp (j : Fin n) : MemLp (p j) 2 (potentialMeasure d.potential) := Lp.memLp _
  have hf2 : MemLp (fun x => χ x * u x) 2 (potentialMeasure d.potential) := hχtop.mul hu
  have hF2 (j : Fin n) : MemLp (F j) 2 (potentialMeasure d.potential) :=
    (hχtop.mul (hp j)).add ((hχdtop j).mul hu)
  have hFE (j : Fin n) : tsupport (F j) ⊆ tsupport χ := by
    exact (tsupport_add _ _).trans
      (union_subset tsupport_mul_subset_left
        (tsupport_mul_subset_left.trans (tsupport_coordinateDerivative_subset χ j)))
  have hFw (j : Fin n) : HasLocalWeakCoordinateDerivative (fun x => χ x * u x) (F j) j := by
    obtain ⟨_, W, hWe, hW⟩ := weightedH1_compact_mul_hasWeakCoordinateDerivative d.source_C1
      (sourceOrdinaryH1Embedding d U) hχ hc j
    rw [sourceOrdinaryH1Embedding_value] at hW hWe
    have hW' : HasLocalWeakCoordinateDerivative (fun x => χ x * u x) (fun x => W x) j := by
      intro ψ hψ hψc
      exact hW ψ hψ hψc
    apply hW'.congr_ae Filter.EventuallyEq.rfl
    filter_upwards [hWe] with x hx
    change W x = χ x * weightedH1Derivative d.potential j (sourceOrdinaryH1Embedding d U) x +
      coordinateDerivative χ j x * canonicalMetricValue d.potential U x
    exact hx
  obtain ⟨V, hv, hd⟩ := d.exists_metricH1_of_compact_rawWeak hc tsupport_mul_subset_left hFE hf2 hF2 hFw
  refine ⟨V, hv, ?_⟩
  intro i
  apply (hd i).trans
  filter_upwards [raw_metric_sourceWeakGradient_ae d U i] with x hx
  change rawCanonicalMetricDerivative d.potential (rawCutoffDerivative χ u p) i x = _
  rw [rawCanonicalMetricDerivative_cutoff, hx]

end KLSConstantImprovement.ActualSourceLocalWeakCalculus405
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.sourceWeakGradient_hasLocalWeakDerivative
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.raw_metric_sourceWeakGradient_ae
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.sourceWeakFlux_local_L2
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.sourceWeakFlux_eq_inverse_gradient_ae
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.compact_metric_derivative_top
#print axioms KLSConstantImprovement.ActualSourceLocalWeakCalculus405.exists_metricH1_compact_mul
