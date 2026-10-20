import KLSConstantImprovement.ActualLocalRawWeakScalarChain405
import KLSConstantImprovement.ActualScalarTruncationL2405
import KLSConstantImprovement.ActualBoundedRawMetricDomain

/-!
The actual canonical form contains every genuine raw weak H1 function
with source L2 value and finite inverse-Hessian energy. The bounded
case is already proved using conservative source cutoffs. Concrete
smooth value truncations, their actual weak chain rule, and closed
metric-graph convergence remove boundedness. This proves form-domain
membership only and makes no assertion about a compact operator core.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators ContDiff Topology ENNReal NNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualMaximalRawMetricDomain405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualRawMetricGraphContinuity ActualBoundedRawMetricDomain
open ActualLocalRawWeakScalarChain405 ActualSmoothScalarTruncation405 ActualScalarTruncationL2405
variable {n : ℕ}

theorem rawCanonicalMetricDerivative_scalarFactor (φ c : Space n → ℝ)
    (F : Fin n → Space n → ℝ) (i : Fin n) (x : Space n) :
    rawCanonicalMetricDerivative φ (fun j y => c y * F j y) i x =
      c x * rawCanonicalMetricDerivative φ F i x := by
  simp only [rawCanonicalMetricDerivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The maximal raw finite-energy first-order domain is contained in the
actual closed canonical metric graph, with its literal weak coordinates.
No boundedness or local Lipschitz representative of f is assumed. -/
theorem _root_.KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.maximal_raw_metric_pair_mem
    {μ : Measure (Space n)} (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : MemLp f 2 (potentialMeasure d.potential))
    (hFloc : ∀ j E, IsCompact E → MemLp (F j) 2 (volume.restrict E))
    (hFw : ∀ j, HasLocalWeakCoordinateDerivative f (F j) j)
    (he : Integrable (rawInverseHessianGradientForm d.potential F) (potentialMeasure d.potential)) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => f x - ∫ y, f y ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential F i := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  let fk (k : ℕ) : Space n → ℝ := scalarClip k ∘ f
  let Fk (k : ℕ) (j : Fin n) (x : Space n) : ℝ := deriv (scalarClip k) (f x) * F j x
  have hfloc (E : Set (Space n)) (hE : IsCompact E) : MemLp f 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure hf d.source_C1.continuous hE
  have hfk (k : ℕ) : MemLp (fk k) 2 (potentialMeasure d.potential) := scalarClip_comp_memLp hf k
  have hFkloc (k : ℕ) (j : Fin n) (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (Fk k j) 2 (volume.restrict E) := by
    have hc := scalarClip_deriv_comp_top (hfloc E hE).aestronglyMeasurable k
    exact hc.mul (hFloc j E hE)
  have hFkw (k : ℕ) (j : Fin n) : HasLocalWeakCoordinateDerivative (fk k) (Fk k j) j := by
    obtain ⟨L, D, hL, hD⟩ := scalarClip_lipschitz k
    exact local_scalar_chain hfloc (hFloc j) (hFw j)
      ((scalarClip_contDiff k).of_le (by norm_num)) (scalarClip_zero k) hL hD
  have hd2 (i : Fin n) := d.raw_metric_derivative_memLp_of_energy hFloc he i
  have hfactor (k : ℕ) (i : Fin n) : rawCanonicalMetricDerivative d.potential (Fk k) i =
      fun x => deriv (scalarClip k) (f x) * rawCanonicalMetricDerivative d.potential F i x := by
    funext x
    exact rawCanonicalMetricDerivative_scalarFactor d.potential
      (fun y => deriv (scalarClip k) (f y)) F i x
  have hdk2 (k : ℕ) (i : Fin n) : MemLp
      (rawCanonicalMetricDerivative d.potential (Fk k) i) 2 (potentialMeasure d.potential) := by
    rw [hfactor]
    exact (scalarClip_deriv_comp_top hf.aestronglyMeasurable k).mul (hd2 i)
  have hke (k : ℕ) : Integrable (rawInverseHessianGradientForm d.potential (Fk k))
      (potentialMeasure d.potential) := by
    have hsum : Integrable (fun x => ∑ i, rawCanonicalMetricDerivative d.potential (Fk k) i x ^ 2)
        (potentialMeasure d.potential) :=
      integrable_finsetSum Finset.univ (fun i _ => (hdk2 k i).integrable_sq)
    exact hsum.congr (d.raw_metric_derivative_sq_ae (Fk k))
  have hmem (k : ℕ) : rawCenteredMetricPair (hfk k) (hdk2 k) ∈
      canonicalMetricGraph d.potential := by
    obtain ⟨B, hB⟩ := (scalarClip_compact k).exists_bound_of_continuous (scalarClip_contDiff k).continuous
    obtain ⟨U, hu, hud⟩ := d.bounded_raw_metric_pair_mem (hfk k).aestronglyMeasurable
      (fun x => hB (f x)) (hFkloc k) (hFkw k) (hke k)
    have hp : rawCenteredMetricPair (hfk k) (hdk2 k) = (U : WeightedEnergyAmbient d.potential) := by
      apply PiLp.ext
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · apply Lp.ext
        exact (rawCenteredMetricPair_value_ae (hfk k) (hdk2 k)).trans hu.symm
      · apply Lp.ext
        exact (rawCenteredMetricPair_derivative_ae (hfk k) (hdk2 k) i).trans (hud i).symm
    rw [hp]
    exact U.property
  have hconv : Tendsto (fun k => eLpNorm (fk k - f) 2 (potentialMeasure d.potential))
      atTop (𝓝 0) := scalarClip_comp_strong_L2 hf
  have hdconv (i : Fin n) : Tendsto (fun k => eLpNorm
      (rawCanonicalMetricDerivative d.potential (Fk k) i - rawCanonicalMetricDerivative d.potential F i) 2
        (potentialMeasure d.potential)) atTop (𝓝 0) := by
    simp_rw [hfactor]
    exact scalarClip_deriv_multiplier_strong_L2 hf.aestronglyMeasurable (hd2 i)
  have ht := rawCenteredMetricPair_tendsto hfk hdk2 hf hd2 hconv hdconv
  have hclosed : IsClosed (canonicalMetricGraph d.potential : Set (WeightedEnergyAmbient d.potential)) :=
    Submodule.isClosed_topologicalClosure _
  have hlim : rawCenteredMetricPair hf hd2 ∈ canonicalMetricGraph d.potential :=
    hclosed.mem_of_tendsto ht (Eventually.of_forall hmem)
  exact ⟨⟨_, hlim⟩, rawCenteredMetricPair_value_ae hf hd2,
    rawCenteredMetricPair_derivative_ae hf hd2⟩

end KLSConstantImprovement.ActualMaximalRawMetricDomain405

#print axioms KLSConstantImprovement.ActualMaximalRawMetricDomain405.rawCanonicalMetricDerivative_scalarFactor
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.maximal_raw_metric_pair_mem
