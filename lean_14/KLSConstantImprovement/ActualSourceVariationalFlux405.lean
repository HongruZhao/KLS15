import KLSConstantImprovement.ActualSourceVariationalCaccioppoli405
import KLSConstantImprovement.ActualCanonicalMetricGraphClosure

/-!
The actual canonical variational solution is a weak divergence-form
solution on compact C1 tests. The flux is the local L2 function J p
already identified from its genuine weak gradient p. No classical
derivative of the solution or of the Hessian is used.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceVariationalFlux405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCanonicalMetricGraphClosure ActualSourceLocalWeakCalculus405
open ActualWeakCanonicalMetricSmoothing ActualWeakCanonicalMetricInverse
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_variational_compact_C1_test (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {τ : ℝ}
    (hU : ∀ V : CanonicalMetricH1 d.potential,
      τ * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
        canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    τ * (∫ x, canonicalMetricValue d.potential U x * ψ x ∂potentialMeasure d.potential) +
      (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i U x *
        canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential) =
      (∫ x, g x * ψ x ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) * (∫ x, ψ x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨V, hv, hd⟩ := d.exists_metricH1_of_compact hψ.locallyLipschitz hc
  have hψ2 := memLp_of_continuous_hasCompactSupport d.source_C1.continuous hψ.continuous hc
  have he := hU V
  rw [weighted_inner_centered_test hψ2 hv, weighted_inner_centered_test hψ2 hv,
    canonicalMetricValue_integral_eq_zero d.source_C1.continuous U,
    zero_mul, sub_zero, canonicalMetricEnergy_apply] at he
  have hi (i : Fin n) : inner ℝ (canonicalMetricGradient d.potential i U)
      (canonicalMetricGradient d.potential i V) =
      ∫ x, canonicalMetricGradient d.potential i U x *
        canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  simpa only [hi] using he

private theorem root_mul_compact_derivative_top (d : SourceData μ)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (i j k : Fin n) :
    MemLp (fun x => canonicalMetricRoot d.potential x i j * coordinateDerivative ψ k x)
      ∞ (potentialMeasure d.potential) := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_coordinateDerivative hc k).exists_bound_of_continuous
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) k).continuous
  have hd : MemLp (coordinateDerivative ψ k) ∞ (potentialMeasure d.potential) :=
    memLp_top_of_bound (measurable_coordinateDerivative ψ k).aestronglyMeasurable C
      (Eventually.of_forall hC)
  have he : (fun x => canonicalMetricRoot d.potential x i j * coordinateDerivative ψ k x) =
      fun x => (tsupport ψ).indicator (fun y => canonicalMetricRoot d.potential y i j) x *
        coordinateDerivative ψ k x := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · rw [indicator_of_mem hx]
    · have hz : coordinateDerivative ψ k x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (tsupport_coordinateDerivative_subset ψ k h))
      rw [hz, mul_zero, mul_zero]
  rw [he]
  exact (d.compact_metricRoot_entry_top hc i j).mul hd

theorem actual_metric_pair_eq_flux_pair (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i U x *
      canonicalMetricDerivative d.potential ψ i x ∂potentialMeasure d.potential) =
      ∫ x, ∑ i : Fin n, sourceWeakFlux d U i x * coordinateDerivative ψ i x
        ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hi (i : Fin n) : Integrable (fun x => canonicalMetricGradient d.potential i U x *
      canonicalMetricDerivative d.potential ψ i x) (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul (d.metric_derivative_memLp hψ hc i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hs : (canonicalMetricRoot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _
    simp only [canonicalMetricDerivative, sourceWeakFlux, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs.apply]
    ring

theorem actual_variational_flux_compact_C1_test (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {τ : ℝ}
    (hU : ∀ V : CanonicalMetricH1 d.potential,
      τ * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
        canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V))
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    τ * (∫ x, canonicalMetricValue d.potential U x * ψ x ∂potentialMeasure d.potential) +
      (∫ x, ∑ i : Fin n, sourceWeakFlux d U i x * coordinateDerivative ψ i x
        ∂potentialMeasure d.potential) =
      (∫ x, g x * ψ x ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) * (∫ x, ψ x ∂potentialMeasure d.potential) := by
  rw [← actual_metric_pair_eq_flux_pair d U hψ hc]
  exact actual_variational_compact_C1_test d U g hU hψ hc

theorem sourceWeakFlux_compact_derivative_integrable (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin n) :
    Integrable (fun x => sourceWeakFlux d U i x * coordinateDerivative ψ i x)
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hj (j : Fin n) : Integrable (fun x =>
      (canonicalMetricRoot d.potential x i j * coordinateDerivative ψ i x) *
        canonicalMetricGradient d.potential j U x) (potentialMeasure d.potential) := by
    have hm : MemLp (fun x =>
        (canonicalMetricRoot d.potential x i j * coordinateDerivative ψ i x) *
          canonicalMetricGradient d.potential j U x) 2 (potentialMeasure d.potential) :=
      (root_mul_compact_derivative_top d hψ hc i j i).mul (Lp.memLp _)
    exact hm.integrable (by norm_num)
  have hs := integrable_finsetSum Finset.univ (fun j _ => hj j)
  apply hs.congr
  exact Eventually.of_forall fun x => by
    unfold sourceWeakFlux
    dsimp only
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring

end KLSConstantImprovement.ActualSourceVariationalFlux405
#print axioms KLSConstantImprovement.ActualSourceVariationalFlux405.actual_variational_compact_C1_test
#print axioms KLSConstantImprovement.ActualSourceVariationalFlux405.actual_metric_pair_eq_flux_pair
#print axioms KLSConstantImprovement.ActualSourceVariationalFlux405.actual_variational_flux_compact_C1_test
#print axioms KLSConstantImprovement.ActualSourceVariationalFlux405.sourceWeakFlux_compact_derivative_integrable
