import KLSConstantImprovement.ActualSourceVariationalFlux405

/-!
Actual canonical variational equations on compact raw H1 tests, including
finite-difference test candidates once their ordinary weak derivatives
are constructed. The actual inverse Hessian is controlled on the common
compact support. No Lipschitz test or second-order solution is assumed.
-/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff ENNReal RealInnerProductSpace
namespace KLSConstantImprovement.ActualSourceVariationalRawTest405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualCompactRawMetricGraph ActualSourceLocalWeakCalculus405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_variational_compact_rawH1_test (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {τ : ℝ}
    (hU : ∀ V : CanonicalMetricH1 d.potential,
      τ * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
        canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V))
    {ψ : Space n → ℝ} {F : Fin n → Space n → ℝ} {E : Set (Space n)}
    (hE : IsCompact E) (hψE : tsupport ψ ⊆ E) (hFE : ∀ i, tsupport (F i) ⊆ E)
    (hψ2 : MemLp ψ 2 (potentialMeasure d.potential))
    (hF2 : ∀ i, MemLp (F i) 2 (potentialMeasure d.potential))
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative ψ (F i) i) :
    τ * (∫ x, canonicalMetricValue d.potential U x * ψ x ∂potentialMeasure d.potential) +
      (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i U x *
        rawCanonicalMetricDerivative d.potential F i x ∂potentialMeasure d.potential) =
      (∫ x, g x * ψ x ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) * (∫ x, ψ x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  obtain ⟨V, hv, hd⟩ := d.exists_metricH1_of_compact_rawWeak hE hψE hFE hψ2 hF2 hFw
  have he := hU V
  rw [weighted_inner_centered_test hψ2 hv, weighted_inner_centered_test hψ2 hv,
    canonicalMetricValue_integral_eq_zero d.source_C1.continuous U,
    zero_mul, sub_zero, canonicalMetricEnergy_apply] at he
  have hi (i : Fin n) : inner ℝ (canonicalMetricGradient d.potential i U)
      (canonicalMetricGradient d.potential i V) =
      ∫ x, canonicalMetricGradient d.potential i U x *
        rawCanonicalMetricDerivative d.potential F i x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  simpa only [hi] using he

theorem actual_raw_metric_pair_eq_flux_pair (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential)
    {ψ : Space n → ℝ} {F : Fin n → Space n → ℝ} {E : Set (Space n)}
    (hE : IsCompact E) (hψE : tsupport ψ ⊆ E) (hFE : ∀ i, tsupport (F i) ⊆ E)
    (hψ2 : MemLp ψ 2 (potentialMeasure d.potential))
    (hF2 : ∀ i, MemLp (F i) 2 (potentialMeasure d.potential))
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative ψ (F i) i) :
    (∑ i : Fin n, ∫ x, canonicalMetricGradient d.potential i U x *
      rawCanonicalMetricDerivative d.potential F i x ∂potentialMeasure d.potential) =
      ∫ x, ∑ i : Fin n, sourceWeakFlux d U i x * F i x ∂potentialMeasure d.potential := by
  have hd2 (i : Fin n) :=
    (d.compact_raw_metric_smoothing hE hψE hFE hψ2 hF2 hFw).2.2 i |>.1
  have hprod (i : Fin n) : Integrable (fun x => canonicalMetricGradient d.potential i U x *
      rawCanonicalMetricDerivative d.potential F i x) (potentialMeasure d.potential) :=
    (Lp.memLp (canonicalMetricGradient d.potential i U)).integrable_mul (hd2 i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hprod i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    have hs : (canonicalMetricRoot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _
    simp only [rawCanonicalMetricDerivative, sourceWeakFlux, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs.apply]
    ring

theorem actual_variational_flux_compact_rawH1_test (d : SourceData μ)
    (U : CanonicalMetricH1 d.potential) (g : Lp ℝ 2 (potentialMeasure d.potential))
    {τ : ℝ}
    (hU : ∀ V : CanonicalMetricH1 d.potential,
      τ * inner ℝ (canonicalMetricValue d.potential U) (canonicalMetricValue d.potential V) +
        canonicalMetricEnergy d.potential U V = inner ℝ g (canonicalMetricValue d.potential V))
    {ψ : Space n → ℝ} {F : Fin n → Space n → ℝ} {E : Set (Space n)}
    (hE : IsCompact E) (hψE : tsupport ψ ⊆ E) (hFE : ∀ i, tsupport (F i) ⊆ E)
    (hψ2 : MemLp ψ 2 (potentialMeasure d.potential))
    (hF2 : ∀ i, MemLp (F i) 2 (potentialMeasure d.potential))
    (hFw : ∀ i, HasLocalWeakCoordinateDerivative ψ (F i) i) :
    τ * (∫ x, canonicalMetricValue d.potential U x * ψ x ∂potentialMeasure d.potential) +
      (∫ x, ∑ i : Fin n, sourceWeakFlux d U i x * F i x ∂potentialMeasure d.potential) =
      (∫ x, g x * ψ x ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) * (∫ x, ψ x ∂potentialMeasure d.potential) := by
  rw [← actual_raw_metric_pair_eq_flux_pair d U hE hψE hFE hψ2 hF2 hFw]
  exact actual_variational_compact_rawH1_test d U g hU hE hψE hFE hψ2 hF2 hFw

end KLSConstantImprovement.ActualSourceVariationalRawTest405
#print axioms KLSConstantImprovement.ActualSourceVariationalRawTest405.actual_variational_compact_rawH1_test
#print axioms KLSConstantImprovement.ActualSourceVariationalRawTest405.actual_raw_metric_pair_eq_flux_pair
#print axioms KLSConstantImprovement.ActualSourceVariationalRawTest405.actual_variational_flux_compact_rawH1_test
