import KLSConstantImprovement.ActualBoundedRawSourceCalculus405
import KLSConstantImprovement.ActualBoundedRawMetricDomain
import KLSConstantImprovement.ActualSourceVariationalRawTest405
import KLSConstantImprovement.ActualSourcePullbackMetricGradient405
import KLSConstantImprovement.ActualSourceNaturalTargetCurvatureDomain405

/-! Actual global bounded raw tests and smooth target pullbacks belong to
the constructed natural form. Their variational identities impose the
literal global target weak-divergence condition; no graph core is assumed. -/
noncomputable section
open MeasureTheory Matrix InnerProductSpace Filter
open scoped BigOperators
namespace KLSConstantImprovement.ActualGlobalRawFormTest405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph
open ActualBoundedRawTestAlgebra405 ActualBoundedRawMetricDomain
open ActualWeakCanonicalMetricInverse ActualSourceVariationalFlux405
open ActualWeakCanonicalMetricOrdinaryGraph
open ActualSourcePullbackMetricGradient405 ActualSourceNaturalTargetCurvatureDomain405
open ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_boundedRawTest_form (d : SourceData μ) (f : BoundedRawTest d) :
    ∃ U : CanonicalMetricH1 d.potential,
      (canonicalMetricValue d.potential U : Space n → ℝ) =ᵐ[potentialMeasure d.potential]
        (fun x => f.value x - ∫ y, f.value y ∂potentialMeasure d.potential) ∧
      ∀ i, (canonicalMetricGradient d.potential i U : Space n → ℝ)
        =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential f.derivative i := by
  obtain ⟨B, hb⟩ := f.bounded
  have he : Integrable (rawInverseHessianGradientForm d.potential f.derivative)
      (potentialMeasure d.potential) :=
    (integrable_finsetSum Finset.univ (fun i _ => (f.metric_gradient i).integrable_sq)).congr
      (d.raw_metric_derivative_sq_ae f.derivative)
  exact d.bounded_raw_metric_pair_mem f.measurable hb f.derivative_local f.weak_derivative he

def boundedRawTestForm (d : SourceData μ) (f : BoundedRawTest d) : CanonicalMetricH1 d.potential :=
  Classical.choose (exists_boundedRawTest_form d f)

theorem boundedRawTestForm_value (d : SourceData μ) (f : BoundedRawTest d) :
    (canonicalMetricValue d.potential (boundedRawTestForm d f) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential]
        (fun x => f.value x - ∫ y, f.value y ∂potentialMeasure d.potential) :=
  (Classical.choose_spec (exists_boundedRawTest_form d f)).1

theorem boundedRawTestForm_gradient (d : SourceData μ) (f : BoundedRawTest d) (i : Fin n) :
    (canonicalMetricGradient d.potential i (boundedRawTestForm d f) : Space n → ℝ)
      =ᵐ[potentialMeasure d.potential] rawCanonicalMetricDerivative d.potential f.derivative i :=
  (Classical.choose_spec (exists_boundedRawTest_form d f)).2 i

theorem actual_variational_bounded_raw_test (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential)) (f : BoundedRawTest d) :
    (∑ i, ∫ x, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
      rawCanonicalMetricDerivative d.potential f.derivative i x ∂potentialMeasure d.potential) =
      (∫ x, g x * f.value x ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) * (∫ x, f.value x ∂potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hf2 : MemLp f.value 2 (potentialMeasure d.potential) := f.value_top.mono_exponent (by simp)
  have he := sourceMetricInverse_variational d g (boundedRawTestForm d f)
  rw [weighted_inner_centered_test hf2 (boundedRawTestForm_value d f), canonicalMetricEnergy_apply] at he
  have hi (i : Fin n) : inner ℝ (canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g))
      (canonicalMetricGradient d.potential i (boundedRawTestForm d f)) =
      ∫ x, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
        rawCanonicalMetricDerivative d.potential f.derivative i x ∂potentialMeasure d.potential := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [boundedRawTestForm_gradient d f i] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  simpa only [hi] using he

def pullbackTest (d : SourceData μ) (f : Space n → ℝ) (hf : ContDiff ℝ 1 f) : BoundedRawTest d where
  value := fun x => f (gradient d.potential x)
  derivative := pullbackRawGradient d f
  measurable := (d.continuous_comp_gradient_memLp hf.continuous 2).aestronglyMeasurable
  bounded := by
    obtain ⟨B, _, hb⟩ := d.exists_bound_continuous_comp_gradient hf.continuous
    exact ⟨B, hb⟩
  derivative_local := fun a E hE =>
    KLS.MemLp.restrict_volume_of_potentialMeasure (d.pullback_weak_derivative_memLp hf a 2)
      d.source_C1.continuous hE
  weak_derivative := d.pullback_hasLocalWeakCoordinateDerivative hf
  metric_gradient := by
    intro r
    letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
    exact (pullback_raw_metric_gradient_memLp_top d hf r).mono_exponent (by simp)

theorem actual_target_pullback_variational (d : SourceData μ)
    (g : Lp ℝ 2 (potentialMeasure d.potential))
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x, ∑ i, naturalCanonicalRawGradient d g i x * gradient f (gradient d.potential x) i
      ∂potentialMeasure d.potential) =
      (∫ x, g x * f (gradient d.potential x) ∂potentialMeasure d.potential) -
        (∫ x, g x ∂potentialMeasure d.potential) *
          (∫ x, f (gradient d.potential x) ∂potentialMeasure d.potential) := by
  have he := actual_variational_bounded_raw_test d g (pullbackTest d f hf)
  change (∑ i, ∫ x, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
    rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i x ∂potentialMeasure d.potential) = _ at he
  have hi (i : Fin n) : Integrable (fun x =>
      canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
        rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i x)
      (potentialMeasure d.potential) :=
    (Lp.memLp _).integrable_mul ((pullbackTest d f hf).metric_gradient i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)] at he
  have hp : (∫ x, ∑ i, canonicalMetricGradient d.potential i (sourceMetricInverseH1 d g) x *
      rawCanonicalMetricDerivative d.potential (pullbackRawGradient d f) i x ∂potentialMeasure d.potential) =
      ∫ x, ∑ i, naturalCanonicalRawGradient d g i x * gradient f (gradient d.potential x) i
        ∂potentialMeasure d.potential := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (pullback_raw_metric_gradient_ae d f)] with x hx
    simp only [hx, naturalCanonicalRawGradient, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hS : (canonicalMetricUnroot d.potential x).IsSymm := inverseSqrtMatrix_isSymm _ |>.inv
    rw [hS.apply i j]
    ring
  rw [hp] at he
  exact he

end KLSConstantImprovement.ActualGlobalRawFormTest405
#print axioms KLSConstantImprovement.ActualGlobalRawFormTest405.exists_boundedRawTest_form
#print axioms KLSConstantImprovement.ActualGlobalRawFormTest405.actual_variational_bounded_raw_test
#print axioms KLSConstantImprovement.ActualGlobalRawFormTest405.pullbackTest
#print axioms KLSConstantImprovement.ActualGlobalRawFormTest405.actual_target_pullback_variational
