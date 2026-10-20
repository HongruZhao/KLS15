import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.MomentGradientRange
import KLS.MomentMapFiniteDifference

/-! A C1 convex probability moment source with the actual original bounded
target inherits global Lipschitzness and the entire genuine weak SourceData
package.  Its given potential is retained exactly; no source uniqueness or
classical smooth upgrade is used. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualC11MomentSourceRealization405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem moment_gradient_range_subset (d : SourceData μ)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hpush : (potentialMeasure φ).map (gradient φ) = μ) :
    range (gradient φ) ⊆ d.targetSet := by
  let S : Set (Space n) := d.targetSet
  change range (gradient φ) ⊆ S
  have htarget : ∀ᵐ y ∂μ, y ∈ S := by
    rw [d.target_representation]
    exact ae_restrict_mem d.target_closed.measurableSet
  rw [← hpush] at htarget
  have hsource : ∀ᵐ x ∂potentialMeasure φ, gradient φ x ∈ S :=
    ae_of_ae_map (measurable_gradient _).aemeasurable htarget
  have hac : (volume : Measure (Space n)) ≪ potentialMeasure φ :=
    volume_absolutelyContinuous_potentialMeasure_of_measurable hφ.continuous.measurable
  have hdense : Dense ((gradient φ) ⁻¹' d.targetSet) :=
    Measure.dense_of_ae (hsource.filter_mono hac.ae_le)
  have hclosed : IsClosed ((gradient φ) ⁻¹' d.targetSet) :=
    d.target_closed.preimage (continuous_gradient_of_contDiff hφ)
  rintro _ ⟨x, rfl⟩
  exact hclosed.closure_subset (hdense x)

theorem exists_moment_source_lipschitz (d : SourceData μ)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hpush : (potentialMeasure φ).map (gradient φ) = μ) :
    ∃ L : ℝ≥0, LipschitzWith L φ :=
  lipschitzWith_of_bounded_gradient (hφ.differentiable (by norm_num))
    (d.target_bounded.subset (moment_gradient_range_subset d hφ hpush))

def realizeC11MomentSource (d : SourceData μ) (φ : Space n → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    (hprob : IsProbabilityMeasure (potentialMeasure φ))
    (hpush : (potentialMeasure φ).map (gradient φ) = μ) : SourceData μ := by
  letI : IsProbabilityMeasure (potentialMeasure φ) := hprob
  let L := Classical.choose (exists_moment_source_lipschitz d hφ hpush)
  have hLip := Classical.choose_spec (exists_moment_source_lipschitz d hφ hpush)
  have htransport : MomentMap.gradientPushforward φ =
      (potentialMeasure d.targetPotential).restrict d.targetSet :=
    hpush.trans d.target_representation
  have hV1 : ContDiff ℝ 1 d.targetPotential := d.target_smooth.of_le (by simp)
  have hg := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV1 d.target_convex_potential d.target_convexity_pos d.target_strong
      d.target_closed d.target_convex htransport
  let hex := weak_moment_exists_third_tensor
    hLip hc hV1 d.target_convex_potential d.target_convexity_pos d.target_strong
      d.target_closed d.target_convex htransport
  let N := Classical.choose hex
  have hNl := (Classical.choose_spec hex).1
  have hNw := (Classical.choose_spec hex).2
  exact {
    potential := φ
    targetPotential := d.targetPotential
    targetSet := d.targetSet
    sourceLipschitzConstant := L
    targetConvexityConstant := d.targetConvexityConstant
    target_closed := d.target_closed
    target_convex := d.target_convex
    target_bounded := d.target_bounded
    target_smooth := d.target_smooth
    target_convexity_pos := d.target_convexity_pos
    target_convex_potential := d.target_convex_potential
    target_strong := d.target_strong
    target_representation := d.target_representation
    source_lipschitz := hLip
    source_convex := hc
    source_probability := hprob
    pushforward := hpush
    source_C1 := hφ
    gradient_lipschitz := hg
    hessian_ae := weak_moment_ae_hessian_equation_of_uniformlyConvex_target
      hLip hc hV1 d.target_convex_potential d.target_convexity_pos d.target_strong
        d.target_closed d.target_convex htransport
    third := N
    third_local_L2 := hNl
    third_weak_derivative := hNw
    third_symmetric_ae := actual_weak_third_tensor_ae_symmetric
      hLip.locallyLipschitz hg.locallyLipschitz hNl hNw }

theorem realizeC11MomentSource_potential (d : SourceData μ) (φ : Space n → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    (hprob : IsProbabilityMeasure (potentialMeasure φ))
    (hpush : (potentialMeasure φ).map (gradient φ) = μ) :
    (realizeC11MomentSource d φ hφ hc hprob hpush).potential = φ := rfl

theorem realizeC11MomentSource_target (d : SourceData μ) (φ : Space n → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : ConvexOn ℝ univ φ)
    (hprob : IsProbabilityMeasure (potentialMeasure φ))
    (hpush : (potentialMeasure φ).map (gradient φ) = μ) :
    (realizeC11MomentSource d φ hφ hc hprob hpush).targetPotential = d.targetPotential ∧
    (realizeC11MomentSource d φ hφ hc hprob hpush).targetSet = d.targetSet ∧
    (realizeC11MomentSource d φ hφ hc hprob hpush).targetConvexityConstant = d.targetConvexityConstant :=
  ⟨rfl, rfl, rfl⟩

end KLSConstantImprovement.ActualC11MomentSourceRealization405
#print axioms KLSConstantImprovement.ActualC11MomentSourceRealization405.moment_gradient_range_subset
#print axioms KLSConstantImprovement.ActualC11MomentSourceRealization405.exists_moment_source_lipschitz
#print axioms KLSConstantImprovement.ActualC11MomentSourceRealization405.realizeC11MomentSource_potential
#print axioms KLSConstantImprovement.ActualC11MomentSourceRealization405.realizeC11MomentSource_target
