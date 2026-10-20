import KLSConstantImprovement.ActualBoundedCanonicalSource
import KLS.MomentGradientHomeomorph
import KLS.MomentLegendreDomainSupport
import KLS.LogConcavitySupport
import KLS.LogConcavityAbsoluteContinuity

/-! Compact target tests lying strictly inside the actual target pull back
to compact source tests. The true finite-conjugate interior is identified
before the gradient homeomorphism is used. No properness at the bounded
target boundary is asserted. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace KLSConstantImprovement.ActualTargetInteriorPullbackSupport405
open KLS ActualBoundedCanonicalSource
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem actual_target_interior_subset_legendre_interior (d : SourceData μ)
    (hμ : admissibleMeasure μ) :
    interior d.targetSet ⊆ interior (momentLegendreDomain d.potential) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hV (y : Space n) : y ∈ (potentialMeasure d.targetPotential).support := by
    apply (volume_absolutelyContinuous_potentialMeasure_of_measurable
      d.target_smooth.continuous.measurable).support_mono
    simp only [Measure.support_eq_univ, mem_univ]
  have ht : interior d.targetSet ⊆ μ.support := by
    intro y hy
    have he : μ.support = ((potentialMeasure d.targetPotential).restrict d.targetSet).support :=
      congrArg Measure.support d.target_representation
    rw [he]
    exact Measure.interior_inter_support ⟨hy, hV y⟩
  have hti : interior d.targetSet ⊆ interior μ.support :=
    interior_maximal ht isOpen_interior
  have he := (interior_momentLegendreDomain_eq_interior_support d.source_lipschitz
    d.source_convex d.pushforward hμ.absolutelyContinuousLebesgue hμ.logConcave.convex_support).2
  simpa only [he] using hti

theorem actual_gradient_preimage_compact_interior (d : SourceData μ)
    {C : Set (Space n)} (hC : IsCompact C)
    (hsub : C ⊆ interior (momentLegendreDomain d.potential)) :
    IsCompact ((gradient d.potential) ⁻¹' C) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hinv : ContinuousOn (gradient (finiteLegendrePotential d.potential)) C :=
    (continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn d.source_lipschitz.continuous
      (moment_strictConvexOn d.source_lipschitz d.source_convex d.target_smooth.continuous
        d.target_closed.measurableSet d.target_convex
        (d.pushforward.trans d.target_representation))).mono hsub
  have heq : (gradient d.potential) ⁻¹' C =
      (gradient (finiteLegendrePotential d.potential)) '' C := by
    ext x
    constructor
    · intro hx
      refine ⟨gradient d.potential x, hx, ?_⟩
      exact moment_gradient_finiteLegendrePotential_gradient d.source_lipschitz d.source_convex
        d.target_smooth.continuous d.target_closed d.target_convex
        (d.pushforward.trans d.target_representation) x
    · rintro ⟨p, hp, rfl⟩
      have he := moment_gradient_gradient_finiteLegendrePotential d.source_lipschitz d.source_convex
        d.target_smooth.continuous d.target_closed d.target_convex
        (d.pushforward.trans d.target_representation) (hsub hp)
      simpa only [mem_preimage, he] using hp
  rw [heq]
  exact hC.image_of_continuousOn hinv

theorem actual_target_pullback_compact (d : SourceData μ) (hμ : admissibleMeasure μ)
    {χ : Space n → ℝ} (hc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ interior d.targetSet) :
    HasCompactSupport (fun x => χ (gradient d.potential x)) := by
  have hs := hsub.trans (actual_target_interior_subset_legendre_interior d hμ)
  have hp := actual_gradient_preimage_compact_interior d hc hs
  apply hp.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hc.isClosed.preimage d.gradient_lipschitz.continuous)
  intro x hx
  exact subset_tsupport χ hx

end KLSConstantImprovement.ActualTargetInteriorPullbackSupport405
#print axioms KLSConstantImprovement.ActualTargetInteriorPullbackSupport405.actual_target_interior_subset_legendre_interior
#print axioms KLSConstantImprovement.ActualTargetInteriorPullbackSupport405.actual_gradient_preimage_compact_interior
#print axioms KLSConstantImprovement.ActualTargetInteriorPullbackSupport405.actual_target_pullback_compact
