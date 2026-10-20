import KLSConstantImprovement.ActualCenteredSourceTransport405
import KLS.C11CenteredDifferenceCalculus

/-! A real canonical SourceData on exactly the centered probability source.
All weak geometric fields are rebuilt from its actual moment transport; no
operator or inverse domain is transported by an unproved identification. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Topology NNReal ContDiff ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualCenteredSourceData405
open KLS ActualBoundedCanonicalSource ActualSourceCentering405 ActualCenteredSourceTransport405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

def centeredCanonicalSource (d : SourceData μ) : SourceData μ := by
  let u := normalizedMomentPotential (centeredSourcePotential d)
  have hu : ∀ x, u x = d.potential (x + actualSourceMinimum d) :=
    centeredSourcePotential_normalized d
  have hLip : LipschitzWith d.sourceLipschitzConstant u := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hu x, hu y]
    simpa only [dist_add_right] using d.source_lipschitz.dist_le_mul
      (x + actualSourceMinimum d) (y + actualSourceMinimum d)
  have hc : ConvexOn ℝ univ u :=
    (centeredSourcePotential_convex d).add_const _
  have hC1 : ContDiff ℝ 1 u := (centeredSourcePotential_C1 d).add contDiff_const
  have hg : LipschitzWith
      (⟨16 / d.targetConvexityConstant, div_nonneg (by norm_num) d.target_convexity_pos.le⟩ : ℝ≥0) (gradient u) := by
    simpa only [u, gradient_normalizedMomentPotential] using centeredSourcePotential_gradient_lipschitz d
  letI : IsProbabilityMeasure (potentialMeasure u) :=
    isProbabilityMeasure_normalizedMomentPotential (centeredSourcePotential_exp_integrable d)
  have hpush : MomentMap.gradientPushforward u = μ := centeredSourcePotential_pushforward d
  have htransport := hpush.trans d.target_representation
  have hV1 : ContDiff ℝ 1 d.targetPotential := d.target_smooth.of_le (by simp)
  let hex := weak_moment_exists_third_tensor
    hLip hc hV1 d.target_convex_potential d.target_convexity_pos d.target_strong
      d.target_closed d.target_convex htransport
  let N := Classical.choose hex
  have hNl := (Classical.choose_spec hex).1
  have hNw := (Classical.choose_spec hex).2
  exact {
    potential := u
    targetPotential := d.targetPotential
    targetSet := d.targetSet
    sourceLipschitzConstant := d.sourceLipschitzConstant
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
    source_probability := inferInstance
    pushforward := hpush
    source_C1 := hC1
    gradient_lipschitz := hg
    hessian_ae := weak_moment_ae_hessian_equation_of_uniformlyConvex_target
      hLip hc hV1 d.target_convex_potential d.target_convexity_pos d.target_strong
        d.target_closed d.target_convex htransport
    third := N
    third_local_L2 := hNl
    third_weak_derivative := hNw
    third_symmetric_ae := actual_weak_third_tensor_ae_symmetric
      hLip.locallyLipschitz hg.locallyLipschitz hNl hNw }

theorem centeredCanonicalSource_potential (d : SourceData μ) :
    (centeredCanonicalSource d).potential = normalizedMomentPotential (centeredSourcePotential d) := rfl

theorem centeredCanonicalSource_target (d : SourceData μ) :
    (centeredCanonicalSource d).targetPotential = d.targetPotential ∧
      (centeredCanonicalSource d).targetSet = d.targetSet ∧
      (centeredCanonicalSource d).targetConvexityConstant = d.targetConvexityConstant :=
  ⟨rfl, rfl, rfl⟩

theorem centeredCanonicalSource_translate (d : SourceData μ) (x : Space n) :
    (centeredCanonicalSource d).potential x = d.potential (x + actualSourceMinimum d) :=
  centeredSourcePotential_normalized d x

theorem centeredCanonicalSource_gradient (d : SourceData μ) (x : Space n) :
    gradient (centeredCanonicalSource d).potential x = gradient d.potential (x + actualSourceMinimum d) := by
  rw [centeredCanonicalSource_potential, gradient_normalizedMomentPotential]
  exact gradient_normalizeAt d _ x

theorem centeredCanonicalSource_hessian (d : SourceData μ) (x : Space n) :
    coordinateHessian (centeredCanonicalSource d).potential x =
      coordinateHessian d.potential (x + actualSourceMinimum d) := by
  have hu : (centeredCanonicalSource d).potential =
      fun y => d.potential (y + actualSourceMinimum d) := funext (centeredCanonicalSource_translate d)
  rw [hu]
  ext i j
  have hd : coordinateDerivative (fun y => d.potential (y + actualSourceMinimum d)) j =
      fun y => coordinateDerivative d.potential j (y + actualSourceMinimum d) :=
    funext (coordinateDerivative_translate_total _ _ j)
  change coordinateDerivative (coordinateDerivative (fun y => d.potential (y + actualSourceMinimum d)) j) i x =
    coordinateDerivative (coordinateDerivative d.potential j) i (x + actualSourceMinimum d)
  rw [hd]
  exact coordinateDerivative_translate_total _ _ i x

theorem centeredCanonicalSource_gradient_zero (d : SourceData μ) :
    gradient (centeredCanonicalSource d).potential 0 = 0 := by
  rw [centeredCanonicalSource_potential, gradient_normalizedMomentPotential]
  exact centeredSourcePotential_gradient_zero d

end KLSConstantImprovement.ActualCenteredSourceData405
#print axioms KLSConstantImprovement.ActualCenteredSourceData405.centeredCanonicalSource_potential
#print axioms KLSConstantImprovement.ActualCenteredSourceData405.centeredCanonicalSource_target
#print axioms KLSConstantImprovement.ActualCenteredSourceData405.centeredCanonicalSource_gradient
#print axioms KLSConstantImprovement.ActualCenteredSourceData405.centeredCanonicalSource_hessian
#print axioms KLSConstantImprovement.ActualCenteredSourceData405.centeredCanonicalSource_gradient_zero
