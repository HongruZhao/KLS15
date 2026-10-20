import KLSConstantImprovement.ActualSourceHessianEvolution405

/-! The actual source Hessian equation accepts genuine bounded compact raw
H1 tests. The supplied F is the test's weak derivative, and the source's
third tensor and weak Monge--Ampere equation are constructed data. This
allows bounded truncations of natural vector products without assuming
classical differentiability of the source Hessian or of the test. -/
noncomputable section
open MeasureTheory Matrix Set Filter
open scoped BigOperators ContDiff ENNReal
namespace KLSConstantImprovement.ActualSourceRawHessianEvolution405
open KLS ActualBoundedCanonicalSource ActualSourceHessianEvolution405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_compact_raw_hessian_evolution (d : SourceData μ)
    {f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hf : ∀ E, IsCompact E → MemLp f 2 (volume.restrict E))
    (hc : HasCompactSupport f) {B : ℝ} (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ B)
    (hF : ∀ a E, IsCompact E → MemLp (F a) 2 (volume.restrict E))
    (hW : ∀ a, HasLocalWeakCoordinateDerivative f (F a) a) (i j : Fin n) :
    (∀ a, Integrable (fun x => ((coordinateHessian d.potential x)⁻¹ *
      sourceThirdMatrix d x i) a j * F a x) (potentialMeasure d.potential)) ∧
    Integrable (fun x => (-coordinateHessian d.potential x i j +
      sourceConnectionCurvature d x i j) * f x) (potentialMeasure d.potential) ∧
    -(∑ a, ∫ x, ((coordinateHessian d.potential x)⁻¹ * sourceThirdMatrix d x i) a j *
      F a x ∂potentialMeasure d.potential) =
      ∫ x, (-coordinateHessian d.potential x i j + sourceConnectionCurvature d x i j) *
        f x ∂potentialMeasure d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have he := weak_moment_hessian_evolution_bounded_H1
    d.source_lipschitz d.source_convex (d.target_smooth.of_le (by simp))
    d.target_convex_potential d.target_convexity_pos d.target_strong
    d.target_closed d.target_convex (d.pushforward.trans d.target_representation)
    (T := sourceThirdMatrix d) d.third_local_L2 d.third_weak_derivative
    hf hc hb hF hW i j
  simpa only [sourceConnectionCurvature, matrixTraceGram, Matrix.add_apply,
    add_assoc] using he

end KLSConstantImprovement.ActualSourceRawHessianEvolution405
#print axioms KLSConstantImprovement.ActualSourceRawHessianEvolution405.actual_compact_raw_hessian_evolution
