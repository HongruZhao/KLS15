import KLSConstantImprovement.ActualCenteredForcingRhsLimit405
import KLSConstantImprovement.ActualSoftTargetSourceHessianLimit405

/-! The compact forcing RHS passage for the actual normalized, whitened
soft-target laws.  Target means are proved to converge by the established
bounded-continuous approximation, rather than supplied as a new limit. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff ENNReal
namespace KLSConstantImprovement.ActualSoftTargetForcingRhs405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualCenteredForcingRhsLimit405 ActualSoftTargetSourceLimit405
open ActualSoftTargetWhitening405 ActualInteriorCapConfinement405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem actual_softTarget_bounded_integral_tendsto
    (d₀ : SourceData μ) (hμ : admissibleMeasure μ)
    {idx : ℕ → ℕ} (hidx : StrictMono idx)
    {F : Space n → ℝ} (hF : Continuous F) {C : ℝ} (hb : ∀ y, ‖F y‖ ≤ C) :
    Tendsto (fun k => ∫ y, F y ∂whitenedSoftTargetMeasure d₀ (idx k)) atTop
      (𝓝 (∫ y, F y ∂μ)) := by
  have hne : d₀.targetSet.Nonempty := by
    obtain ⟨r, hr, hb⟩ := actual_target_contains_origin_ball d₀
    exact ⟨0, hb (mem_ball_self hr)⟩
  exact (tendsto_integral_bounded_whitened_softTarget hμ d₀.target_smooth
    d₀.target_convexity_pos (strongConvexOn_iff_convex.mpr d₀.target_strong)
    d₀.target_closed hne d₀.target_convex d₀.target_representation hF hb).comp hidx.tendsto_atTop

theorem actual_softTarget_centered_compact_rhs_tendsto
    (d₀ : SourceData μ) (hμ : admissibleMeasure μ)
    {idx : ℕ → ℕ} (hidx : StrictMono idx)
    (d : ∀ k, SourceData (whitenedSoftTargetMeasure d₀ (idx k))) (e : SourceData μ)
    (hg0 : ∀ k, gradient (d k).potential (0 : Space n) = 0)
    (hφ : ∀ x, Tendsto (fun k => (d k).potential x) atTop (𝓝 (e.potential x)))
    (hg : ∀ x, Tendsto (fun k => gradient (d k).potential x) atTop
      (𝓝 (gradient e.potential x)))
    {F : Space n → ℝ} (hF : Continuous F) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C)
    {ψ : Space n → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun k => ∫ x, centeredTargetDatum (d k) F hF x*ψ x
      ∂potentialMeasure (d k).potential) atTop
      (𝓝 (∫ x, centeredTargetDatum e F hF x*ψ x ∂potentialMeasure e.potential)) :=
  centeredTargetDatum_compact_rhs_tendsto d e hg0 hφ hg hF hC hb
    (actual_softTarget_bounded_integral_tendsto d₀ hμ hidx hF hb) hψ hcψ

end KLSConstantImprovement.ActualSoftTargetForcingRhs405
#print axioms KLSConstantImprovement.ActualSoftTargetForcingRhs405.actual_softTarget_bounded_integral_tendsto
#print axioms KLSConstantImprovement.ActualSoftTargetForcingRhs405.actual_softTarget_centered_compact_rhs_tendsto
