import KLSConstantImprovement.ActualTargetInteriorPullbackSupport405
import KLSConstantImprovement.ActualGlobalRawFormTest405

/-! Actual target pullback cutoffs have genuine weak gradients and an a.e.
pointwise metric-energy bound from target Lipschitz continuity. Compact
source support uses the true interior condition proved separately. -/
noncomputable section
open MeasureTheory Set Filter Matrix InnerProductSpace
open scoped BigOperators Topology ContDiff NNReal ENNReal
namespace KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405
open KLS ActualBoundedCanonicalSource ActualSourcePullbackMetricGradient405
open ActualWeakCanonicalMetricOrdinaryGraph ActualCompactRawMetricGraph
open ActualGlobalRawFormTest405 ActualTargetInteriorPullbackSupport405
variable {n : ℕ} {μ : Measure (Space n)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def pullbackMetricSquare (d : SourceData μ) (χ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑ i : Fin n, rawCanonicalMetricDerivative d.potential (pullbackRawGradient d χ) i x ^ 2

theorem pullbackMetricSquare_ae (d : SourceData μ) (χ : Space n → ℝ) :
    pullbackMetricSquare d χ =ᵐ[potentialMeasure d.potential] fun x =>
      inner ℝ (gradient χ (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (gradient χ (gradient d.potential x))) := by
  filter_upwards [d.hessian_ae_source, ae_all_iff.mpr (pullback_raw_metric_gradient_ae d χ)] with x hp hx
  let S := canonicalMetricUnroot d.potential x
  let v : Fin n → ℝ := fun a => gradient χ (gradient d.potential x) a
  have he : (S *ᵥ v) ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (coordinateHessian d.potential x *ᵥ v) := by
    rw [← Matrix.dotProduct_transpose_mulVec S v (S *ᵥ v), Matrix.mulVec_mulVec,
      canonicalMetricUnroot_gram_at hp.1]
  calc
    _ = (S *ᵥ v) ⬝ᵥ (S *ᵥ v) := by
      simp only [pullbackMetricSquare, hx, S, v, dotProduct, Matrix.mulVec, pow_two]
    _ = _ := he
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, matrixAction_apply, v]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem pullbackMetricSquare_bound_ae (d : SourceData μ)
    {χ : Space n → ℝ} {L : NNReal} (hLip : LipschitzWith L χ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      pullbackMetricSquare d χ x ≤ (16 / d.targetConvexityConstant) * (L : ℝ) ^ 2 := by
  have hac : potentialMeasure d.potential ≪ (volume : Measure (Space n)) :=
    withDensity_absolutelyContinuous _ _
  filter_upwards [pullbackMetricSquare_ae d χ, d.hessian_operator_bound_ae.filter_mono hac.ae_le]
    with x hx hH
  rw [hx]
  let v := gradient χ (gradient d.potential x)
  have hg : ‖v‖ ≤ (L : ℝ) := norm_gradient_le_of_lipschitz hLip _
  have hsq : ‖v‖ ^ 2 ≤ (L : ℝ) ^ 2 := (sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr hg
  calc
    _ ≤ ‖v‖ * ‖matrixAction (coordinateHessian d.potential x) v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * ((16 / d.targetConvexityConstant) * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hH (norm_nonneg v))) (norm_nonneg v)
    _ = (16 / d.targetConvexityConstant) * ‖v‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by have hκ := d.target_convexity_pos; positivity)

theorem actual_target_cutoff_domains (d : SourceData μ) (hμ : admissibleMeasure μ)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ interior d.targetSet) {L : NNReal} (hLip : LipschitzWith L χ) :
    HasCompactSupport (fun x => χ (gradient d.potential x)) ∧
      LocallyLipschitz (fun x => χ (gradient d.potential x)) ∧
      (∀ i, HasLocalWeakCoordinateDerivative (fun x => χ (gradient d.potential x))
        (pullbackRawGradient d χ i) i) ∧
      (∀ i E, IsCompact E → MemLp (pullbackRawGradient d χ i) 2 (volume.restrict E)) ∧
      ∀ᵐ x ∂potentialMeasure d.potential,
        pullbackMetricSquare d χ x ≤ (16 / d.targetConvexityConstant) * (L : ℝ) ^ 2 := by
  refine ⟨actual_target_pullback_compact d hμ hc hsub,
    (hLip.comp d.gradient_lipschitz).locallyLipschitz,
    d.pullback_hasLocalWeakCoordinateDerivative hχ, ?_, pullbackMetricSquare_bound_ae d hLip⟩
  intro i E hE
  exact KLS.MemLp.restrict_volume_of_potentialMeasure (d.pullback_weak_derivative_memLp hχ i 2)
    d.source_C1.continuous hE

end KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405
#print axioms KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405.pullbackMetricSquare_ae
#print axioms KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405.pullbackMetricSquare_bound_ae
#print axioms KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405.actual_target_cutoff_domains
