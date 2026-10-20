import KLSConstantImprovement.ActualCompactTargetExtensions405
import KLSConstantImprovement.ActualTargetPullbackCutoffEnergy405
import KLS.LocalWeakAlgebra

/-! Fixed bounded C1 target extensions give actual centered forcing weak
derivatives and uniform metric-gradient square bounds on every approximant.
Centering changes only a constant.  The bound uses the common target
convexity modulus, not the growing target radius. -/
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology NNReal ContDiff ENNReal
namespace KLSConstantImprovement.ActualCenteredTargetForcing405
open KLS ActualBoundedCanonicalSource ActualCompactTargetExtensions405
open ActualSourcePullbackMetricGradient405 ActualTargetPullbackCutoffEnergy405
open ActualCompactRawMetricGraph
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ} {μ : Measure (Space n)}

theorem centeredTargetDatum_hasLocalWeakCoordinateDerivative
    (d : SourceData μ) {F : Space n → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin n) :
    HasLocalWeakCoordinateDerivative
      (centeredTargetDatum d F hF.continuous : Space n → ℝ)
      (pullbackRawGradient d F i) i := by
  let m : ℝ := ∫ y, F y ∂μ
  have hloc (E : Set (Space n)) (hE : IsCompact E) :
      MemLp (pullbackRawGradient d F i) 2 (volume.restrict E) :=
    KLS.MemLp.restrict_volume_of_potentialMeasure (d.pullback_weak_derivative_memLp hF i 2)
      d.source_C1.continuous hE
  have hw := (d.pullback_hasLocalWeakCoordinateDerivative hF i).add
    (hasLocalWeakCoordinateDerivative_const (-m) i)
    ((hF.continuous.comp d.gradient_lipschitz.continuous).locallyIntegrable)
    (continuous_const.locallyIntegrable)
    (locallyIntegrable_of_memLp_two_on_compacts hloc)
    (continuous_const.locallyIntegrable)
  have hraw : HasLocalWeakCoordinateDerivative
      (fun x => F (gradient d.potential x)-m) (pullbackRawGradient d F i) i := by
    change HasLocalWeakCoordinateDerivative
      (fun x => F (gradient d.potential x)-m)
      (fun x => inner ℝ (gradient F (gradient d.potential x))
        (matrixAction (coordinateHessian d.potential x) (EuclideanSpace.single i 1))) i
    simpa only [sub_eq_add_neg, add_zero] using hw
  have he : (centeredTargetDatum d F hF.continuous : Space n → ℝ) =ᵐ[volume]
      (fun x => F (gradient d.potential x)-m) :=
    (centeredTargetDatum_ae d F hF.continuous).filter_mono
      (volume_absolutelyContinuous_potentialMeasure d.source_C1.continuous).ae_le
  exact hraw.congr_ae he.symm EventuallyEq.rfl

theorem centeredTargetDatum_derivative_domains
    (d : SourceData μ) {F : Space n → ℝ} (hF : ContDiff ℝ 1 F) :
    (∀ i E, IsCompact E → MemLp (pullbackRawGradient d F i) 2 (volume.restrict E)) ∧
      (∀ i, MemLp
        (rawCanonicalMetricDerivative d.potential (pullbackRawGradient d F) i) ∞
        (potentialMeasure d.potential)) := by
  refine ⟨fun i E hE => ?_, fun i => pullback_raw_metric_gradient_memLp_top d hF i⟩
  exact KLS.MemLp.restrict_volume_of_potentialMeasure (d.pullback_weak_derivative_memLp hF i 2)
    d.source_C1.continuous hE

theorem centeredTargetDatum_metric_square_uniform
    (d : SourceData μ) {F : Space n → ℝ} (hF : ContDiff ℝ 1 F)
    {c G : ℝ} (hc : 0 < c) (hκ : c ≤ d.targetConvexityConstant)
    (hG : 0 ≤ G) (hbound : ∀ x, ‖gradient F x‖ ≤ G) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (∑ i : Fin n, rawCanonicalMetricDerivative d.potential (pullbackRawGradient d F) i x ^ 2)
        ≤ (16/c)*G^2 := by
  let L : ℝ≥0 := ⟨G, hG⟩
  have hLip : LipschitzWith L F := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by norm_num))
    intro x
    change ‖fderiv ℝ F x‖ ≤ G
    rw [← norm_gradient_eq_norm_fderiv]
    exact hbound x
  have hh : 16/d.targetConvexityConstant ≤ 16/c :=
    div_le_div_of_nonneg_left (by norm_num) hc hκ
  filter_upwards [pullbackMetricSquare_bound_ae d hLip] with x hx
  exact hx.trans (mul_le_mul_of_nonneg_right hh (sq_nonneg G))

theorem centeredTargetDatum_family_metric_square_uniform
    {ρ : ℕ → Measure (Space n)} (d : ∀ k, SourceData (ρ k))
    {F : Space n → ℝ} (hF : ContDiff ℝ 1 F)
    {c G : ℝ} (hc : 0 < c) (hκ : ∀ k, c ≤ (d k).targetConvexityConstant)
    (hG : 0 ≤ G) (hbound : ∀ x, ‖gradient F x‖ ≤ G) :
    ∀ k, ∀ᵐ x ∂potentialMeasure (d k).potential,
      (∑ i : Fin n,
        rawCanonicalMetricDerivative (d k).potential (pullbackRawGradient (d k) F) i x ^ 2)
        ≤ (16/c)*G^2 :=
  fun k => centeredTargetDatum_metric_square_uniform (d k) hF hc (hκ k) hG hbound

end KLSConstantImprovement.ActualCenteredTargetForcing405
#print axioms KLSConstantImprovement.ActualCenteredTargetForcing405.centeredTargetDatum_hasLocalWeakCoordinateDerivative
#print axioms KLSConstantImprovement.ActualCenteredTargetForcing405.centeredTargetDatum_derivative_domains
#print axioms KLSConstantImprovement.ActualCenteredTargetForcing405.centeredTargetDatum_metric_square_uniform
#print axioms KLSConstantImprovement.ActualCenteredTargetForcing405.centeredTargetDatum_family_metric_square_uniform
