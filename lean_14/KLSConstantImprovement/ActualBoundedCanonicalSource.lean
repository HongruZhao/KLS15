import KLS.StrongDensityWeakMomentQuadratic
import KLS.WeakMomentAeEllipticity
import KLS.WeakMomentLocalStrongConvexity
import KLS.WeakMomentExistsTraceEnergy
import KLS.WeakHessianTensorSymmetry

/-!
Actual canonical-source construction for the bounded strongly convex target
class. Every datum below is constructed from admissibility and the stated
target density. This is a C1,1 / weak-third-derivative package: it does not
claim classical C2, C4, or a smooth diffeomorphism.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ContDiff Topology NNReal ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualBoundedCanonicalSource
open KLS
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {n : ℕ}

/-- Genuine canonical source and its actual weak geometric derivatives.
The matrix norm in `hessian_ae` is the entrywise norm, while the gradient
Lipschitz property separately controls the operator norm. -/
structure SourceData (μ : Measure (Space n)) where
  potential : Space n → ℝ
  targetPotential : Space n → ℝ
  targetSet : Set (Space n)
  sourceLipschitzConstant : ℝ≥0
  targetConvexityConstant : ℝ
  target_closed : IsClosed targetSet
  target_convex : Convex ℝ targetSet
  target_bounded : Bornology.IsBounded targetSet
  target_smooth : ContDiff ℝ (⊤ : ℕ∞) targetPotential
  target_convexity_pos : 0 < targetConvexityConstant
  target_convex_potential : ConvexOn ℝ univ targetPotential
  target_strong : ConvexOn ℝ univ (fun p =>
    targetPotential p - (targetConvexityConstant / 2) * ‖p‖ ^ 2)
  target_representation : μ = (potentialMeasure targetPotential).restrict targetSet
  source_lipschitz : LipschitzWith sourceLipschitzConstant potential
  source_convex : ConvexOn ℝ univ potential
  source_probability : IsProbabilityMeasure (potentialMeasure potential)
  pushforward : MomentMap.gradientPushforward potential = μ
  source_C1 : ContDiff ℝ 1 potential
  gradient_lipschitz : LipschitzWith
    (⟨16 / targetConvexityConstant, by positivity⟩ : ℝ≥0) (gradient potential)
  hessian_ae : ∀ᵐ x ∂(volume : Measure (Space n)),
    (coordinateHessian potential x).PosDef ∧
    (coordinateHessian potential x).det =
      Real.exp (-potential x + targetPotential (gradient potential x)) ∧
    HasFDerivAt (gradient potential) (matrixAction (coordinateHessian potential x)) x ∧
    ‖coordinateHessian potential x‖ ≤ 16 / targetConvexityConstant
  third : Space n → Fin n → Fin n → Fin n → ℝ
  third_local_L2 : ∀ k i j E, IsCompact E →
    MemLp (fun x => third x k i j) 2 (volume.restrict E)
  third_weak_derivative : ∀ k i j, HasLocalWeakCoordinateDerivative
    (fun x => coordinateHessian potential x i j) (fun x => third x k i j) k
  third_symmetric_ae : ∀ᵐ x ∂(volume : Measure (Space n)),
    ∀ k i j, third x k i j = third x i k j ∧ third x k i j = third x k j i

/-- Bounded strongly convex target laws actually possess all the weak source
data in `SourceData`; no source-existence or source-regularity premise occurs. -/
theorem exists_sourceData {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    (hreg : HasSmoothBoundedStronglyConvexDensity μ) : Nonempty (SourceData μ) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨K, V, κ, hKo, hKc, hKb, _, hV, hκ, hstrong, htarget⟩ := hreg
  obtain ⟨R, hR, hbound⟩ := hKb.exists_pos_norm_le
  let L : ℝ≥0 := ⟨R, hR.le⟩
  have hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ L := by
    rw [htarget]
    exact (ae_restrict_mem hKo.measurableSet).mono fun y hy => hbound y hy
  obtain ⟨u, hLip, hc, hprob, hmap⟩ :=
    hμ.isotropic.exists_bounded_momentMap L hbounded
  letI : IsProbabilityMeasure (potentialMeasure u) := hprob
  have hpush : MomentMap.gradientPushforward u = μ := hmap
  have hclosedTarget : μ = (potentialMeasure V).restrict (closure K) :=
    htarget.trans (potentialMeasure_restrict_closure_of_convex V hKc).symm
  have htransport := hpush.trans hclosedTarget
  have hVc : ConvexOn ℝ univ V :=
    convexOn_of_strongConvexOn_nonneg hκ.le hstrong
  rw [strongConvexOn_iff_convex] at hstrong
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by simp)
  have hgrad := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV1 hVc hκ hstrong isClosed_closure hKc.closure htransport
  obtain ⟨N, hNl, hNw⟩ := weak_moment_exists_third_tensor
    hLip hc hV1 hVc hκ hstrong isClosed_closure hKc.closure htransport
  exact ⟨{
    potential := u
    targetPotential := V
    targetSet := closure K
    sourceLipschitzConstant := L
    targetConvexityConstant := κ
    target_closed := isClosed_closure
    target_convex := hKc.closure
    target_bounded := hKb.isCompact_closure.isBounded
    target_smooth := hV
    target_convexity_pos := hκ
    target_convex_potential := hVc
    target_strong := hstrong
    target_representation := hclosedTarget
    source_lipschitz := hLip
    source_convex := hc
    source_probability := hprob
    pushforward := hpush
    source_C1 := moment_contDiff_one_closedTarget hLip hc hV.continuous
      isClosed_closure hKc.closure htransport
    gradient_lipschitz := hgrad
    hessian_ae := weak_moment_ae_hessian_equation_of_uniformlyConvex_target
      hLip hc hV1 hVc hκ hstrong isClosed_closure hKc.closure htransport
    third := N
    third_local_L2 := hNl
    third_weak_derivative := hNw
    third_symmetric_ae := actual_weak_third_tensor_ae_symmetric
      hLip.locallyLipschitz hgrad.locallyLipschitz hNl hNw }⟩

/-- The AE geometry holds in the actual normalized source law as well. -/
theorem SourceData.hessian_ae_source {μ : Measure (Space n)} (d : SourceData μ) :
    ∀ᵐ x ∂potentialMeasure d.potential,
      (coordinateHessian d.potential x).PosDef ∧
      (coordinateHessian d.potential x).det =
        Real.exp (-d.potential x + d.targetPotential (gradient d.potential x)) ∧
      HasFDerivAt (gradient d.potential)
        (matrixAction (coordinateHessian d.potential x)) x ∧
      ‖coordinateHessian d.potential x‖ ≤ 16 / d.targetConvexityConstant := by
  have hac : potentialMeasure d.potential ≪ volume := withDensity_absolutelyContinuous _ _
  exact d.hessian_ae.filter_mono hac.ae_le

/-- The actual derivative, not the entrywise matrix norm, gives the uniform
operator bound at almost every source point. -/
theorem SourceData.hessian_operator_bound_ae {μ : Measure (Space n)} (d : SourceData μ) :
    ∀ᵐ x ∂(volume : Measure (Space n)),
      ‖matrixAction (coordinateHessian d.potential x)‖ ≤ 16 / d.targetConvexityConstant := by
  filter_upwards [d.hessian_ae] with x hx
  rw [← hx.2.2.1.fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ d.gradient_lipschitz

/-- Local positive lower Hessian bounds are actual consequences of the
canonical transport and its positive continuous density. No uniform global
lower Hessian bound is asserted. -/
theorem SourceData.locally_strongly_convex {μ : Measure (Space n)} (d : SourceData μ)
    {E : Set (Space n)} (hE : IsCompact E) (hEc : Convex ℝ E) :
    ∃ c : ℝ, 0 < c ∧ StrongConvexOn E c d.potential := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  exact weak_moment_strongConvexOn_compact d.source_lipschitz d.source_convex
    (d.target_smooth.of_le (by simp)) d.target_convex_potential
    d.target_convexity_pos d.target_strong d.target_closed d.target_convex
    (d.pushforward.trans d.target_representation) hE hEc

/-- The source gradient is globally bounded because the actual source
potential is Lipschitz; the bound is allowed to depend on the target set. -/
theorem SourceData.gradient_range_bounded {μ : Measure (Space n)} (d : SourceData μ) :
    Bornology.IsBounded (range (gradient d.potential)) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨d.sourceLipschitzConstant, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_gradient_le_of_lipschitz d.source_lipschitz x

end KLSConstantImprovement.ActualBoundedCanonicalSource
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.exists_sourceData
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_ae_source
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.hessian_operator_bound_ae
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.locally_strongly_convex
#print axioms KLSConstantImprovement.ActualBoundedCanonicalSource.SourceData.gradient_range_bounded
