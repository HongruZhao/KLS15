import KLSConstantImprovement.ActualBoundedCanonicalSource

/-! The existing actual bounded-source constructor with its supplied target
potential and convexity constant retained in the conclusion. This is needed
for a uniform C1,1 exhaustion bound; an arbitrary existential density witness
does not expose a uniform numerical convexity constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology NNReal ContDiff
namespace KLSConstantImprovement.ActualFixedTargetSource405
open KLS ActualBoundedCanonicalSource
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem exists_sourceData_fixed_target (hμ : admissibleMeasure μ)
    (K : Set (Space n)) (V : Space n → ℝ) (κ : ℝ)
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKb : Bornology.IsBounded K)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hκ : 0 < κ) (hs : StrongConvexOn univ κ V)
    (htarget : μ = (potentialMeasure V).restrict K) :
    ∃ d : SourceData μ, d.targetPotential = V ∧ d.targetSet = closure K ∧
      d.targetConvexityConstant = κ := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨R, hR, hbound⟩ := hKb.exists_pos_norm_le
  let L : ℝ≥0 := ⟨R, hR.le⟩
  have hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ L := by
    rw [htarget]
    exact (ae_restrict_mem hKo.measurableSet).mono fun y hy => hbound y hy
  obtain ⟨u, hLip, hc, hprob, hmap⟩ := hμ.isotropic.exists_bounded_momentMap L hbounded
  letI : IsProbabilityMeasure (potentialMeasure u) := hprob
  have hpush : MomentMap.gradientPushforward u = μ := hmap
  have hclosedTarget : μ = (potentialMeasure V).restrict (closure K) :=
    htarget.trans (potentialMeasure_restrict_closure_of_convex V hKc).symm
  have htransport := hpush.trans hclosedTarget
  have hVc : ConvexOn ℝ univ V := convexOn_of_strongConvexOn_nonneg hκ.le hs
  rw [strongConvexOn_iff_convex] at hs
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by simp)
  have hgrad := weak_moment_gradient_lipschitz_of_uniformlyConvex_target
    hLip hc hV1 hVc hκ hs isClosed_closure hKc.closure htransport
  obtain ⟨N, hNl, hNw⟩ := weak_moment_exists_third_tensor
    hLip hc hV1 hVc hκ hs isClosed_closure hKc.closure htransport
  let d : SourceData μ := {
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
    target_strong := hs
    target_representation := hclosedTarget
    source_lipschitz := hLip
    source_convex := hc
    source_probability := hprob
    pushforward := hpush
    source_C1 := moment_contDiff_one_closedTarget hLip hc hV.continuous
      isClosed_closure hKc.closure htransport
    gradient_lipschitz := hgrad
    hessian_ae := weak_moment_ae_hessian_equation_of_uniformlyConvex_target
      hLip hc hV1 hVc hκ hs isClosed_closure hKc.closure htransport
    third := N
    third_local_L2 := hNl
    third_weak_derivative := hNw
    third_symmetric_ae := actual_weak_third_tensor_ae_symmetric
      hLip.locallyLipschitz hgrad.locallyLipschitz hNl hNw }
  exact ⟨d, rfl, rfl, rfl⟩

end KLSConstantImprovement.ActualFixedTargetSource405
#print axioms KLSConstantImprovement.ActualFixedTargetSource405.exists_sourceData_fixed_target
