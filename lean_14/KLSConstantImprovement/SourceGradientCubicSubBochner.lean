import KLSConstantImprovement.SourceGradientCubicCombinedEnergy

/-! The actual natural inverse currently supplies the sub-Bochner bound
`‖r‖² + curvature ≤ V`. Equality is unnecessary for the combined energy
route. The source pairing and numerical residual are still separate inputs.
-/
noncomputable section
namespace KLSConstantImprovement.SourceGradientCubicSubBochner
open SourceGradientCubicCombinedEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_gradient_variance_upper (b r : E)
    {V response curvature : ℝ}
    (hpair : V = 3 * inner ℝ r b + 3 * response)
    (hbochner : ‖r‖ ^ 2 + curvature ≤ V) :
    V - 9 * ‖b‖ ^ 2 ≤
      6 * response - ‖r - (3 : ℝ) • b‖ ^ 2 - curvature := by
  have h := source_gradient_objective b r (curvature := curvature) hpair
  linarith

theorem residual_ninety_gives_cubic336 (b r : E)
    {V response curvature N : ℝ}
    (hN : 0 ≤ N)
    (hpair : V = 3 * inner ℝ r b + 3 * response)
    (hbochner : ‖r‖ ^ 2 + curvature ≤ V)
    (hmain : ‖b‖ ^ 2 ≤ (16 + 8 * Real.sqrt 2) * N)
    (hresidual :
      6 * response - ‖r - (3 : ℝ) • b‖ ^ 2 - curvature ≤ 90 * N) :
    V ≤ 336 * N := by
  have h := source_gradient_variance_upper b r hpair hbochner
  exact KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
    hN hmain (h.trans hresidual)

end KLSConstantImprovement.SourceGradientCubicSubBochner
#print axioms KLSConstantImprovement.SourceGradientCubicSubBochner.source_gradient_variance_upper
#print axioms KLSConstantImprovement.SourceGradientCubicSubBochner.residual_ninety_gives_cubic336
