import KLSConstantImprovement.HessianMomentScalar

/-! Exact same-field completion for the source-gradient cubic route.
Actual source IBP, target vector-Bochner similarity, and graph-domain
identifications remain analytic inputs in the signatures. The numerical
residual90 is an explicit hypothesis, not a proved universal estimate.
See literature/root-source-gradient-cubic-combined-energy-20261014.md. -/
noncomputable section
namespace KLSConstantImprovement.SourceGradientCubicCombinedEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_gradient_objective (b r : E)
    {functional response curvature : ℝ}
    (hpair : functional = 3 * inner ℝ r b + 3 * response) :
    2 * functional - ‖r‖^2 - curvature =
      9 * ‖b‖^2 + 6 * response - ‖r - (3:ℝ) • b‖^2 - curvature := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul]
  norm_num
  nlinarith

/-- The same source Hessian and target curvature give the variance identity.
No ordinary-target Hessian or curvature is substituted for these fields. -/
theorem source_gradient_variance (b r : E)
    {V response curvature : ℝ}
    (hpair : V = 3 * inner ℝ r b + 3 * response)
    (hbochner : V = ‖r‖^2 + curvature) :
    V - 9 * ‖b‖^2 =
      6 * response - ‖r - (3:ℝ) • b‖^2 - curvature := by
  have h := source_gradient_objective b r (curvature := curvature) hpair
  linarith

/-- All-law affine trace and numerical residual payments remain explicit. -/
theorem residual_ninety_gives_cubic336 (b r : E)
    {V response curvature N : ℝ}
    (hN : 0 ≤ N)
    (hpair : V = 3 * inner ℝ r b + 3 * response)
    (hbochner : V = ‖r‖^2 + curvature)
    (hmain : ‖b‖^2 ≤ (16 + 8 * Real.sqrt 2) * N)
    (hresidual : 6 * response - ‖r - (3:ℝ) • b‖^2 - curvature ≤ 90 * N) :
    V ≤ 336 * N := by
  have h := source_gradient_variance b r hpair hbochner
  exact KLSConstantImprovement.HessianMomentScalar.residual_ninety_gives_cubic336
    hN hmain (by linarith)

/-- Rational values from the explicit same-source exponential calculation. -/
theorem exponential_residual_calibration :
    (216:ℝ) - 9 * 14 = 108 - 18 ∧ (108:ℝ) - 18 = 90 := by
  norm_num

end KLSConstantImprovement.SourceGradientCubicCombinedEnergy
#print axioms KLSConstantImprovement.SourceGradientCubicCombinedEnergy.source_gradient_objective
#print axioms KLSConstantImprovement.SourceGradientCubicCombinedEnergy.source_gradient_variance
#print axioms KLSConstantImprovement.SourceGradientCubicCombinedEnergy.residual_ninety_gives_cubic336
#print axioms KLSConstantImprovement.SourceGradientCubicCombinedEnergy.exponential_residual_calibration
