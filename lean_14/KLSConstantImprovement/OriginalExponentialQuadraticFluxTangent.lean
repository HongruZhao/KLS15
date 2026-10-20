import KLSConstantImprovement.SourceThirdAdjointResponse

/-! Exact kernels for the same original exponential density path and
standardized natural quadratic flux. Tail differentiation, source/kernel
identification and the two cutoff integrations are explicit analytic
inputs. This is a local norm tangent, not a finite perturbation bound. -/
noncomputable section
namespace KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent

theorem sandwich_tail_polynomial_identity (t : ℝ) :
    (-12*t^2-30*t)-2*(-4*t^3-15*t^2)+(-t^4-5*t^3) =
      -t^4+3*t^3+18*t^2-30*t := by ring

theorem flux_tail_polynomial_identity (t : ℝ) :
    (-10*t^3/3-13*t^2-32*t)-2*(-5*t^4/6-13*t^3/3-16*t^2)+
      (-t^5/6-13*t^4/12-16*t^3/3) =
      -t^5/6+7*t^4/12+19*t^2-32*t := by ring

theorem flux_minus_sandwich_kernel (t : ℝ) :
    (-t^5/6-13*t^4/12-16*t^3/3)-(-t^4-5*t^3) =
      -t^3*(2*t^2+t+4)/12 := by ring

theorem convex_flux_comparison_pointwise {t w2 : ℝ}
    (ht : 0 ≤ t) (hw : 0 ≤ w2) :
    -t^3*(2*t^2+t+4)*w2/12 ≤ 0 := by
  have ht3 : 0 ≤ t^3 := pow_nonneg ht _
  have hp : 0 ≤ 2*t^2+t+4 := by positivity
  have hmul := mul_nonneg (mul_nonneg ht3 hp) hw
  nlinarith

/-- The integrated curvature kernel is on the same original density path. -/
theorem convex_flux_slope_le_sandwich {fluxSlope sandwichSlope charge : ℝ}
    (hcharge : 0 ≤ charge)
    (hidentity : fluxSlope-sandwichSlope = -charge/12) :
    fluxSlope ≤ sandwichSlope := by linarith

theorem actual_shape_and_quadratic_score_calibrations :
    (-17/2 : ℝ)-(-7) = -3/2 ∧
    (-156 : ℝ)-(-108) = -48 := by norm_num

/-- An actual uniform-base convex tilt blocks global slope monotonicity.
It does not refute the strict norm comparison at that base. -/
theorem uniform_base_comparison_slope_guardrail :
    (4/525 : ℝ)-(-3/25) = 67/525 ∧ (0 : ℝ)<67/525 ∧
    (2/35 : ℝ)<54/35 := by norm_num

end KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.sandwich_tail_polynomial_identity
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.flux_tail_polynomial_identity
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.flux_minus_sandwich_kernel
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.convex_flux_comparison_pointwise
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.convex_flux_slope_le_sandwich
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.actual_shape_and_quadratic_score_calibrations
#print axioms KLSConstantImprovement.OriginalExponentialQuadraticFluxTangent.uniform_base_comparison_slope_guardrail
