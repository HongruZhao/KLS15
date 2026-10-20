import KLSConstantImprovement.ResponseCurvatureProductionBudget

/-! Finite certificates for the original exponential convex-tilt filtered
cross obstruction. Unique scalar kernels, weak shifted resolvent passage,
standardization and the smooth full-support witness are analytic bindings,
not supplied by these polynomial/scalar statements. -/
noncomputable section
namespace KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction

theorem exponential_quadratic_mode (t : ℝ) :
    -2*t+(t-1)*(2*t-4) = 2*(t^2-4*t+2) := by ring

theorem kernel_residual_variation (t : ℝ) :
    -t^2-2*t+4 = -(t^2-4*t+2)-6*(t-1) := by ring

theorem full_whitening_changes_only_affine_mode (t : ℝ) :
    (-t^2+t+1)-(-t^2-2*t+4) = 3*(t-1) := by ring

theorem quadratic_filtered_cross_derivative_negative
    {c : ℝ} (hNumerator : 9*c = -12) : c = -4/3 ∧ c < 0 := by
  constructor <;> linarith

theorem soft_barrier_uniform_convexity
    {epsilon sigma a : ℝ} (he : 0 < epsilon) (ha : 0 ≤ a)
    (hs0 : 0 ≤ sigma) (hs1 : sigma ≤ 1) :
    0 < epsilon+a*sigma*(1-sigma) := by
  have h := mul_nonneg (mul_nonneg ha hs0) (sub_nonneg.mpr hs1)
  linarith

end KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction
#print axioms KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction.exponential_quadratic_mode
#print axioms KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction.kernel_residual_variation
#print axioms KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction.full_whitening_changes_only_affine_mode
#print axioms KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction.quadratic_filtered_cross_derivative_negative
#print axioms KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction.soft_barrier_uniform_convexity
