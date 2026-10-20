import KLSConstantImprovement.PostAffineWeightedGapTwoObstruction

/-! Actual even quartic source rejects universal H-specific post-affine gap2.
The source/target realization, Gaussian expansion and joint-cutoff limits
are paper proofs; finite coefficients and strict consequences are formal.
No active response or original CP theorem uses the rejected higher gap. -/
namespace KLSConstantImprovement.RegressedHessianGapTwoObstruction

theorem quartic_target_convexity_numerator {eps z : ℝ}
    (he : 0 ≤ eps) (he18 : eps ≤ (1/18:ℝ)) (hz : 0 ≤ z) :
    0 < 1+3*z+3*z^2+9*z^3+6*eps-54*eps*z := by
  have hfactor : 0 ≤ 1-18*eps := by linarith
  have hp : 0 ≤ 3*z*(1-18*eps) :=
    mul_nonneg (mul_nonneg (by norm_num) hz) hfactor
  have hz2 : 0 ≤ z^2 := sq_nonneg z
  have hz3 : 0 ≤ z^3 := pow_nonneg hz 3
  nlinarith

theorem gaussian_regressed_hessian_cubic_coefficient :
    -(324:ℝ)-108+2*216-4*3*9 = -108 := by
  norm_num

theorem negative_hessian_gap_from_joint_cutoff
    {eps c2 c3 remainder normalized gap : ℝ}
    (he : 0 < eps) (hc2 : c2 ≤ 18*eps) (hc3 : c3 ≤ -90)
    (hrem : remainder ≤ 18*eps)
    (hn : normalized ≤ c2+eps*c3+remainder)
    (hgap : gap=eps^2*normalized) : gap < 0 := by
  have hb := mul_le_mul_of_nonneg_left hc3 (le_of_lt he)
  have hnneg : normalized < 0 := by nlinarith
  rw [hgap]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos he) hnneg

theorem positive_whitening_preserves_hessian_gap {gap sigma : ℝ}
    (hg : gap < 0) (hs : 0 < sigma) : gap/sigma^4 < 0 := by
  exact div_neg_of_neg_of_pos hg (pow_pos hs 4)

end KLSConstantImprovement.RegressedHessianGapTwoObstruction
#print axioms KLSConstantImprovement.RegressedHessianGapTwoObstruction.quartic_target_convexity_numerator
#print axioms KLSConstantImprovement.RegressedHessianGapTwoObstruction.gaussian_regressed_hessian_cubic_coefficient
#print axioms KLSConstantImprovement.RegressedHessianGapTwoObstruction.negative_hessian_gap_from_joint_cutoff
#print axioms KLSConstantImprovement.RegressedHessianGapTwoObstruction.positive_whitening_preserves_hessian_gap
