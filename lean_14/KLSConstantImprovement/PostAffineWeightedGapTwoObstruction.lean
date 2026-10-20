import Mathlib

/-! Generic post-coordinate source gap2 is false on actual symmetric Laplace
and on suitable smooth uniformly convex regular approximations.
Actual Stein/polynomial/core bindings are paper inputs; H-specific gap2 is
neither asserted nor refuted by this quadratic test. -/
namespace KLSConstantImprovement.PostAffineWeightedGapTwoObstruction

theorem quadratic_regression_gap_two_characterization
    (m4 m3 V energy : ℝ)
    (hV : V=m4-1-m3^2) (hE : energy=(4/3:ℝ)*m4-m3^2) :
    energy < 2*V ↔ 3+(3/2:ℝ)*m3^2 < m4 := by
  constructor <;> intro h <;> nlinarith

theorem symmetric_fourth_above_three_rejects_gap_two
    (m4 V energy : ℝ) (hm : 3 < m4)
    (hV : V=m4-1) (hE : energy=(4/3:ℝ)*m4) :
    energy < 2*V := by
  nlinarith

theorem literal_laplace_quadratic_calibration :
    (4/3:ℝ)*6=8 ∧ (6:ℝ)-1=5 ∧ (8:ℝ)<2*5 := by
  norm_num

end KLSConstantImprovement.PostAffineWeightedGapTwoObstruction
#print axioms KLSConstantImprovement.PostAffineWeightedGapTwoObstruction.quadratic_regression_gap_two_characterization
#print axioms KLSConstantImprovement.PostAffineWeightedGapTwoObstruction.symmetric_fourth_above_three_rejects_gap_two
#print axioms KLSConstantImprovement.PostAffineWeightedGapTwoObstruction.literal_laplace_quadratic_calibration
