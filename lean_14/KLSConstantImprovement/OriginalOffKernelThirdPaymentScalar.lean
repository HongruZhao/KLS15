import Mathlib

/- Scalar consequences of the original ODECO off-kernel cube identities.
The positive matrix trace remainder and original joint-kernel moment/domain
inputs are explicit premises. This source is not an actual-law bridge. -/

namespace KLSConstantImprovement.OriginalOffKernelThirdPaymentScalar

theorem cube_pinching_from_positive_remainder
    (cube diagonalCube positiveRemainder weightedOff : ℝ)
    (hid : cube - diagonalCube = positiveRemainder + 2 * weightedOff)
    (hpositive : 0 ≤ positiveRemainder) :
    2 * weightedOff ≤ cube - diagonalCube := by
  linarith

theorem original_weighted_off_third_payment
    (p cube diagonalCube traceCube q d b : ℝ)
    (hpinching : 2 * p ≤ cube - diagonalCube)
    (hupper : cube ≤ 6 * traceCube + 3 * Real.sqrt 2 * q + (3 / 4 : ℝ) * d * b)
    (hlower : 6 * traceCube - 12 * q - (2 / 3 : ℝ) * d * b ≤ diagonalCube) :
    2 * p ≤ (12 + 3 * Real.sqrt 2) * q + (17 / 12 : ℝ) * d * b := by
  nlinarith

theorem weighted_off_coefficient_lt_seventeen :
    (12 : ℝ) + 3 * Real.sqrt 2 < 17 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

#print axioms KLSConstantImprovement.OriginalOffKernelThirdPaymentScalar.cube_pinching_from_positive_remainder
#print axioms KLSConstantImprovement.OriginalOffKernelThirdPaymentScalar.original_weighted_off_third_payment
#print axioms KLSConstantImprovement.OriginalOffKernelThirdPaymentScalar.weighted_off_coefficient_lt_seventeen

end KLSConstantImprovement.OriginalOffKernelThirdPaymentScalar
