import Mathlib

/- Scalar consequences of the original ODECO mixed-moment estimates only.
The kernel L3 bound and Holder inequality are explicit premises. This source
contains no original-law analytic bridge and was not built by the worker. -/

namespace KLSConstantImprovement.OriginalDiagonalWeightedCoreScalar

theorem affine_l3_rational_coefficient :
    (64 : ℝ) + 12 * Real.sqrt 2 < 81 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem mixed_error_cube_rational
    (N d q l w : ℝ) (hN : 0 ≤ N) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hq2 : q ^ 2 = N * d) (hl : 0 ≤ l)
    (hl3 : l ≤ 81 * q + (17 / 3 : ℝ) * d)
    (hholder : w ^ 3 ≤ 720 * N * l ^ 2) :
    w ^ 3 ≤ 9447840 * N ^ 2 * d + 46240 * N * d ^ 2 := by
  have hsum : 0 ≤ 81 * q + (17 / 3 : ℝ) * d + l := by positivity
  have hdiff : 0 ≤ 81 * q + (17 / 3 : ℝ) * d - l := by linarith
  have hprod := mul_nonneg hsum hdiff
  have hsq := sq_nonneg (81 * q - (17 / 3 : ℝ) * d)
  have hl2 : l ^ 2 ≤ 13122 * N * d + (578 / 9 : ℝ) * d ^ 2 := by
    nlinarith
  have hmult := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ 720 * N)
  nlinarith

theorem correction_joint_payment
    (N r3 a delta y correction d : ℝ)
    (hy : y = N - r3 / 4 - delta)
    (hc : correction = r3 + 4 * N - 4 * a)
    (hscalar : 4 * (2 * N - a) ≤ (8 / 3 : ℝ) * d) :
    correction + 4 * delta + 4 * y ≤ (8 / 3 : ℝ) * d := by
  linarith

#print axioms KLSConstantImprovement.OriginalDiagonalWeightedCoreScalar.affine_l3_rational_coefficient
#print axioms KLSConstantImprovement.OriginalDiagonalWeightedCoreScalar.mixed_error_cube_rational
#print axioms KLSConstantImprovement.OriginalDiagonalWeightedCoreScalar.correction_joint_payment

end KLSConstantImprovement.OriginalDiagonalWeightedCoreScalar
