import Mathlib

/- Exact original ODECO coefficient-aspect sector scalar endgame.
The same finite metric/Poisson/domain, full main, original d/S and
actual law geometry identifications are explicit analytic premises. -/

namespace KLSConstantImprovement.OriginalCoefficientAspectSectorScalar

theorem regularized_aspect_ratio
    (qmin qmax eta kappa : ℝ) (heta : 0 ≤ eta) (hk : 1 ≤ kappa)
    (haspect : qmax ≤ kappa * qmin) :
    qmax + eta ≤ kappa * (qmin + eta) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hk) heta]

theorem variance_root_cap
    (z j a : ℝ) (hz : 0 ≤ z) (hj : 0 ≤ j)
    (hmain : j ≤ (3421 / 200 : ℝ))
    (hresponse : a ≤ (7 / 5000 : ℝ))
    (hvariance : z ^ 2 ≤ j ^ 2 + a * z) :
    z ≤ (21383 / 1250 : ℝ) := by
  have hjsquare : j ^ 2 ≤ (3421 / 200 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (by positivity : 0 ≤ 3421 / 200 + j)]
  have haz : a * z ≤ (7 / 5000 : ℝ) * z :=
    mul_le_mul_of_nonneg_right hresponse hz
  by_contra h
  have hgt : (21383 / 1250 : ℝ) < z := lt_of_not_ge h
  have hp : 0 < (z - 21383 / 1250) * (z + 21383 / 1250 - 7 / 5000) :=
    mul_pos (sub_pos.mpr hgt) (by linarith)
  nlinarith

theorem variance_squared_cap
    (z : ℝ) (hz : 0 ≤ z) (hroot : z ≤ (21383 / 1250 : ℝ)) :
    z ^ 2 ≤ (457232689 / 1562500 : ℝ) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hroot) (by positivity : 0 ≤ 21383 / 1250 + z)]

theorem original_additive_sector_margin
    (N d V S : ℝ) (hN : 0 < N) (hd : d ≤ N / 100000000)
    (hV : V ≤ (457232689 / 1562500 : ℝ) * N)
    (hS : 4 * N - (11 / 6 : ℝ) * d ≤ S) :
    15 * N < 224 * N + 21 * S - V := by
  nlinarith

#print axioms KLSConstantImprovement.OriginalCoefficientAspectSectorScalar.regularized_aspect_ratio
#print axioms KLSConstantImprovement.OriginalCoefficientAspectSectorScalar.variance_root_cap
#print axioms KLSConstantImprovement.OriginalCoefficientAspectSectorScalar.variance_squared_cap
#print axioms KLSConstantImprovement.OriginalCoefficientAspectSectorScalar.original_additive_sector_margin

end KLSConstantImprovement.OriginalCoefficientAspectSectorScalar
