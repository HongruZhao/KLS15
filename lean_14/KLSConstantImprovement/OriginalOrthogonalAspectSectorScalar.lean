import Mathlib

/- Fivefold wider original ODECO coefficient-aspect scalar sector.
Root's Hilbert orthogonality, same finite-metric/domain response,
original S11/6 and geometry/aspect identification are explicit inputs. -/

namespace KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar

theorem combined_main_root_cap
    (combined core off : ℝ) (hc : 0 ≤ combined) (hcore : 0 ≤ core)
    (hidentity : combined ^ 2 ≤ core ^ 2 + off)
    (hcorecap : core ≤ (87 / 5 : ℝ)) (hoffcap : off ≤ (1 / 4 : ℝ)) :
    combined ≤ (1741 / 100 : ℝ) := by
  have hcoresquare : core ^ 2 ≤ (87 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcorecap) (by positivity : 0 ≤ 87 / 5 + core)]
  by_contra h
  have hgt : (1741 / 100 : ℝ) < combined := lt_of_not_ge h
  nlinarith [mul_pos (sub_pos.mpr hgt) (show 0 < combined + 1741 / 100 by linarith)]

theorem full_main_root_cap
    (main combined correction : ℝ)
    (htriangle : main ≤ combined + correction)
    (hc : combined ≤ (1741 / 100 : ℝ))
    (hcorr : correction ≤ (9 / 100 : ℝ)) : main ≤ (35 / 2 : ℝ) := by
  linarith

theorem variance_root_cap
    (z j a : ℝ) (hz : 0 ≤ z) (hj : 0 ≤ j)
    (hmain : j ≤ (35 / 2 : ℝ)) (hresponse : a ≤ (3 / 1000 : ℝ))
    (hvariance : z ^ 2 ≤ j ^ 2 + a * z) : z ≤ (17503 / 1000 : ℝ) := by
  have hjsquare : j ^ 2 ≤ (35 / 2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmain) (by positivity : 0 ≤ 35 / 2 + j)]
  have haz : a * z ≤ (3 / 1000 : ℝ) * z :=
    mul_le_mul_of_nonneg_right hresponse hz
  by_contra h
  have hgt : (17503 / 1000 : ℝ) < z := lt_of_not_ge h
  nlinarith [mul_pos (sub_pos.mpr hgt)
    (show 0 < z + 17503 / 1000 - 3 / 1000 by linarith)]

theorem original_additive_sector_margin
    (N d V S : ℝ) (hN : 0 < N) (hd : d ≤ N / 20000000)
    (hV : V < 307 * N) (hS : 4 * N - (11 / 6 : ℝ) * d ≤ S) :
    (1 - (77 / 40000000 : ℝ)) * N < 224 * N + 21 * S - V := by
  linarith

#print axioms KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar.combined_main_root_cap
#print axioms KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar.full_main_root_cap
#print axioms KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar.variance_root_cap
#print axioms KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar.original_additive_sector_margin

end KLSConstantImprovement.OriginalOrthogonalAspectSectorScalar
