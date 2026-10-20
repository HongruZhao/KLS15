import KLSConstantImprovement.NearDiagonalExplicitSectorScalar

/-! A same-law neighbourhood of the new rank-free bounded-aspect sector.
The nearby ODECO tensor and all original-law norm/variance/signed transfers
are explicit inputs. This does not assert an arbitrary-tensor approximation. -/

noncomputable section
namespace KLSConstantImprovement.NearAspectODECOSectorScalar
set_option maxHeartbeats 2000000

theorem nearby_variance_cap {N NU VT VU rootN rootU rootT rootV h : ℝ}
    (hrootN : 0 < rootN) (hrootU : 0 < rootU)
    (hrootT : 0 ≤ rootT) (hrootV : 0 ≤ rootV)
    (hN : rootN ^ 2 = N) (hNU : rootU ^ 2 = NU)
    (hVT : rootT ^ 2 = VT) (hVU : rootV ^ 2 = VU)
    (hdiag : VU ≤ 293 * NU)
    (hnearU : rootU ≤ (251 / 250 : ℝ) * rootN)
    (hnearh : h ≤ rootN / 250) (htransfer : rootT ≤ rootV + 30 * h) :
    VT < 300 * N := by
  have hv : rootV < (428 / 25 : ℝ) * rootU := by
    by_contra! hn
    have hmul := mul_le_mul hn hn
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 428 / 25) hrootU.le) hrootV
    nlinarith [sq_pos_of_pos hrootU]
  have hbound : rootT < (54089 / 3125 : ℝ) * rootN := by linarith
  have hprod := mul_pos (sub_pos.mpr hbound)
    (add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num : (0 : ℝ) < 54089 / 3125) hrootN) hrootT)
  nlinarith [sq_pos_of_pos hrootN]

theorem nearby_signed_cap {N NU ST SU dU rootN radius h : ℝ}
    (hrootN : 0 < rootN) (hh : 0 ≤ h)
    (hN : rootN ^ 2 = N) (hNU : (249 : ℝ) ^ 2 * N ≤ 250 ^ 2 * NU)
    (hdU : dU ≤ NU / 100000000)
    (hdiag : 4 * NU - (11 / 6 : ℝ) * dU ≤ SU)
    (hradius : radius ≤ (501 / 250 : ℝ) * rootN)
    (hnearh : h ≤ rootN / 250) (htransfer : SU - 8 * radius * h ≤ ST) :
    (39 / 10 : ℝ) * N < ST := by
  have hm := mul_le_mul hradius hnearh hh
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 501 / 250) hrootN.le)
  have hSU : (4 - 11 / 600000000 : ℝ) * NU ≤ SU := by linarith
  nlinarith [sq_pos_of_pos hrootN]

theorem nearby_additive_sector {N S V : ℝ}
    (hV : V < 300 * N) (hS : (39 / 10 : ℝ) * N < S) :
    (59 / 10 : ℝ) * N < 224 * N + 21 * S - V := by
  linarith

end KLSConstantImprovement.NearAspectODECOSectorScalar
#print axioms KLSConstantImprovement.NearAspectODECOSectorScalar.nearby_variance_cap
#print axioms KLSConstantImprovement.NearAspectODECOSectorScalar.nearby_signed_cap
#print axioms KLSConstantImprovement.NearAspectODECOSectorScalar.nearby_additive_sector
