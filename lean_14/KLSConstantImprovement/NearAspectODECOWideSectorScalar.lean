import KLSConstantImprovement.NearAspectODECOSectorScalar

/-! A wider same-law neighbourhood of the paid bounded-aspect ODECO sector.
The nearby tensor and all original-law norm, variance, and signed transfers
remain explicit inputs. No arbitrary-tensor approximation is asserted. -/

noncomputable section
namespace KLSConstantImprovement.NearAspectODECOWideSectorScalar
set_option maxHeartbeats 2000000

theorem nearby_variance_cap {N NU VT VU rootN rootU rootT rootV h : ℝ}
    (hrootN : 0 < rootN) (hrootU : 0 < rootU)
    (hrootT : 0 ≤ rootT) (hrootV : 0 ≤ rootV)
    (hN : rootN ^ 2 = N) (hNU : rootU ^ 2 = NU)
    (hVT : rootT ^ 2 = VT) (hVU : rootV ^ 2 = VU)
    (hdiag : VU ≤ 293 * NU)
    (hnearU : rootU ≤ (151 / 150 : ℝ) * rootN)
    (hnearh : h ≤ rootN / 150) (htransfer : rootT ≤ rootV + 30 * h) :
    VT < 304 * N := by
  have hv : rootV < (428 / 25 : ℝ) * rootU := by
    by_contra! hn
    have hmul := mul_le_mul hn hn
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 428 / 25) hrootU.le) hrootV
    nlinarith [sq_pos_of_pos hrootU]
  have hbound : rootT < (32689 / 1875 : ℝ) * rootN := by linarith
  have hprod := mul_pos (sub_pos.mpr hbound)
    (add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num : (0 : ℝ) < 32689 / 1875) hrootN) hrootT)
  nlinarith [sq_pos_of_pos hrootN]

theorem nearby_signed_cap {N NU ST SU dU rootN radius h : ℝ}
    (hrootN : 0 < rootN) (hh : 0 ≤ h)
    (hN : rootN ^ 2 = N) (hNU : (149 : ℝ) ^ 2 * N ≤ 150 ^ 2 * NU)
    (hdU : dU ≤ NU / 100000000)
    (hdiag : 4 * NU - (11 / 6 : ℝ) * dU ≤ SU)
    (hradius : radius ≤ (301 / 150 : ℝ) * rootN)
    (hnearh : h ≤ rootN / 150) (htransfer : SU - 8 * radius * h ≤ ST) :
    (3839 / 1000 : ℝ) * N < ST := by
  have hm := mul_le_mul hradius hnearh hh
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 301 / 150) hrootN.le)
  have hSU : (4 - 11 / 600000000 : ℝ) * NU ≤ SU := by linarith
  nlinarith [sq_pos_of_pos hrootN]

theorem nearby_additive_sector {N S V : ℝ}
    (hV : V < 304 * N) (hS : (3839 / 1000 : ℝ) * N < S) :
    (619 / 1000 : ℝ) * N < 224 * N + 21 * S - V := by
  linarith

end KLSConstantImprovement.NearAspectODECOWideSectorScalar
#print axioms KLSConstantImprovement.NearAspectODECOWideSectorScalar.nearby_variance_cap
#print axioms KLSConstantImprovement.NearAspectODECOWideSectorScalar.nearby_signed_cap
#print axioms KLSConstantImprovement.NearAspectODECOWideSectorScalar.nearby_additive_sector
