import KLSConstantImprovement.DiagonalDirectionalStabilityScalar

/-! Rational transfer for a same-law test near an orthogonally decomposable
test. All norm, deficit, covariance and perturbation estimates remain explicit
inputs. This does not assert a universal tensor approximation theorem. -/
noncomputable section
namespace KLSConstantImprovement.NearDiagonalExplicitSectorScalar
set_option maxHeartbeats 2000000

theorem nearby_deficit_rank_budget {N NU dT dU h rank : ℝ}
    (hN : 0 < N)
    (hT : 800*rank^2*dT ≤ N) (hh : 102400*rank^2*h^2 ≤ N)
    (htransfer : dU ≤ 2*dT+16*h^2)
    (hNU : (319:ℝ)^2*N ≤ 320^2*NU) :
    (10*rank)^2*dU ≤ NU := by
  have hm := mul_le_mul_of_nonneg_left htransfer (sq_nonneg rank)
  have hsmall : 100*rank^2*dU ≤ (17/64:ℝ)*N := by nlinarith
  nlinarith

theorem nearby_variance_cap {N NU VT VU rootN rootU rootT rootV h : ℝ}
    (hrootN : 0 < rootN) (hrootU : 0 < rootU)
    (hrootT : 0 ≤ rootT) (hrootV : 0 ≤ rootV)
    (hN : rootN^2 = N) (hNU : rootU^2 = NU)
    (hVT : rootT^2 = VT) (hVU : rootV^2 = VU)
    (hdiag : VU ≤ 285*NU)
    (hnearU : rootU ≤ (321/320:ℝ)*rootN)
    (hnearh : h ≤ rootN/320) (htransfer : rootT ≤ rootV+30*h) :
    VT < (2975593401/10240000:ℝ)*N := by
  have hv : rootV < (169/10:ℝ)*rootU := by
    by_contra! hn
    have hmul := mul_le_mul hn hn
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 169/10) hrootU.le) hrootV
    nlinarith [sq_pos_of_pos hrootU]
  have hbound : rootT < (54549/3200:ℝ)*rootN := by linarith
  have hprod := mul_pos (sub_pos.mpr hbound)
    (add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num : (0:ℝ) < 54549/3200) hrootN) hrootT)
  nlinarith

theorem nearby_signed_cap {N NU ST SU dU rootN radius h : ℝ}
    (hrootN : 0 ≤ rootN) (hh : 0 ≤ h)
    (hN : rootN^2 = N) (hNU : (319:ℝ)^2*N ≤ 320^2*NU)
    (hdU : dU ≤ (17/6400:ℝ)*N)
    (hdiag : 4*NU-(11/6:ℝ)*dU ≤ SU)
    (hradius : radius ≤ (641/320:ℝ)*rootN)
    (hnearh : h ≤ rootN/320) (htransfer : SU-8*radius*h ≤ ST) :
    (301063/76800:ℝ)*N ≤ ST := by
  have hm := mul_le_mul hradius hnearh hh
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 641/320) hrootN)
  nlinarith

theorem nearby_additive_sector {N S V : ℝ} (hN : 0 < N)
    (hV : V < (2975593401/10240000:ℝ)*N)
    (hS : (301063/76800:ℝ)*N ≤ S) :
    V < 291*N ∧ (39/10:ℝ)*N < S ∧
      (149/10:ℝ)*N < 224*N+21*S-V := by
  constructor
  · nlinarith
  constructor <;> nlinarith

end KLSConstantImprovement.NearDiagonalExplicitSectorScalar
#print axioms KLSConstantImprovement.NearDiagonalExplicitSectorScalar.nearby_deficit_rank_budget
#print axioms KLSConstantImprovement.NearDiagonalExplicitSectorScalar.nearby_variance_cap
#print axioms KLSConstantImprovement.NearDiagonalExplicitSectorScalar.nearby_signed_cap
#print axioms KLSConstantImprovement.NearDiagonalExplicitSectorScalar.nearby_additive_sector
