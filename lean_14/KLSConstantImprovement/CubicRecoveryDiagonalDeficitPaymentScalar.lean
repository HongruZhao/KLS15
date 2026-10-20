import KLSConstantImprovement.DeficitCurvatureScalar

/-! Scalar local-Taylor payment. The analytic tilt/covariance neighborhood
and original-law approximation are documented in the separate proof note;
they are explicit inputs here, and no full divergence or CP endpoint is asserted. -/
noncomputable section
open Set
namespace KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar
set_option maxHeartbeats 1500000

theorem local_taylor_squared_payment {d e L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hcover : 2*d ≤ L*r^2)
    (hTaylor : ∀ s ∈ Icc (-r) r,0 ≤ d+e*s+(L/2)*s^2) :
    e^2 ≤ 2*L*d := by
  have hp := hTaylor r ⟨by linarith,le_rfl⟩
  have hn := hTaylor (-r) ⟨le_rfl,by linarith⟩
  have heUpper : e ≤ L*r := by
    apply (mul_le_mul_iff_of_pos_right hr).mp
    nlinarith [hn,hcover]
  have heLower : -(L*r) ≤ e := by
    apply (mul_le_mul_iff_of_pos_right hr).mp
    nlinarith [hp,hcover]
  have hpoint : -e/L ∈ Icc (-r) r := by
    constructor
    · apply (le_div_iff₀ hL).mpr
      nlinarith [heUpper]
    · apply (div_le_iff₀ hL).mpr
      nlinarith [heLower]
  have hmin := hTaylor (-e/L) hpoint
  have hid : d+e*(-e/L)+(L/2)*(-e/L)^2 = d-e^2/(2*L) := by
    field_simp [ne_of_gt hL]
    ring
  rw [hid] at hmin
  have hh : e^2/(2*L) ≤ d := sub_nonneg.mp hmin
  have hd := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 2) hL)).mp hh
  nlinarith

theorem diagonal_deficit_squared_payment {W d e : ℝ} (hW : 0 ≤ W)
    (hd0 : 0 ≤ d) (hd8 : d ≤ 8*W)
    (hTaylor : ∀ s ∈ Icc (-(1/6:ℝ)) (1/6),0 ≤ d+e*s+800*W*s^2) :
    e^2 ≤ 3200*W*d := by
  by_cases hz : W = 0
  · subst W
    have hd : d = 0 := by linarith
    have hp := hTaylor (1/6) (by norm_num : (1/6:ℝ) ∈ Icc (-(1/6:ℝ)) (1/6))
    have hn := hTaylor (-(1/6)) (by norm_num : (-(1/6:ℝ)) ∈ Icc (-(1/6:ℝ)) (1/6))
    have he : e = 0 := by nlinarith [hp,hn,hd]
    simp [he]
  · have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    have hh := local_taylor_squared_payment
      (L := 1600*W) (r := (1/6:ℝ)) (d := d) (e := e)
      (by positivity) (by norm_num)
      (by nlinarith [hd8]) (by
        intro s hs
        have hp := hTaylor s hs
        convert hp using 1 <;> ring)
    convert hh using 1 <;> ring

theorem paid_whitening_constant : (276:ℝ)*(16/9)^3 < 1600 := by norm_num
theorem paid_radius_covers_all_quad_deficits : (2:ℝ)*8 < 1600*(1/6)^2 := by norm_num

end KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar
#print axioms KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar.local_taylor_squared_payment
#print axioms KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar.diagonal_deficit_squared_payment
#print axioms KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar.paid_whitening_constant
#print axioms KLSConstantImprovement.CubicRecoveryDiagonalDeficitPaymentScalar.paid_radius_covers_all_quad_deficits
