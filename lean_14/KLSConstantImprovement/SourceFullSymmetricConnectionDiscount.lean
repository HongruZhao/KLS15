import KLSConstantImprovement.TensorGramThirdSandwich

/-! The full-symmetric slot projection retains source curvature and the
source connection commutator in the affine main cost. Those charges are
not identified with target Poisson curvature. The final raw336 statement
is conditional on a still-open SAME-field response inequality. -/
noncomputable section
namespace KLSConstantImprovement.SourceFullSymmetricConnectionDiscount

theorem full_symmetric_slot_charge {b W Q R p : ℝ}
    (hslot : b^2 ≤ W*((Q+2*R)/3))
    (hsource : Q+R=W-p) :
    2*b^2 ≤ W*(W-p-(Q-R)/3) := by
  have heq : W*((Q+2*R)/3)=(W*(W-p-(Q-R)/3))/2 := by
    rw [← hsource]
    ring
  rw [heq] at hslot
  nlinarith

/-- A completed square retains the complete source charge q. -/
theorem affine_main_source_discount {W q J b : ℝ}
    (hW : 0 ≤ W) (hq : 0 ≤ q) (hqW : q ≤ W)
    (hidentity : J=W+2*b)
    (hcharge : 2*b^2 ≤ W*(W-q)) :
    Real.sqrt 2*J+q ≤ (Real.sqrt 2+2)*W := by
  have hr : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  by_cases hz : W=0
  · have hqz : q=0 := by linarith
    have hbz : b=0 := by nlinarith [sq_nonneg b]
    have hJz : J=0 := by rw [hidentity, hz, hbz]; ring
    simp [hz, hqz, hJz]
  · have hWp : 0<W := lt_of_le_of_ne hW (Ne.symm hz)
    have hsqb : (Real.sqrt (2:ℝ)*b)^2=2*b^2 := by
      rw [mul_pow, hrs]
    have hlin : 2*Real.sqrt 2*b+q ≤ 2*W := by
      by_contra h
      have hlt : 2*W < 2*Real.sqrt 2*b+q := lt_of_not_ge h
      have hp := mul_pos hWp (sub_pos.mpr hlt)
      nlinarith [sq_nonneg (Real.sqrt 2*b-W)]
    nlinarith

theorem original_kernel_main_source_discount {W q J b N : ℝ}
    (hW : 0 ≤ W) (hN : 0 ≤ N) (hq : 0 ≤ q) (hqW : q ≤ W)
    (hbound : W ≤ (8*Real.sqrt 2)*N)
    (hidentity : J=W+2*b)
    (hcharge : 2*b^2 ≤ W*(W-q)) :
    Real.sqrt 2*J+q ≤ (16+16*Real.sqrt 2)*N := by
  have h := affine_main_source_discount hW hq hqW hidentity hcharge
  have hr : 0 ≤ Real.sqrt (2:ℝ) := Real.sqrt_nonneg _
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp := mul_nonneg (show 0 ≤ Real.sqrt (2:ℝ)+2 by positivity)
    (sub_nonneg.mpr hbound)
  have heq : (Real.sqrt (2:ℝ)+2)*(8*Real.sqrt 2)*N=
      (16+16*Real.sqrt 2)*N := by
    calc
      (Real.sqrt (2:ℝ)+2)*(8*Real.sqrt 2)*N=
          (8*(Real.sqrt 2)^2+16*Real.sqrt 2)*N := by ring
      _=(16+16*Real.sqrt 2)*N := by rw [hrs]; ring
  nlinarith

/-- The response may consume the paid SOURCE discount q. This theorem
does not assert that the response hypothesis holds for an original law. -/
theorem conditional_combined_source_discount {V J loss q N : ℝ}
    (hmain : Real.sqrt 2*J+q ≤ (16+16*Real.sqrt 2)*N)
    (hvariance : V=9*J+loss)
    (hresponse : Real.sqrt 2*loss ≤ 90*Real.sqrt 2*N+9*q) :
    Real.sqrt 2*V ≤ (144+234*Real.sqrt 2)*N := by
  have hscaled := congrArg (fun z : ℝ => Real.sqrt 2*z) hvariance
  nlinarith [hscaled]

theorem conditional_raw_cap {V N : ℝ} (hN : 0 ≤ N)
    (hpaid : Real.sqrt 2*V ≤ (144+234*Real.sqrt 2)*N) :
    V ≤ (234+72*Real.sqrt 2)*N := by
  have hr : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have heq : Real.sqrt 2*((234+72*Real.sqrt 2)*N)=
      (144+234*Real.sqrt 2)*N := by
    calc
      Real.sqrt 2*((234+72*Real.sqrt 2)*N)=
          (234*Real.sqrt 2+72*(Real.sqrt 2)^2)*N := by ring
      _=(144+234*Real.sqrt 2)*N := by rw [hrs]; ring
  rw [← heq] at hpaid
  exact (mul_le_mul_iff_right₀ hr).mp hpaid

theorem raw_cap_coefficient_lt_336 : (234+72*Real.sqrt (2:ℝ))<336 := by
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hrs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  nlinarith

end KLSConstantImprovement.SourceFullSymmetricConnectionDiscount
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.full_symmetric_slot_charge
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.affine_main_source_discount
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.original_kernel_main_source_discount
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.conditional_combined_source_discount
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.conditional_raw_cap
#print axioms KLSConstantImprovement.SourceFullSymmetricConnectionDiscount.raw_cap_coefficient_lt_336
