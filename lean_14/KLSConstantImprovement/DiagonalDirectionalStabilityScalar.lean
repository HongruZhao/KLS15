import KLSConstantImprovement.DeficitCurvatureScalar

/-! Scalar consequences of the diagonal original-law moment budgets and a
pointwise nonnegative cubic remainder. Moment identities, original-law
Hessian realization, and same-law tensor perturbation stay explicit inputs.
No general tensor variance bound or universal Poincare improvement is asserted. -/
noncomputable section
namespace KLSConstantImprovement.DiagonalDirectionalStabilityScalar
set_option maxHeartbeats 2000000

theorem diagonal_signed_budget {N d H gap S R3 : ℝ}
    (hH : 4*N-(4/3:ℝ)*d ≤ H) (hgap : gap ≤ d)
    (hS : H-gap/2 ≤ S) (hSR3 : S ≤ R3) (hR3 : R3 ≤ 4*N) :
    4*N-(11/6:ℝ)*d ≤ S ∧ S ≤ R3 ∧ R3 ≤ 4*N := by
  exact ⟨by linarith,hSR3,hR3⟩

theorem diagonal_signed_absolute {N d S : ℝ}
    (hlo : 4*N-(11/6:ℝ)*d ≤ S) (hhi : S ≤ 4*N) :
    |S-4*N| ≤ (11/6:ℝ)*d := by
  apply abs_le.mpr
  constructor <;> linarith

theorem diagonal_skew_payment {N d S R3 skew : ℝ}
    (hlo : 4*N-(11/6:ℝ)*d ≤ S) (hR3 : R3 ≤ 4*N)
    (hskew : skew = (R3-S)/2) : skew ≤ (11/12:ℝ)*d := by
  linarith

theorem diagonal_additive_gate {N d S V : ℝ}
    (hS : 4*N-(11/6:ℝ)*d ≤ S)
    (hV : V ≤ 308*N-(77/2:ℝ)*d) : 0 ≤ 224*N+21*S-V := by
  linarith

theorem near_diagonal_signed_transfer {NT NU ST SU dU D radius h : ℝ}
    (hdiag : |SU-4*NU| ≤ (11/6:ℝ)*dU) (hd : dU ≤ D)
    (hS : |ST-SU| ≤ 8*radius*h) (hN : |NT-NU| ≤ radius*h) :
    |ST-4*NT| ≤ (11/6:ℝ)*D+12*radius*h := by
  obtain ⟨hdiaglo,hdiaghi⟩ := abs_le.mp hdiag
  obtain ⟨hSlo,hShi⟩ := abs_le.mp hS
  obtain ⟨hNlo,hNhi⟩ := abs_le.mp hN
  apply abs_le.mpr
  constructor <;> nlinarith

theorem nonnegative_cubic_remainder {h b : ℝ} (hh : 0 ≤ h) (hb : 0 ≤ b) :
    |h-b|^3 ≤ h^3-b^3-3*b^2*(h-b) := by
  by_cases hbh : b ≤ h
  · rw [abs_of_nonneg (sub_nonneg.mpr hbh)]
    have hp : 0 ≤ 3*b*(h-b)^2 := by positivity
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge hbh)))]
    have hp : 0 ≤ (2*h+b)*(h-b)^2 := by positivity
    nlinarith

theorem rational_directional_error_coefficient : (12:ℝ)+3*Real.sqrt 2 ≤ 17 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem directional_third_tail_budget {tail response N d R C : ℝ}
    (hresponse : response ≤ C*Real.sqrt (N*d)+(17/12:ℝ)*d)
    (htail : tail ≤ 8*response+192*N/R) :
    tail ≤ 8*C*Real.sqrt (N*d)+(34/3:ℝ)*d+192*N/R := by
  linarith

theorem explicit_diagonal_rank_sector {N d rank root V S : ℝ}
    (hN : 0 < N) (hrank : 1 ≤ rank) (hroot : 0 ≤ root)
    (hd : d = N*root^2) (hbudget : (10*rank)^2*d ≤ N)
    (hV : V ≤ 216*N+690*rank*N*root)
    (hS : 4*N-(11/6:ℝ)*d ≤ S) :
    V ≤ 285*N ∧ 22*N < 224*N+21*S-V := by
  have heq : (10*rank)^2*d = N*(10*rank*root)^2 := by
    rw [hd]
    ring
  rw [heq] at hbudget
  have hsquare : (10*rank*root)^2 ≤ 1 :=
    (mul_le_mul_iff_of_pos_left hN).mp (by simpa only [mul_one] using hbudget)
  have hunit : 10*rank*root ≤ 1 := by
    nlinarith [sq_nonneg (10*rank*root-1)]
  have hmass := mul_le_mul_of_nonneg_left hunit hN.le
  have hrootrank : root ≤ rank*root := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrank) hroot]
  have hroot10 : root ≤ (1/10:ℝ) := by nlinarith
  have hroot2 : root^2 ≤ (1/100:ℝ) := by
    have hm := mul_le_mul hroot10 hroot10 hroot (by norm_num : (0:ℝ) ≤ 1/10)
    nlinarith
  have hdeficit := mul_le_mul_of_nonneg_left hroot2 hN.le
  have hd100 : d ≤ N/100 := by nlinarith [hd]
  refine ⟨by nlinarith,by nlinarith⟩

end KLSConstantImprovement.DiagonalDirectionalStabilityScalar
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.diagonal_signed_budget
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.diagonal_signed_absolute
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.diagonal_skew_payment
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.diagonal_additive_gate
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.near_diagonal_signed_transfer
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.nonnegative_cubic_remainder
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.rational_directional_error_coefficient
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.directional_third_tail_budget
#print axioms KLSConstantImprovement.DiagonalDirectionalStabilityScalar.explicit_diagonal_rank_sector
