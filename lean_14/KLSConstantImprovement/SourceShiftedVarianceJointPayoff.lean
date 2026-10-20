import KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff

/-! The additional regressed-variance spectral estimate sharpens the
same-source analytic raw470.8 payoff to raw2351/5=470.2. Actual source,
spectral calculus, normalized BL and Riesz identifications remain explicit
premises. No closed original-class Lean variance or Poincare endpoint
is asserted. Production and all main/response discounts are retained. -/
noncomputable section
namespace KLSConstantImprovement.SourceShiftedVarianceJointPayoff
open SourceMatchedMeanResponseConditionalPayoff

theorem cross_linear_majorant {rho r N delta ell : ℝ}
    (hr : 0 ≤ r) (hd : 0 ≤ delta) (hv : 0 ≤ N-delta-ell)
    (hc : rho^2 ≤ r*(20*N+205*delta-20*ell)/1331) :
    rho ≤ (9/100:ℝ)*r+(500/11979:ℝ)*N+
      (5125/11979:ℝ)*delta-(500/11979:ℝ)*ell := by
  have hu : 0 ≤ (9/100:ℝ)*r+(500/11979:ℝ)*N+
      (5125/11979:ℝ)*delta-(500/11979:ℝ)*ell := by nlinarith
  have hs := sq_nonneg ((9/100:ℝ)*r-(500/11979:ℝ)*N-
      (5125/11979:ℝ)*delta+(500/11979:ℝ)*ell)
  nlinarith

theorem joint_coefficient_certificate :
    0 ≤ ((2351/45:ℝ)-(173/73:ℝ)*(10750/11979:ℝ))-
      ((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)+
        (173/73:ℝ)*((9/100:ℝ)-(5125/11979:ℝ))) ∧
    ((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)+
        (173/73:ℝ)*((9/100:ℝ)-(5125/11979:ℝ)))^2+
      ((519/100:ℝ)*(1+Real.sqrt 2)+(519/73:ℝ))^2 ≤
    (((2351/45:ℝ)-(173/73:ℝ)*(10750/11979:ℝ))-
      ((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)+
        (173/73:ℝ)*((9/100:ℝ)-(5125/11979:ℝ))))^2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  constructor <;> nlinarith

theorem retained_joint_raw2351_div5
    {V J I W N r t g k q xi losses delta ell rho : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hr : 0 ≤ r) (hd : 0 ≤ delta) (hv : 0 ≤ N-delta-ell)
    (hstate : r+delta=2*N-g)
    (hcross : rho^2 ≤ r*(20*N+205*delta-20*ell)/1331)
    (hYoung : V ≤ (1557/100:ℝ)*J+(1557/73:ℝ)*I)
    (hMain : J+(Real.sqrt 2/2)*q ≤ (1+Real.sqrt 2)*W)
    (hDirect : W+2*k ≤ 3*(r+t))
    (hResponse : I ≤ W+r+rho-xi/2-losses) :
    V ≤ (2351/5:ℝ)*N-(227997713/971630:ℝ)*g-
      (86500/97163:ℝ)*ell-
      ((1557/50:ℝ)*(1+Real.sqrt 2)+(3114/73:ℝ))*k-
      (1557*Real.sqrt 2/200)*q-(1557/146:ℝ)*xi-(1557/73:ℝ)*losses := by
  let A : ℝ := (519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)+
      (173/73:ℝ)*((9/100:ℝ)-(5125/11979:ℝ))
  let B : ℝ := (519/100:ℝ)*(1+Real.sqrt 2)+(519/73:ℝ)
  have hcoef := joint_coefficient_certificate
  have hs := disk_linear_support hneff hcoef.1 hcoef.2 hdisk
  have hc := cross_linear_majorant hr hd hv hcross
  have hm := mul_le_mul_of_nonneg_left hMain (show (0:ℝ) ≤ 1557/100 by norm_num)
  have hi := mul_le_mul_of_nonneg_left hResponse (show (0:ℝ) ≤ 1557/73 by norm_num)
  have hcc := mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 1557/73 by norm_num)
  have hk := mul_le_mul_of_nonneg_left hDirect
    (show (0:ℝ) ≤ (1557/100:ℝ)*(1+Real.sqrt 2)+(1557/73:ℝ) by positivity)
  have hvs : V ≤ 9*(A*r+B*t)+(1859750/97163:ℝ)*N-
      ((1557/73:ℝ)*(5125/11979:ℝ))*g-(86500/97163:ℝ)*ell-
      ((1557/50:ℝ)*(1+Real.sqrt 2)+(3114/73:ℝ))*k-
      (1557*Real.sqrt 2/200)*q-(1557/146:ℝ)*xi-(1557/73:ℝ)*losses := by
    dsimp [A,B]
    nlinarith
  dsimp [A,B] at hvs
  nlinarith

end KLSConstantImprovement.SourceShiftedVarianceJointPayoff
#print axioms KLSConstantImprovement.SourceShiftedVarianceJointPayoff.cross_linear_majorant
#print axioms KLSConstantImprovement.SourceShiftedVarianceJointPayoff.joint_coefficient_certificate
#print axioms KLSConstantImprovement.SourceShiftedVarianceJointPayoff.retained_joint_raw2351_div5
