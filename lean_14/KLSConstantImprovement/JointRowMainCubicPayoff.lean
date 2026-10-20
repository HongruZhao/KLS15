import KLSConstantImprovement.GeometricQuadraticWeightedHigherOrderDefect
import KLSConstantImprovement.SourceShiftedVarianceJointPayoff
import KLSConstantImprovement.QuadraticGradientReferenceProjection

/-! New joint ROW/whole-cubic and shifted-main payoff. Actual source,
graph/Riesz, regular domain and original target moment passage remain
explicit analytic inputs. All scalar credits use the same law and T.
This is not a closed original-law Lean variance or Poincare theorem. -/
noncomputable section
namespace KLSConstantImprovement.JointRowMainCubicPayoff
open SourceMatchedMeanResponseConditionalPayoff

theorem affine_row_curvature_identity
    {W p e1 e2 q thetaZ : ℝ}
    (hPDE : W=p+e1+e2) (hq : 3*q=3*p+e2-e1)
    (hRow : thetaZ=p+e2) : thetaZ=(W+3*q-2*p)/2 := by
  linarith

theorem row_ell_young_remainder
    {ell W theta : ℝ} (hW : 0 ≤ W) (ht : 0 ≤ theta)
    (hCauchy : ell^2 ≤ W*theta) :
    0 ≤ 3*W/4+4*theta/3-2*ell := by
  have hs := sq_nonneg (3*W/4-4*theta/3)
  have hsq : (2*ell)^2 ≤ (3*W/4+4*theta/3)^2 := by nlinarith
  have hb : 0 ≤ 3*W/4+4*theta/3 := by positivity
  have h := le_of_sq_le_sq hsq hb
  linarith

theorem retained_whole_cubic_row_branch
    {V m W theta thetaF thetaZ ell r t q k p extra rowRem ellRem
      pcol rloss dloss skew etaDefect : ℝ}
    (hVariance : V ≤ 36*m-72*skew-36*etaDefect)
    (hRow : 2*m=W+theta+2*ell-pcol-rloss-dloss)
    (hSplit : theta+rowRem=(thetaF+thetaZ)/2)
    (hAffine : thetaZ=(W+3*q-2*p)/2)
    (hResponse : thetaF+extra ≤ 2*r+t)
    (hEll : ellRem=3*W/4+4*theta/3-2*ell)
    (hDirect : W+2*k ≤ 3*(r+t)) :
    V ≤ 168*r+147*t+(63/2:ℝ)*q-
      (84*k+21*p+21*extra+42*rowRem+18*ellRem+
        18*pcol+18*rloss+18*dloss+72*skew+36*etaDefect) := by
  linarith

theorem joint_row_main_disk_certificate :
    0 ≤ (42377119/97163:ℝ)-(503741289741/2720564000:ℝ) ∧
    (503741289741/2720564000:ℝ)^2+(346086381/2044000:ℝ)^2 ≤
      ((42377119/97163:ℝ)-(503741289741/2720564000:ℝ))^2 := by
  norm_num

theorem retained_joint_raw901_div2
    {V N g r t q ellD rowLoss shiftLoss : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q)
    (hWhole : V ≤ 168*r+147*t+(63/2:ℝ)*q-rowLoss)
    (hShifted : V ≤ (129825867247/680141000:ℝ)*r+
      (90323127/511000:ℝ)*t+(1859750/97163:ℝ)*N-
      ((1557/73:ℝ)*(5125/11979:ℝ))*g-(86500/97163:ℝ)*ellD-
      (1557*Real.sqrt 2/200)*q-shiftLoss) :
    V ≤ (901/2:ℝ)*N-(87414113/388652:ℝ)*g-
      (64875/97163:ℝ)*ellD-(1197/4000:ℝ)*q-rowLoss/4-3*shiftLoss/4 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hl : (7/5:ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hqq := mul_le_mul_of_nonneg_right hl hq
  have hc := joint_row_main_disk_certificate
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have hAverage : V ≤ (503741289741/2720564000:ℝ)*r+
      (346086381/2044000:ℝ)*t+(2789625/194326:ℝ)*N-
      ((3/4:ℝ)*(1557/73:ℝ)*(5125/11979:ℝ))*g-
      (64875/97163:ℝ)*ellD-(1197/4000:ℝ)*q-rowLoss/4-3*shiftLoss/4 := by
    nlinarith
  nlinarith

end KLSConstantImprovement.JointRowMainCubicPayoff
#print axioms KLSConstantImprovement.JointRowMainCubicPayoff.affine_row_curvature_identity
#print axioms KLSConstantImprovement.JointRowMainCubicPayoff.row_ell_young_remainder
#print axioms KLSConstantImprovement.JointRowMainCubicPayoff.retained_whole_cubic_row_branch
#print axioms KLSConstantImprovement.JointRowMainCubicPayoff.joint_row_main_disk_certificate
#print axioms KLSConstantImprovement.JointRowMainCubicPayoff.retained_joint_raw901_div2
