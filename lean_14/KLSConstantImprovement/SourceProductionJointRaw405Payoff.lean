import KLSConstantImprovement.JointRowMainCubicPayoff
import KLSConstantImprovement.FullSymmetricProductionCoercivity

/-! Quantitative payoff for the newly paid same-field production.
Actual source, full tensor-slot whitening, natural-domain, scalar Riesz,
and target-variance transfer are the companion analytic inputs. This is
not a closed original-class Lean raw405 or Poincare endpoint. -/
noncomputable section
namespace KLSConstantImprovement.SourceProductionJointRaw405Payoff
open SourceMatchedMeanResponseConditionalPayoff

theorem rational_affine_main_discount {W J q : ℝ}
    (hW : 0 ≤ W) (hq : 0 ≤ q)
    (hmain : Real.sqrt 2*J+q ≤ (Real.sqrt 2+2)*W) :
    J ≤ (169/70:ℝ)*W-(7/10:ℝ)*q := by
  have hr : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have heq : Real.sqrt 2*((1+Real.sqrt 2)*W-Real.sqrt 2*q/2) =
      (Real.sqrt 2+2)*W-q := by
    calc
      _ = (Real.sqrt 2+(Real.sqrt 2)^2)*W-(Real.sqrt 2)^2*q/2 := by ring
      _ = _ := by rw [hs]; ring
  have hJ : J ≤ (1+Real.sqrt 2)*W-Real.sqrt 2*q/2 := by
    apply (mul_le_mul_iff_right₀ hr).mp
    rw [heq]
    linarith
  have hup : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  have hlo : (7/5:ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hwp := mul_nonneg hW (sub_nonneg.mpr hup)
  have hqp := mul_nonneg hq (sub_nonneg.mpr hlo)
  nlinarith

theorem response_bound_from_paid_production
    {I m W r cf t xi extra theta gammaRow pcol hookT center responseLoss : ℝ}
    (hproduction : pcol+(4/3:ℝ)*W-gammaRow+(3/2:ℝ)*hookT+8*center ≤ xi)
    (hrow : gammaRow ≤ theta)
    (hcurvature : theta+extra=2*r-2*cf)
    (hmetric : m=W+r-cf-(xi+extra)/2)
    (hresponse : I ≤ m-responseLoss)
    (hfilter : -cf ≤ t/2) :
    I ≤ W/3+2*r+t-
      (extra+pcol/2+3*hookT/4+4*center+responseLoss) := by
  linarith

theorem retained_new_main_branch
    {V J I W r t q k mainDefect productionLoss : ℝ}
    (hmain : J ≤ (169/70:ℝ)*W-(7/10:ℝ)*q)
    (hresponse : I ≤ W/3+2*r+t-productionLoss)
    (hyoung : V ≤ (72/5:ℝ)*(J-mainDefect)+24*I)
    (hdirect : W+2*k ≤ 3*(r+t)) :
    V ≤ (30852/175:ℝ)*r+(26652/175:ℝ)*t-(252/25:ℝ)*q-
      ((14968/175:ℝ)*k+(72/5:ℝ)*mainDefect+24*productionLoss) := by
  linarith

theorem raw405_disk_certificate :
    0 ≤ (405:ℝ)-(762588/4375:ℝ) ∧
    (762588/4375:ℝ)^2+(660738/4375:ℝ)^2 ≤
      ((405:ℝ)-(762588/4375:ℝ))^2 := by
  norm_num

theorem retained_joint_raw405
    {V N g r t q rowLoss newLoss : ℝ}
    (hg : 0 ≤ g) (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hq : 0 ≤ q) (hrowLoss : 0 ≤ rowLoss) (hnewLoss : 0 ≤ newLoss)
    (hrow : V ≤ 168*r+147*t+(63/2:ℝ)*q-rowLoss)
    (hnew : V ≤ (30852/175:ℝ)*r+(26652/175:ℝ)*t-
      (252/25:ℝ)*q-newLoss) :
    V ≤ 405*N-(405/2:ℝ)*g-(63/625:ℝ)*q-
      (6/25:ℝ)*rowLoss-(19/25:ℝ)*newLoss ∧ V ≤ 405*N := by
  have hc := raw405_disk_certificate
  have hsupport := disk_linear_support hneff hc.1 hc.2 hdisk
  have haverage : V ≤ (762588/4375:ℝ)*r+(660738/4375:ℝ)*t-
      (63/625:ℝ)*q-(6/25:ℝ)*rowLoss-(19/25:ℝ)*newLoss := by
    linarith
  have hfirst : V ≤ 405*N-(405/2:ℝ)*g-(63/625:ℝ)*q-
      (6/25:ℝ)*rowLoss-(19/25:ℝ)*newLoss := by nlinarith
  exact ⟨hfirst, by linarith⟩

end KLSConstantImprovement.SourceProductionJointRaw405Payoff
#print axioms KLSConstantImprovement.SourceProductionJointRaw405Payoff.rational_affine_main_discount
#print axioms KLSConstantImprovement.SourceProductionJointRaw405Payoff.response_bound_from_paid_production
#print axioms KLSConstantImprovement.SourceProductionJointRaw405Payoff.retained_new_main_branch
#print axioms KLSConstantImprovement.SourceProductionJointRaw405Payoff.raw405_disk_certificate
#print axioms KLSConstantImprovement.SourceProductionJointRaw405Payoff.retained_joint_raw405
