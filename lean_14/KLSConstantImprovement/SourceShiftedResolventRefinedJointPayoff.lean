import KLSConstantImprovement.SourceShiftedResolventJointPayoff

/-! A rational Young ratio 73/100 sharpens the retained joint raw471
payoff to raw2354/5. Actual source/operator/BL/Riesz bindings remain
explicit inputs. This proves no closed actual-law Lean variance theorem
and no new original-class Poincare endpoint. -/
noncomputable section
namespace KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff
open SourceMatchedMeanResponseConditionalPayoff

theorem joint_coefficient_certificate :
    0 ≤ (2354/45:ℝ)-((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)) ∧
    ((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ))^2+
      ((519/100:ℝ)*(1+Real.sqrt 2)+(1211/146:ℝ))^2 ≤
    ((2354/45:ℝ)-((519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)))^2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  constructor <;> nlinarith

theorem retained_joint_raw2354_div5
    {V J I W N r t g k q xi losses : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hYoung : V ≤ (1557/100:ℝ)*J+(1557/73:ℝ)*I)
    (hMain : J+(Real.sqrt 2/2)*q ≤ (1+Real.sqrt 2)*W)
    (hDirect : W+2*k ≤ 3*(r+t))
    (hResponse : I ≤ W+r+t/2-xi/2-losses) :
    V ≤ (2354/5:ℝ)*N-(1177/5:ℝ)*g-
      ((1557/50:ℝ)*(1+Real.sqrt 2)+(3114/73:ℝ))*k-
      (1557*Real.sqrt 2/200)*q-(1557/146:ℝ)*xi-(1557/73:ℝ)*losses := by
  let A : ℝ := (519/100:ℝ)*(1+Real.sqrt 2)+(692/73:ℝ)
  let B : ℝ := (519/100:ℝ)*(1+Real.sqrt 2)+(1211/146:ℝ)
  have hc := joint_coefficient_certificate
  have hs := disk_linear_support hneff hc.1 hc.2 hdisk
  have hm := mul_le_mul_of_nonneg_left hMain (show (0:ℝ) ≤ 1557/100 by norm_num)
  have hi := mul_le_mul_of_nonneg_left hResponse (show (0:ℝ) ≤ 1557/73 by norm_num)
  have hk := mul_le_mul_of_nonneg_left hDirect
    (show (0:ℝ) ≤ (1557/100:ℝ)*(1+Real.sqrt 2)+(1557/73:ℝ) by positivity)
  have hv : V ≤ 9*(A*r+B*t)-
      ((1557/50:ℝ)*(1+Real.sqrt 2)+(3114/73:ℝ))*k-
      (1557*Real.sqrt 2/200)*q-(1557/146:ℝ)*xi-(1557/73:ℝ)*losses := by
    dsimp [A,B]
    nlinarith
  dsimp [A,B] at hv
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_split_73_div100_young (a f : E) :
    9*‖a+f‖^2 ≤ (1557/100:ℝ)*‖a‖^2+(1557/73:ℝ)*‖f‖^2 := by
  have hc : inner ℝ a f ≤ ‖a‖*‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg (73*‖a‖-100*‖f‖)
  rw [norm_add_sq_real]
  nlinarith

end KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff
#print axioms KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff.joint_coefficient_certificate
#print axioms KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff.retained_joint_raw2354_div5
#print axioms KLSConstantImprovement.SourceShiftedResolventRefinedJointPayoff.source_split_73_div100_young
