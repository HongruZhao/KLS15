import KLSConstantImprovement.SourceShiftedResolventResponseUpper

/-! Joint disk optimization of the paid regular-source shifted-resolvent
response. Actual source, resolvent, normalized BL, scalar Riesz and literal
cubic bindings remain explicit inputs. This does not close their actual-law
formalization or assert a new original Poincare endpoint. All production,
main, skew, matching and curvature losses are retained. -/
noncomputable section
namespace KLSConstantImprovement.SourceShiftedResolventJointPayoff
open SourceMatchedMeanResponseConditionalPayoff

theorem joint_coefficient_certificate :
    0 ≤ (157/3:ℝ)-((175/12:ℝ)+(21/4:ℝ)*Real.sqrt 2) ∧
    ((175/12:ℝ)+(21/4:ℝ)*Real.sqrt 2)^2+
      ((161/12:ℝ)+(21/4:ℝ)*Real.sqrt 2)^2 ≤
    ((157/3:ℝ)-((175/12:ℝ)+(21/4:ℝ)*Real.sqrt 2))^2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hu : Real.sqrt (2:ℝ) ≤ 99/70 := by nlinarith
  constructor <;> nlinarith

theorem retained_joint_raw471
    {V J I W N r t g k q xi losses : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hYoung : V ≤ (63/4:ℝ)*J+21*I)
    (hMain : J+(Real.sqrt 2/2)*q ≤ (1+Real.sqrt 2)*W)
    (hDirect : W+2*k ≤ 3*(r+t))
    (hResponse : I ≤ W+r+t/2-xi/2-losses) :
    V ≤ 471*N-(471/2:ℝ)*g-
      ((63/2:ℝ)*(1+Real.sqrt 2)+42)*k-
      (63*Real.sqrt 2/8)*q-(21/2:ℝ)*xi-21*losses := by
  let A : ℝ := (175/12:ℝ)+(21/4:ℝ)*Real.sqrt 2
  let B : ℝ := (161/12:ℝ)+(21/4:ℝ)*Real.sqrt 2
  have hc := joint_coefficient_certificate
  have hs := disk_linear_support hneff hc.1 hc.2 hdisk
  have hm := mul_le_mul_of_nonneg_left hMain (show (0:ℝ) ≤ 63/4 by norm_num)
  have hi := mul_le_mul_of_nonneg_left hResponse (show (0:ℝ) ≤ 21 by norm_num)
  have hk := mul_le_mul_of_nonneg_left hDirect
    (show (0:ℝ) ≤ (63/4:ℝ)*(1+Real.sqrt 2)+21 by positivity)
  have hv : V ≤ 9*(A*r+B*t)-
      ((63/2:ℝ)*(1+Real.sqrt 2)+42)*k-
      (63*Real.sqrt 2/8)*q-(21/2:ℝ)*xi-21*losses := by
    dsimp [A,B]
    nlinarith
  dsimp [A,B] at hv
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem source_split_three_quarters_young (a f : E) :
    9*‖a+f‖^2 ≤ (63/4:ℝ)*‖a‖^2+21*‖f‖^2 := by
  have hc : inner ℝ a f ≤ ‖a‖*‖f‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hy := sq_nonneg (3*‖a‖-4*‖f‖)
  rw [norm_add_sq_real]
  nlinarith

end KLSConstantImprovement.SourceShiftedResolventJointPayoff
#print axioms KLSConstantImprovement.SourceShiftedResolventJointPayoff.joint_coefficient_certificate
#print axioms KLSConstantImprovement.SourceShiftedResolventJointPayoff.retained_joint_raw471
#print axioms KLSConstantImprovement.SourceShiftedResolventJointPayoff.source_split_three_quarters_young
