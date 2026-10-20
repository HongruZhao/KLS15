import KLSConstantImprovement.ShiftedFilterSignedCorrelationSlack

/-! Joint main/response graph completion, on the SAME source datum.
Actual u=Q Usym, q=Q Z and responseSkew=4s are paper bindings.
No arbitrary source matrix lift, positive uniform loss or new cap is proved. -/
noncomputable section
namespace KLSConstantImprovement.SourceCoupledMainResponseLossCredit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupled_projection_exact_square (u q : E) :
    ‖(2:ℝ) • u-q‖^2+(4/7:ℝ)*‖q‖^2 =
      (11/7:ℝ)*‖q-(14/11:ℝ) • u‖^2+(16/11:ℝ)*‖u‖^2 := by
  simp only [norm_sub_sq_real, norm_smul, inner_smul_left,
    inner_smul_right, Real.norm_eq_abs, real_inner_comm q u]
  norm_num <;> ring

theorem coupled_projection_loss_credit (u q : E) :
    (16/11:ℝ)*‖u‖^2 ≤ ‖(2:ℝ) • u-q‖^2+(4/7:ℝ)*‖q‖^2 := by
  have h := coupled_projection_exact_square u q
  nlinarith [sq_nonneg ‖q-(14/11:ℝ) • u‖]

theorem coupled_production_pays_retained_response (u q : E)
    {I W r t b xi s g k affine : ℝ}
    (hShifted : I ≤ W+r+t/2-b/4-xi/2-4*s-‖(2:ℝ) • u-q‖^2)
    (hPaid : xi/2+(16/11:ℝ)*‖u‖^2+4*s+b/4 ≥
      W-r+t/2-(27/4:ℝ)*g-(8/7:ℝ)*(1+Real.sqrt 2)*k-
        (2/7:ℝ)*Real.sqrt 2*affine) :
    I ≤ 2*r+(27/4:ℝ)*g+(8/7:ℝ)*(1+Real.sqrt 2)*k+
      (2/7:ℝ)*Real.sqrt 2*affine+(4/7:ℝ)*‖q‖^2 := by
  have hc := coupled_projection_loss_credit u q
  linarith

theorem coupled_skew_only_sufficient_production (u q : E)
    {I W r t b xi s g k affine : ℝ}
    (hSkew : s ≤ ‖u‖^2)
    (hShifted : I ≤ W+r+t/2-b/4-xi/2-4*s-‖(2:ℝ) • u-q‖^2)
    (hPaid : xi/2+(60/11:ℝ)*s+b/4 ≥
      W-r+t/2-(27/4:ℝ)*g-(8/7:ℝ)*(1+Real.sqrt 2)*k-
        (2/7:ℝ)*Real.sqrt 2*affine) :
    I ≤ 2*r+(27/4:ℝ)*g+(8/7:ℝ)*(1+Real.sqrt 2)*k+
      (2/7:ℝ)*Real.sqrt 2*affine+(4/7:ℝ)*‖q‖^2 := by
  apply coupled_production_pays_retained_response u q hShifted
  linarith

end KLSConstantImprovement.SourceCoupledMainResponseLossCredit
#print axioms KLSConstantImprovement.SourceCoupledMainResponseLossCredit.coupled_projection_exact_square
#print axioms KLSConstantImprovement.SourceCoupledMainResponseLossCredit.coupled_projection_loss_credit
#print axioms KLSConstantImprovement.SourceCoupledMainResponseLossCredit.coupled_production_pays_retained_response
#print axioms KLSConstantImprovement.SourceCoupledMainResponseLossCredit.coupled_skew_only_sufficient_production
