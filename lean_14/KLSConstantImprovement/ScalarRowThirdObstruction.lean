import KLSConstantImprovement.JointRowMainCubicPayoff

/-! Rational consequences of one actual canonical scalar-row interval
certificate. Kernel/flux identification, directed interval integration
and the smooth full-support Fatou witness remain explicit paper inputs. -/
noncomputable section
namespace KLSConstantImprovement.ScalarRowThirdObstruction

theorem certified_scalar_row_third_violation
    {theta W : ℝ} (htheta : (169/200:ℝ) ≤ theta)
    (hW : W ≤ (1259/500:ℝ)) : (1/200:ℝ) < theta-W/3 := by
  linarith

theorem scalar_gram_gap_does_not_pay_row_third
    {theta W g deltaT deltaD : ℝ}
    (htheta : (169/200:ℝ) ≤ theta) (hW : W ≤ (1259/500:ℝ))
    (hScalar : deltaT=deltaD) (hg : g=deltaT-deltaD) :
    theta > W/3+4*g := by
  have h := certified_scalar_row_third_violation htheta hW
  linarith

theorem regular_fatou_witness_rational_violation
    {theta W : ℝ} (htheta : (211/250:ℝ) ≤ theta)
    (hW : W ≤ (2519/1000:ℝ)) : (1/250:ℝ) < theta-W/3 := by
  linarith

theorem curvature_paid_candidate_survives_scalar_guard
    {theta source : ℝ} (htheta : theta ≤ (106/125:ℝ))
    (hSource : (1483/1000:ℝ) ≤ source) : theta < source := by
  linarith

end KLSConstantImprovement.ScalarRowThirdObstruction
#print axioms KLSConstantImprovement.ScalarRowThirdObstruction.certified_scalar_row_third_violation
#print axioms KLSConstantImprovement.ScalarRowThirdObstruction.scalar_gram_gap_does_not_pay_row_third
#print axioms KLSConstantImprovement.ScalarRowThirdObstruction.regular_fatou_witness_rational_violation
#print axioms KLSConstantImprovement.ScalarRowThirdObstruction.curvature_paid_candidate_survives_scalar_guard
