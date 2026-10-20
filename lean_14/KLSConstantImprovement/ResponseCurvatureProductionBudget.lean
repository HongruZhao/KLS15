import KLSConstantImprovement.SourceShiftedResolventResponseUpper

/-! Quantitative ROW source-curvature consequences of the existing actual
shifted-resolvent and metric identities. The source S=P+Gamma, entrywise
resolvent, fixed dual row congruences and scalar geometric rows are explicit
analytic bindings. These finite consequences do not formalize that geometry,
bound a column contraction or assert a new cubic variance/Poincare endpoint. -/
noncomputable section
namespace KLSConstantImprovement.ResponseCurvatureProductionBudget
open SourceMatchedMeanResponseConditionalPayoff

theorem joint_curvature_production_identity
    {m w theta xi force prod extra r filtered : ℝ}
    (hMetric : 2*m = 2*w+theta-xi)
    (hResolvent : m = 2*force-prod)
    (hForcingIdentity : 2*force = w+r-filtered)
    (hExtra : extra = 2*prod-xi) :
    theta+extra = 2*r-2*filtered := by
  linarith

theorem retained_curvature_production_upper
    {m w theta xi force prod extra r t : ℝ}
    (hMetric : 2*m = 2*w+theta-xi)
    (hResolvent : m = 2*force-prod)
    (hForcing : 2*force ≤ w+r+t/2)
    (hExtra : extra = 2*prod-xi) :
    theta+extra ≤ 2*r+t := by
  linarith

theorem matched_joint_curvature_production_bound
    {theta extra N g r t : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hBudget : theta+extra ≤ 2*r+t) :
    theta+extra ≤ (2+Real.sqrt 5)*(N-g/2) := by
  have hp := Real.sqrt_nonneg (5:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hc : 0 ≤ (2+Real.sqrt 5)-2 := by nlinarith
  have hcoef : (2:ℝ)^2+(1:ℝ)^2 ≤ ((2+Real.sqrt 5)-2)^2 := by
    nlinarith
  have h := disk_linear_support hneff hc hcoef hdisk
  nlinarith

theorem rational_joint_curvature_production_bound
    {theta extra N g r t : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hBudget : theta+extra ≤ 2*r+t) :
    theta+extra ≤ (17/4:ℝ)*(N-g/2) := by
  have h := matched_joint_curvature_production_bound hneff hdisk hBudget
  have hp := Real.sqrt_nonneg (5:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hu : Real.sqrt (5:ℝ) ≤ 9/4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hu hneff
  nlinarith

theorem geometric_row_curvature_weighted_split
    {thetaU thetaF thetaZ cross : ℝ}
    (hSplit : 4*thetaU = thetaF+2*cross+thetaZ)
    (hGram : 0 ≤ thetaF+thetaZ/4-cross) :
    thetaU ≤ (3/4:ℝ)*thetaF+(3/8:ℝ)*thetaZ := by
  linarith

theorem geometric_row_curvature_matched_bound
    {thetaU thetaF thetaZ extra W N g r t k : ℝ}
    (hneff : 0 ≤ N-g/2)
    (hdisk : (r-(N-g/2))^2+t^2 ≤ (N-g/2)^2)
    (hSplit : thetaU ≤ (3/4:ℝ)*thetaF+(3/8:ℝ)*thetaZ)
    (hResponse : thetaF+extra ≤ 2*r+t)
    (hAffine : thetaZ ≤ 2*W)
    (hDirect : W+2*k ≤ 3*(r+t)) :
    thetaU ≤ ((15+3*Real.sqrt 41)/4)*(N-g/2)
      -(3/2:ℝ)*k-(3/4:ℝ)*extra := by
  have hp := Real.sqrt_nonneg (41:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 41 by norm_num)
  have hc : 0 ≤ (15+3*Real.sqrt 41)/4-(15/4:ℝ) := by nlinarith
  have hcoef : (15/4:ℝ)^2+(3:ℝ)^2 ≤
      ((15+3*Real.sqrt 41)/4-(15/4:ℝ))^2 := by nlinarith
  have h := disk_linear_support hneff hc hcoef hdisk
  nlinarith

end KLSConstantImprovement.ResponseCurvatureProductionBudget
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.joint_curvature_production_identity
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.retained_curvature_production_upper
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.matched_joint_curvature_production_bound
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.rational_joint_curvature_production_bound
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.geometric_row_curvature_weighted_split
#print axioms KLSConstantImprovement.ResponseCurvatureProductionBudget.geometric_row_curvature_matched_bound
