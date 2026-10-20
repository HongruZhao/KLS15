import KLSConstantImprovement.FilteredSourceCrossConvexTiltObstruction

/-! Finite consequences of the SAME original exponential convex-density
tangent. The actual kernel, closed shifted resolvent and p3 derivative
identifications are analytic inputs, not formalized by these scalars. -/
noncomputable section
namespace KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment

theorem curvature_tangent_payment
    {c p a b : ℝ} (hc : 9*c = -a+2*b) (hp : p=a) :
    c+p/9 = 2*b/9 := by linarith

theorem curvature_tangent_payment_nonnegative
    {c p a b : ℝ} (hc : 9*c = -a+2*b) (hp : p=a)
    (hb : 0 ≤ b) : 0 ≤ c+p/9 := by linarith

theorem correlated_production_tangent
    {c p a b theta extra r : ℝ}
    (hc : 9*c = -a+2*b) (hp : p=a)
    (hproduction : theta+extra = 2*r-2*c) :
    theta+extra-2*r-2*p/9 = -4*b/9 := by linarith

theorem quadratic_correlated_production_tangent
    {c p theta extra r : ℝ} (hc : 9*c = -12) (hp : p=24)
    (hproduction : theta+extra = 2*r-2*c) :
    c+p/9 = 4/3 ∧ theta+extra-2*r-2*p/9 = -8/3 := by
  constructor <;> linarith

end KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment
#print axioms KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment.curvature_tangent_payment
#print axioms KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment.curvature_tangent_payment_nonnegative
#print axioms KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment.correlated_production_tangent
#print axioms KLSConstantImprovement.FilteredSourceCrossLocalCurvaturePayment.quadratic_correlated_production_tangent
