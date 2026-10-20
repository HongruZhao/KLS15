import KLSConstantImprovement.OrdinaryRowRightRegression

/-! Same-source ordinary/geometric quadratic row coupling. The actual weak
row equations, compact form-domain pairing, two endpoint Bochner records
and mean regression are paper inputs. The right-H projection does not
order the extra-H Hessian norms or prove a numerical response budget. -/
noncomputable section
namespace KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem geometric_row_projection (ordinary geometric : E)
    (hpair : inner ℝ ordinary geometric = ‖geometric‖^2) :
    inner ℝ (ordinary-geometric) geometric = 0 ∧
      ‖ordinary‖^2 = ‖geometric‖^2+‖ordinary-geometric‖^2 := by
  constructor
  · rw [inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  · rw [norm_sub_sq_real]
    linarith

theorem geometric_hessian_loss_decomposition (ordinary geometric : E)
    {datum h loss j : ℝ}
    (hpair : inner ℝ ordinary geometric = ‖geometric‖^2)
    (hOrdinary : datum = h+‖ordinary‖^2)
    (hGeometric : ‖geometric‖^2 = j)
    (hEndpoint : datum = loss+j) :
    loss = h+‖ordinary-geometric‖^2 := by
  have hProjection := (geometric_row_projection ordinary geometric hpair).2
  linarith

theorem right_response_cost_difference (ordinary geometric : E)
    {j h loss : ℝ}
    (hLoss : loss = h+‖ordinary-geometric‖^2) :
    (j-4*h)-(j-4*loss) = 4*‖ordinary-geometric‖^2 ∧
      j-4*loss ≤ j-4*h := by
  have hn := sq_nonneg (‖ordinary-geometric‖)
  constructor <;> linarith

theorem combined_gradient_and_third_moment_charge (ordinary geometric : E)
    {j h loss third : ℝ}
    (hLoss : loss = h+‖ordinary-geometric‖^2)
    (hRegression : 0 ≤ j-4*loss-third/4) :
    4*h+4*‖ordinary-geometric‖^2+third/4 ≤ j := by
  linarith

end KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux

#print axioms KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux.geometric_row_projection
#print axioms KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux.geometric_hessian_loss_decomposition
#print axioms KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux.right_response_cost_difference
#print axioms KLSConstantImprovement.CoupledOrdinaryGeometricRowFlux.combined_gradient_and_third_moment_charge
