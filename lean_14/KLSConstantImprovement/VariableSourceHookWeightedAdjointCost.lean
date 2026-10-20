import KLSConstantImprovement.SourceHookMainCharge

/-! The first-derivative weighted-adjoint cost of a variable source hook.
Actual compact-source integration identifies the signed scalar A and
metric field k. The compatible null pairing and the original source
Riesz representation remain explicit. No uniform cost premise is claimed. -/
noncomputable section
namespace KLSConstantImprovement.VariableSourceHookWeightedAdjointCost

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The signed derivative budget becomes a norm cost after the metric term. -/
theorem weighted_adjoint_cost_square (w k : F) {A : ℝ}
    (hcost : ‖w‖^2 = A + inner ℝ w k) :
    ‖w‖^2 + ‖w-k‖^2 = 2*A + ‖k‖^2 := by
  rw [norm_sub_sq_real]
  nlinarith

theorem weighted_adjoint_cost_cap (w k : F) {A : ℝ}
    (hcost : ‖w‖^2 = A + inner ℝ w k) :
    ‖w‖^2 ≤ 2*A + ‖k‖^2 := by
  have h := weighted_adjoint_cost_square w k hcost
  nlinarith [sq_nonneg ‖w-k‖]

theorem weighted_adjoint_budget_nonneg (w k : F) {A : ℝ}
    (hcost : ‖w‖^2 = A + inner ℝ w k) :
    0 ≤ 2*A + ‖k‖^2 := by
  have h := weighted_adjoint_cost_cap w k hcost
  nlinarith [sq_nonneg ‖w‖]

/-- A cost upper bound preserves a paid Schur charge, including zero cost. -/
theorem variable_hook_schur_budget {Q budget gap pairing : ℝ}
    (hgap : 0 ≤ gap) (hcap : Q ≤ budget)
    (hschur : pairing^2 ≤ Q*gap) :
    pairing^2 ≤ budget*gap := by
  have h := mul_nonneg (sub_nonneg.mpr hcap) hgap
  nlinarith

theorem variable_hook_zero_budget {budget gap pairing : ℝ}
    (hbudget : budget = 0)
    (hschur : pairing^2 ≤ budget*gap) :
    pairing = 0 := by
  rw [hbudget, zero_mul] at hschur
  nlinarith [sq_nonneg pairing]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Same scalar data and curvature projection as the source Riesz estimate. -/
theorem variable_hook_paid_variance (a f : E) {budget J pairing V : ℝ}
    (hbudget : 0 ≤ budget)
    (hvariance : V = 9*‖a+f‖^2)
    (hschur : pairing^2 ≤ budget*(J-‖a‖^2)) :
    budget*V + 9*pairing^2 ≤
      budget*(9*J+18*inner ℝ a f+9*‖f‖^2) := by
  rw [norm_add_sq_real] at hvariance
  have hscaled := congrArg (fun x : ℝ => budget*x) hvariance
  nlinarith

theorem gamma_four_weighted_hook_budget :
    (8:ℝ) = 4+4-1/6+1/6 ∧
    (8:ℝ)+8 = 2*(47/6)+1/3 ∧
    (1/2:ℝ)^2 / 16 = 1/64 := by norm_num

end KLSConstantImprovement.VariableSourceHookWeightedAdjointCost
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.weighted_adjoint_cost_square
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.weighted_adjoint_cost_cap
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.weighted_adjoint_budget_nonneg
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.variable_hook_schur_budget
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.variable_hook_zero_budget
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.variable_hook_paid_variance
#print axioms KLSConstantImprovement.VariableSourceHookWeightedAdjointCost.gamma_four_weighted_hook_budget
