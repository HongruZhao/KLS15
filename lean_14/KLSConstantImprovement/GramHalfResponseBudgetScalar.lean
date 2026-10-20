import KLSConstantImprovement.DeficitCurvatureScalar

/-! Algebraic payment once a common original-law Hessian realization and
the finite Gram-half positive form have supplied the displayed identities.
Those analytic and finite-matrix statements remain explicit inputs here.
No actual-law response estimate or dimension-free CP improvement is asserted. -/
noncomputable section
namespace KLSConstantImprovement.GramHalfResponseBudgetScalar

theorem moment_gap_remainder {d gap deltaT deltaA residual : ℝ}
    (hgap : gap = 4*deltaT-4*deltaA-4*residual) :
    d-gap = (d-4*deltaT)+4*deltaA+4*residual := by
  rw [hgap]
  ring

theorem moment_gap_paid_by_diagonal {d gap deltaT deltaA residual : ℝ}
    (hfinite : 0 ≤ gap) (hA : 0 ≤ deltaA) (hresidual : 0 ≤ residual)
    (hpaid : 4*deltaT ≤ d)
    (hgap : gap = 4*deltaT-4*deltaA-4*residual) :
    0 ≤ gap ∧ gap ≤ d ∧ deltaA ≤ deltaT ∧ deltaA ≤ d/4 := by
  refine ⟨hfinite,?_,?_,?_⟩ <;> linarith

theorem moment_gap_paid_by_distinct_slots {N R3 gap deltaA rootResidual : ℝ}
    (hfinite : 0 ≤ gap) (hA : 0 ≤ deltaA) (hresidual : 0 ≤ rootResidual)
    (hslot : 4*N-R3 = 4*deltaA+4*rootResidual+gap) :
    gap ≤ 4*N-R3 ∧ deltaA ≤ (4*N-R3)/4 := by
  constructor <;> linarith

theorem joint_moment_gap_payment {N R3 d gap deltaT deltaA residual rootResidual : ℝ}
    (hfinite : 0 ≤ gap) (hA : 0 ≤ deltaA)
    (hresidual : 0 ≤ residual) (hrootResidual : 0 ≤ rootResidual)
    (hpaid : 4*deltaT ≤ d)
    (hgap : gap = 4*deltaT-4*deltaA-4*residual)
    (hslot : 4*N-R3 = 4*deltaA+4*rootResidual+gap) :
    0 ≤ gap ∧ gap ≤ min d (4*N-R3) ∧
      deltaA ≤ min d (4*N-R3)/4 := by
  obtain ⟨hg0,hgd,_,hAd⟩ := moment_gap_paid_by_diagonal hfinite hA hresidual hpaid hgap
  obtain ⟨hgs,hAs⟩ := moment_gap_paid_by_distinct_slots hfinite hA hrootResidual hslot
  refine ⟨hg0,le_min hgd hgs,?_⟩
  rcases le_total d (4*N-R3) with h | h
  · simpa only [min_eq_left h] using hAd
  · simpa only [min_eq_right h] using hAs

theorem normalized_response_payment {d deltaT deltaA excess response : ℝ}
    (hA : 0 ≤ deltaA) (hpaid : 4*deltaT ≤ d)
    (hexcess : excess = deltaT-deltaA)
    (hresponse : response ≤ 2*excess) :
    response ≤ d/2 := by
  linarith

end KLSConstantImprovement.GramHalfResponseBudgetScalar
#print axioms KLSConstantImprovement.GramHalfResponseBudgetScalar.moment_gap_remainder
#print axioms KLSConstantImprovement.GramHalfResponseBudgetScalar.moment_gap_paid_by_diagonal
#print axioms KLSConstantImprovement.GramHalfResponseBudgetScalar.moment_gap_paid_by_distinct_slots
#print axioms KLSConstantImprovement.GramHalfResponseBudgetScalar.joint_moment_gap_payment
#print axioms KLSConstantImprovement.GramHalfResponseBudgetScalar.normalized_response_payment
