import Mathlib

/-! The actual source regression component is q_K/4. Quadratic8,
one-slot8 and the accepted cubic signed bound16/3 pay its variance.
This file keeps those existing analytic/tensor inputs explicit; it
does not bound the remaining signed same-source response correction. -/
noncomputable section
namespace KLSConstantImprovement.OriginalSourceLinearResponseSlack

theorem linear_response_exact_slack {N B2 signed dK Ilin : ℝ}
    (hcomponent : Ilin=(B2+signed)/4-dK/16) :
    (10/3 : ℝ)*N-Ilin = dK/16+(8*N-B2)/4+((16/3 : ℝ)*N-signed)/4 := by
  rw [hcomponent]
  ring

theorem linear_response_original_cap {N B2 signed dK Ilin : ℝ}
    (hcomponent : Ilin=(B2+signed)/4-dK/16)
    (hB : B2 ≤ 8*N) (hS : signed ≤ (16/3 : ℝ)*N) (hd : 0 ≤ dK) :
    Ilin ≤ (10/3 : ℝ)*N := by
  linarith

theorem linear_slack_budget_exact {N B2 signed dK Ilin : ℝ}
    (hcomponent : Ilin=(B2+signed)/4-dK/16) :
    (7/2 : ℝ)*N-Ilin = N/6+dK/16+(8*N-B2)/4+((16/3 : ℝ)*N-signed)/4 := by
  rw [hcomponent]
  ring

end KLSConstantImprovement.OriginalSourceLinearResponseSlack
#print axioms KLSConstantImprovement.OriginalSourceLinearResponseSlack.linear_response_exact_slack
#print axioms KLSConstantImprovement.OriginalSourceLinearResponseSlack.linear_response_original_cap
#print axioms KLSConstantImprovement.OriginalSourceLinearResponseSlack.linear_slack_budget_exact
