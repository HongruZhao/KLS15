import KLSConstantImprovement.LowerBudgetProfileMonotonicity

/-! A quantitative certificate-slack gain when the full previous budget
is lowered. Every weight and generator parameter stays fixed. -/
noncomputable section
namespace KLSConstantImprovement.LowerBudgetProfileSlack
open TriplePositiveEnergyWeightedBudget LowerBudgetProfileMonotonicity
set_option backward.isDefEq.respectTransparency false

theorem coefficient_slack_lower (P : Parameters) {D σ : ℝ} (d : ℕ)
    (hK : 0 ≤ P.K) (hD : D ≤ P.C) (hy : 0 < P.young d)
    (hσ : σ * P.young d ≤ (d : ℝ) ^ 2)
    (hOld : P.c ≤ coefficient P d) :
    P.c + σ * P.K * (P.C - D) ≤ coefficient (withBudget P D) d := by
  have hrat : σ ≤ (d : ℝ) ^ 2 / P.young d := (le_div_iff₀ hy).mpr hσ
  have hm := mul_le_mul_of_nonneg_left hrat (mul_nonneg hK (sub_nonneg.mpr hD))
  have he : P.K * (P.C - D) * ((d : ℝ) ^ 2 / P.young d) =
      (P.K * (P.C - D) / P.young d) * (d : ℝ) ^ 2 := by ring
  rw [he] at hm
  rw [coefficient_withBudget]
  nlinarith

end KLSConstantImprovement.LowerBudgetProfileSlack
#print axioms KLSConstantImprovement.LowerBudgetProfileSlack.coefficient_slack_lower
