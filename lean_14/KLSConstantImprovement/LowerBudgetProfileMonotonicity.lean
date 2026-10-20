import KLSConstantImprovement.RawCubicWeightedBudget

/-! Lowering the SAME full previous budget improves every all-rank
generator coefficient. This transfers the already proved infinite-tail
certificate; no finite-degree truncation or new law estimate is used. -/
noncomputable section
namespace KLSConstantImprovement.LowerBudgetProfileMonotonicity
open TriplePositiveEnergyWeightedBudget
set_option backward.isDefEq.respectTransparency false

def withBudget (P : Parameters) (D : ℝ) : Parameters := { P with C := D }

theorem coefficient_withBudget (P : Parameters) (D : ℝ) (d : ℕ) :
    coefficient (withBudget P D) d = coefficient P d +
      (P.K * (P.C - D) / P.young d) * (d : ℝ) ^ 2 := by
  simp only [coefficient, withBudget, TriplePositiveEnergyWeightedGenerator.coefficient,
    TriplePositiveEnergyWeightedGenerator.cost]
  simp only [div_eq_mul_inv]
  ring

theorem head_withBudget (P : Parameters) (D : ℝ) :
    head (withBudget P D) = head P + (P.K * (D - P.C) / P.young 2) * 4 := by
  simp only [head, withBudget, TriplePositiveEnergyWeightedGenerator.head,
    TriplePositiveEnergyWeightedGenerator.cost]
  norm_num only [Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  ring

theorem coefficient_le_lowerBudget (P : Parameters) {D : ℝ}
    (hK : 0 ≤ P.K) (hD : D ≤ P.C) (d : ℕ) (hy : 0 < P.young d) :
    coefficient P d ≤ coefficient (withBudget P D) d := by
  rw [coefficient_withBudget]
  apply le_add_of_nonneg_right
  exact mul_nonneg
    (div_nonneg (mul_nonneg hK (sub_nonneg.mpr hD)) hy.le) (sq_nonneg _)

end KLSConstantImprovement.LowerBudgetProfileMonotonicity
#print axioms KLSConstantImprovement.LowerBudgetProfileMonotonicity.coefficient_withBudget
#print axioms KLSConstantImprovement.LowerBudgetProfileMonotonicity.head_withBudget
#print axioms KLSConstantImprovement.LowerBudgetProfileMonotonicity.coefficient_le_lowerBudget
