import Mathlib

/-! Exact scalar consequence of the canonical Dirichlet Killing-pair
formula. The actual source/law/field identification is an explicit input,
not a formalized original-law or matrix-lift theorem in this module. -/
noncomputable section
namespace KLSConstantImprovement.OriginalKillingLiftObstructionScalar

theorem positive_killing_pair {p : ℝ} (hp : 0 < p) :
    0 < 2*p/(p+2)^2 := by
  have hp2 : 0 < p+2 := by linarith
  exact div_pos (by positivity) (sq_pos_of_pos hp2)

theorem scoped_killing_pair_nonzero {p pair : ℝ}
    (hp : 0 < p) (hpair : pair = 2*p/(p+2)^2) : pair ≠ 0 := by
  rw [hpair]
  exact ne_of_gt (positive_killing_pair hp)

end KLSConstantImprovement.OriginalKillingLiftObstructionScalar
#print axioms KLSConstantImprovement.OriginalKillingLiftObstructionScalar.positive_killing_pair
#print axioms KLSConstantImprovement.OriginalKillingLiftObstructionScalar.scoped_killing_pair_nonzero
