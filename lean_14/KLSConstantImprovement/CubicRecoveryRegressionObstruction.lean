import KLSConstantImprovement.ActualCubicRegressionSectorCriteria

/-! Scalar regression-budget negativity at the exact exponential moment
data. The original-law moment identification is documented separately;
this module checks the universal polynomial identity and coefficient
homogeneity, preserving the sufficient implications in the imported module. -/
noncomputable section
namespace KLSConstantImprovement.CubicRecoveryRegressionObstruction
set_option maxHeartbeats 1500000

def exponentialDenominator (C : ℝ) : ℝ := 4*C-8-4/(C-1)
def exponentialNumerator (C : ℝ) : ℝ := 36-12*C+12/(C-1)
def exponentialBudget (C target : ℝ) : ℝ :=
  (C-1)*exponentialDenominator C*(target-72*C)+
    36*exponentialDenominator C+(C-1)*(exponentialNumerator C)^2

def exponentialHomogeneousBudget (C target t b : ℝ) : ℝ :=
  (C-1)*(b^2*exponentialDenominator C)*(target*t^2-72*C*t^2)+
    (b^2*exponentialDenominator C)*(36*t^2)+
      (C-1)*(t*b*exponentialNumerator C)^2

theorem exponentialBudget_raw_factorization {C : ℝ} (hC : C-1 ≠ 0) :
    exponentialBudget C 336 =
      -48*(3*(C-7)^3+38*(C-7)^2+139*(C-7)+127) := by
  unfold exponentialBudget exponentialDenominator exponentialNumerator
  field_simp [hC]
  ring

theorem exponentialBudget_additive_factorization {C : ℝ} (hC : C-1 ≠ 0) :
    exponentialBudget C 308 =
      -16*(9*(C-7)^3+121*(C-7)^2+494*(C-7)+584) := by
  unfold exponentialBudget exponentialDenominator exponentialNumerator
  field_simp [hC]
  ring

theorem exponentialBudget_raw_negative {C : ℝ} (hC : 7 ≤ C) :
    exponentialBudget C 336 < 0 := by
  rw [exponentialBudget_raw_factorization (by linarith : C-1 ≠ 0)]
  have hy : 0 ≤ C-7 := by linarith
  have h2 := sq_nonneg (C-7)
  have h3 := pow_nonneg hy 3
  nlinarith

theorem exponentialBudget_additive_negative {C : ℝ} (hC : 7 ≤ C) :
    exponentialBudget C 308 < 0 := by
  rw [exponentialBudget_additive_factorization (by linarith : C-1 ≠ 0)]
  have hy : 0 ≤ C-7 := by linarith
  have h2 := sq_nonneg (C-7)
  have h3 := pow_nonneg hy 3
  nlinarith

theorem exponentialHomogeneousBudget_eq (C target t b : ℝ) :
    exponentialHomogeneousBudget C target t b = t^2*b^2*exponentialBudget C target := by
  unfold exponentialHomogeneousBudget exponentialBudget
  ring

theorem exponentialHomogeneousBudget_raw_negative {C t b : ℝ}
    (hC : 7 ≤ C) (ht : t ≠ 0) (hb : b ≠ 0) :
    exponentialHomogeneousBudget C 336 t b < 0 := by
  rw [exponentialHomogeneousBudget_eq]
  have ht2 : 0 < t^2 := sq_pos_of_ne_zero ht
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  exact mul_neg_of_pos_of_neg (mul_pos ht2 hb2) (exponentialBudget_raw_negative hC)

theorem exponentialHomogeneousBudget_additive_negative {C t b : ℝ}
    (hC : 7 ≤ C) (ht : t ≠ 0) (hb : b ≠ 0) :
    exponentialHomogeneousBudget C 308 t b < 0 := by
  rw [exponentialHomogeneousBudget_eq]
  have ht2 : 0 < t^2 := sq_pos_of_ne_zero ht
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  exact mul_neg_of_pos_of_neg (mul_pos ht2 hb2) (exponentialBudget_additive_negative hC)

end KLSConstantImprovement.CubicRecoveryRegressionObstruction
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialBudget_raw_factorization
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialBudget_additive_factorization
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialBudget_raw_negative
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialBudget_additive_negative
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialHomogeneousBudget_eq
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialHomogeneousBudget_raw_negative
#print axioms KLSConstantImprovement.CubicRecoveryRegressionObstruction.exponentialHomogeneousBudget_additive_negative
