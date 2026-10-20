import KLSConstantImprovement.ActualResponseProductionAlgebra405

/-! Exact whitening of the two compatible response-production squares.
The first square uses the actual Poisson Hessian rather than separately
requiring the third tensor contracted with the unbounded Poisson flux. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualResponseCompletionWhitening405
open ActualResponseProductionAlgebra405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem completionLeft_whitening (H J S R D Nu Nz T : Matrix (Fin n) (Fin n) ℝ)
    (hSJ : S * J = R) (hHR : H * R = S) (hRH : R * H = S) :
    S * completionLeft H J ((2 : ℝ) • Nu - Nz) ((2 : ℝ) • D - T * H) T * R =
      (2 : ℝ) • (R * (H * D + Nu) * R) - (2 : ℝ) • (S * T * S) - R * Nz * R := by
  have hC : R * (H * D + Nu) * R = S * D * R + R * Nu * R := by
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hRH]
  have hTH : S * (T * H) * R = S * T * S := by
    simp only [Matrix.mul_assoc, hHR]
  have hJN (A : Matrix (Fin n) (Fin n) ℝ) : S * (J * A) * R = R * A * R := by
    simp only [← Matrix.mul_assoc, hSJ]
  rw [hC]
  simp only [completionLeft, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  rw [hTH, hJN Nu, hJN Nz]
  module

theorem completionRight_whitening (H S R D T : Matrix (Fin n) (Fin n) ℝ)
    (hHR : H * R = S) :
    S * completionRight H ((2 : ℝ) • D - T * H) T * R =
      (2 : ℝ) • (S * D * R) := by
  have he : completionRight H ((2 : ℝ) • D - T * H) T = (2 : ℝ) • D := by
    unfold completionRight
    abel
  rw [he, Matrix.mul_smul, Matrix.smul_mul]

theorem trace_product_similarity (S R A B : Matrix (Fin n) (Fin n) ℝ)
    (hRS : R * S = 1) :
    ((S * A * R) * (S * B * R)).trace = (A * B).trace := by
  have hp : (S * A * R) * (S * B * R) = S * (A * B) * R := by
    calc
      _ = S * A * (R * S) * B * R := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRS]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hp, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hRS, Matrix.one_mul]

end KLSConstantImprovement.ActualResponseCompletionWhitening405

#print axioms KLSConstantImprovement.ActualResponseCompletionWhitening405.completionLeft_whitening
#print axioms KLSConstantImprovement.ActualResponseCompletionWhitening405.completionRight_whitening
#print axioms KLSConstantImprovement.ActualResponseCompletionWhitening405.trace_product_similarity
