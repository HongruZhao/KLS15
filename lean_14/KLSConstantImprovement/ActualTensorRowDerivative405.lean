import KLSConstantImprovement.ActualDirectCubicCoefficients405
import KLSConstantImprovement.ActualTensorRowCongruence405

/-! Literal row congruence of the raw Gram derivative. The source metric
and derivative direction are unchanged; only deterministic row coefficients
are transformed. No form realization or analytic witness is supplied. -/
noncomputable section
open Matrix
namespace KLSConstantImprovement.ActualTensorRowDerivative405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualDirectCubicWhitening405 ActualDirectCubicCoefficients405 ActualTensorRowCongruence405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem rawGramDerivative_rowCongruentSlices (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (C S : Matrix (Fin n) (Fin n) ℝ) :
    rawGramDerivative H (rowCongruentSlices T S) C = S.transpose * rawGramDerivative H T C * S := by
  have hsym (U : Fin n → Matrix (Fin n) (Fin n) ℝ) :
      rawGramDerivative H U C = directLinear H U C + (directLinear H U C).transpose := by
    ext i j
    exact rawGramDerivative_eq_direct_symmetrization H U C i j
  have hrow : rowCongruentSlices T S = mixFamily S.transpose T := rfl
  rw [hsym, hsym, hrow, directLinear_mix_rows]
  simp only [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

end KLSConstantImprovement.ActualTensorRowDerivative405

#print axioms KLSConstantImprovement.ActualTensorRowDerivative405.rawGramDerivative_rowCongruentSlices
