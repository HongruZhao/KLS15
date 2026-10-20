import KLSConstantImprovement.ActualSourceMeanGramCongruence405

/-! Literal row transformation of a fixed slice family. These identities
change only the finite tensor row coefficients; the measure, diffusion
coordinates and scalar generator remain those of the original source. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualTensorRowCongruence405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405
open ActualSourceMeanGramOrder405 ActualSourceMeanGramCongruence405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

def rowCongruentSlices (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ a, S a i • T a

theorem rowCongruentSlices_symmetric
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : (rowCongruentSlices T S i).IsSymm :=
  sliceCombination_symmetric T hT (fun a => S a i)

theorem matrixTraceGram_rowCongruentSlices
    (H : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    matrixTraceGram H (rowCongruentSlices T S) = S.transpose * matrixTraceGram H T * S := by
  ext i j
  simp only [matrixTraceGram, rowCongruentSlices, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem coefficientGram_rowCongruentSlices
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    sourceCoefficientGram (rowCongruentSlices T S) = congruentCoefficientGram T S :=
  matrixTraceGram_rowCongruentSlices 1 T S

theorem actual_meanGram_rowCongruentSlices (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    sourceMeanGram d (rowCongruentSlices T S) = congruentMeanGram d T S := by
  ext i j
  have he (x : Space n) : matrixTraceGram (coordinateHessian d.potential x)
      (rowCongruentSlices T S) i j = ∑ b, ∑ a,
      S a i * matrixTraceGram (coordinateHessian d.potential x) T a b * S b j := by
    rw [matrixTraceGram_rowCongruentSlices]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  change (∫ x, matrixTraceGram (coordinateHessian d.potential x)
    (rowCongruentSlices T S) i j ∂potentialMeasure d.potential) = _
  simp_rw [he]
  have hi (a b : Fin n) : Integrable (fun x =>
      S a i * matrixTraceGram (coordinateHessian d.potential x) T a b * S b j)
      (potentialMeasure d.potential) :=
    ((actual_traceGram_integrable d T a b).const_mul (S a i)).mul_const (S b j)
  rw [integral_finsetSum Finset.univ (fun b _ =>
    integrable_finsetSum Finset.univ fun a _ => hi a b)]
  simp_rw [integral_finsetSum Finset.univ (fun a _ => hi a _), integral_mul_const,
    integral_const_mul]
  simp only [congruentMeanGram, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    sourceMeanGram]

end KLSConstantImprovement.ActualTensorRowCongruence405
#print axioms KLSConstantImprovement.ActualTensorRowCongruence405.rowCongruentSlices_symmetric
#print axioms KLSConstantImprovement.ActualTensorRowCongruence405.matrixTraceGram_rowCongruentSlices
#print axioms KLSConstantImprovement.ActualTensorRowCongruence405.coefficientGram_rowCongruentSlices
#print axioms KLSConstantImprovement.ActualTensorRowCongruence405.actual_meanGram_rowCongruentSlices
