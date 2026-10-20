import KLSConstantImprovement.ActualSourceMeanGramOrder405

/-! The actual mean Gram bound survives every constant congruence.
The squared Hilbert--Schmidt mean is paid by its positive trace pairing.
Both mean matrices are literal functions of the constructed source and
fixed tensor; no normalized mean/order witness is supplied. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceMeanGramCongruence405
open KLS ActualBoundedCanonicalSource ActualSourceMeanGram405 ActualSourceMeanGramOrder405
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def congruentMeanGram (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := S.transpose * sourceMeanGram d T * S

def congruentCoefficientGram (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S.transpose * sourceCoefficientGram T * S

theorem actual_congruent_meanGram_posSemidef (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (S : Matrix (Fin n) (Fin n) ℝ) : (congruentMeanGram d T S).PosSemidef := by
  simpa only [congruentMeanGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (actual_meanGram_posSemidef d T hT).conjTranspose_mul_mul_same S

theorem actual_congruent_meanGram_order (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    ((2 : ℝ) • congruentCoefficientGram T S - congruentMeanGram d T S).PosSemidef := by
  have h := (actual_meanGram_le_two_coefficientGram d hiso T hT).conjTranspose_mul_mul_same S
  simpa only [congruentCoefficientGram, congruentMeanGram,
    Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul,
    Matrix.mul_smul, Matrix.smul_mul] using h

theorem actual_congruent_meanGram_square_bound (d : SourceData μ) (hiso : IsIsotropic μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm)
    (S : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq (congruentMeanGram d T S) ≤
      2 * (congruentMeanGram d T S * congruentCoefficientGram T S).trace := by
  have hp := trace_mul_nonneg_of_posSemidef
    (actual_congruent_meanGram_posSemidef d T hT S)
    (actual_congruent_meanGram_order d hiso T hT S)
  rw [mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hp
  rw [matrixFrobeniusSq_eq_trace_sq
    (actual_congruent_meanGram_posSemidef d T hT S).isHermitian.isSymm]
  linarith

end KLSConstantImprovement.ActualSourceMeanGramCongruence405
#print axioms KLSConstantImprovement.ActualSourceMeanGramCongruence405.actual_congruent_meanGram_posSemidef
#print axioms KLSConstantImprovement.ActualSourceMeanGramCongruence405.actual_congruent_meanGram_order
#print axioms KLSConstantImprovement.ActualSourceMeanGramCongruence405.actual_congruent_meanGram_square_bound
