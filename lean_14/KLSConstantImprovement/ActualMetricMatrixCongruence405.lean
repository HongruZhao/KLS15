import KLSConstantImprovement.ActualTensorRowDerivative405
import KLSConstantImprovement.ActualSourceQuarticBinding405

/-! Deterministic dual matrix congruences preserve the literal entry
pairing. The same source metric derivative commutes with these constant
row transformations, without changing coordinates or the diffusion. -/
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace KLSConstantImprovement.ActualMetricMatrixCongruence405
open KLS ActualBoundedCanonicalSource ActualCanonicalMetricEnergyGraph ActualCompactRawMetricGraph
open ActualSourceHessianEvolution405 ActualSourceTensorGramMetricBinding ActualSourceQuarticBinding405
open ActualQuarticCompression405 ActualQuarticCongruence405 ActualTensorRowCongruence405 ActualTensorRowDerivative405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ} {μ : Measure (Space n)}

theorem entryPair_eq_trace_transpose (X Y : Matrix (Fin n) (Fin n) ℝ) :
    entryPair X Y = (X.transpose * Y).trace := by
  simp only [entryPair, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem entryPair_dual_congruence (R S X Y : Matrix (Fin n) (Fin n) ℝ)
    (hSR : S * R = 1) :
    entryPair (R * X * R.transpose) (S.transpose * Y * S) = entryPair X Y := by
  have hRtSt : R.transpose * S.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hSR
  rw [entryPair_eq_trace_transpose, entryPair_eq_trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (R * (X.transpose * Y * S)).trace := by
      have hc : R.transpose * (S.transpose * (Y * S)) = Y * S := by
        rw [← Matrix.mul_assoc, hRtSt, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hc]
    _ = ((X.transpose * Y * S) * R).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc, hSR, Matrix.mul_one]

def rawMetricMatrix (d : SourceData μ) (F : Fin n → Space n → Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ a, canonicalMetricRoot d.potential x r a • F a x

theorem rawMetricMatrix_apply (d : SourceData μ)
    (F : Fin n → Space n → Matrix (Fin n) (Fin n) ℝ) (r i j : Fin n) (x : Space n) :
    rawMetricMatrix d F r x i j =
      rawCanonicalMetricDerivative d.potential (fun a y => F a y i j) r x := by
  simp only [rawMetricMatrix, rawCanonicalMetricDerivative, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem rawMetricMatrix_congruence (d : SourceData μ)
    (F : Fin n → Space n → Matrix (Fin n) (Fin n) ℝ)
    (R C : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (x : Space n) :
    rawMetricMatrix d (fun a y => R * F a y * C) r x = R * rawMetricMatrix d F r x * C := by
  simp only [rawMetricMatrix, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

def hessianMetricMatrix (d : SourceData μ) (r : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  rawMetricMatrix d (fun a y => sourceThirdMatrix d y a) r x

def gramMetricMatrix (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  rawMetricMatrix d (fun a y => rawGramDerivative (coordinateHessian d.potential y) T (sourceThirdMatrix d y a)) r x

theorem hessianMetricMatrix_apply (d : SourceData μ) (r i j : Fin n) (x : Space n) :
    hessianMetricMatrix d r x i j =
      rawCanonicalMetricDerivative d.potential (fun a y => d.third y a i j) r x := by
  exact rawMetricMatrix_apply d _ r i j x

theorem gramMetricMatrix_apply (d : SourceData μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (r i j : Fin n) (x : Space n) :
    gramMetricMatrix d T r x i j = rawCanonicalMetricDerivative d.potential
      (sourceTensorGramRawDerivative d.potential d.third T i j) r x := by
  rw [gramMetricMatrix, rawMetricMatrix_apply]
  unfold rawCanonicalMetricDerivative
  apply Finset.sum_congr rfl
  intro a _
  rw [actual_gram_raw_derivative_binding]

theorem gramMetricMatrix_rowCongruence (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n) (x : Space n) :
    gramMetricMatrix d (rowCongruentSlices T S) r x = S.transpose * gramMetricMatrix d T r x * S := by
  unfold gramMetricMatrix
  simp_rw [rawGramDerivative_rowCongruentSlices]
  exact rawMetricMatrix_congruence d _ S.transpose S r x

end KLSConstantImprovement.ActualMetricMatrixCongruence405
#print axioms KLSConstantImprovement.ActualMetricMatrixCongruence405.entryPair_dual_congruence
#print axioms KLSConstantImprovement.ActualMetricMatrixCongruence405.rawMetricMatrix_congruence
#print axioms KLSConstantImprovement.ActualMetricMatrixCongruence405.gramMetricMatrix_rowCongruence
