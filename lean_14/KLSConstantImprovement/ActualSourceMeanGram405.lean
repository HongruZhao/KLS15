import KLSConstantImprovement.ActualSourceQuadraticSandwich405
import KLS.MatrixEntryLpProducts

/-! Actual means of the same source tensor Gram. The signed matrix cap is
applied to every literal slice combination, which supplies the Loewner upper
bound without a mean-matrix witness or a change of law.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualSourceMeanGram405
open KLS ActualBoundedCanonicalSource ActualSourceQuadraticSandwich405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

def sliceCombination (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := ∑ i, v i • T i

def sourceMeanGram {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, matrixTraceGram (coordinateHessian d.potential x) T i j
    ∂potentialMeasure d.potential

theorem traceGram_cyclic (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    matrixTraceGram H T i j = (T i * H * T j * H).trace := by
  unfold matrixTraceGram
  calc
    _ = (H * (T i * H * T j)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_comm _ _

theorem sliceCombination_trace (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * matrixTraceGram H T i j) =
      (sliceCombination T v * H * sliceCombination T v * H).trace := by
  simp_rw [traceGram_cyclic]
  simp only [sliceCombination, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ht := Matrix.trace_mul_comm (T j * H) (T i * H)
  simp only [Matrix.mul_assoc] at ht ⊢
  rw [ht]
  ring

theorem actual_traceGram_integrable {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Integrable (fun x => matrixTraceGram (coordinateHessian d.potential x) T i j)
      (potentialMeasure d.potential) := by
  letI : IsProbabilityMeasure (potentialMeasure d.potential) := d.source_probability
  have hh := fun a b => d.hessian_entry_memLp a b ∞
  have hm1 : ∀ a b, MemLp (fun x => (coordinateHessian d.potential x * T i) a b) ∞
      (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries hh (memLp_constant_matrix_entries (T i))
  have hm2 : ∀ a b, MemLp (fun x =>
      (coordinateHessian d.potential x * T i * coordinateHessian d.potential x) a b) ∞
      (potentialMeasure d.potential) := memLp_matrix_mul_entries hm1 hh
  have hm3 : ∀ a b, MemLp (fun x =>
      (coordinateHessian d.potential x * T i * coordinateHessian d.potential x * T j) a b) ∞
      (potentialMeasure d.potential) :=
    memLp_matrix_mul_entries hm2 (memLp_constant_matrix_entries (T j))
  exact (memLp_matrix_trace_entries hm3).integrable (by simp)

theorem actual_meanGram_quadratic_identity {μ : Measure (Space n)} (d : SourceData μ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * sourceMeanGram d T i j) =
      ∫ x, (sliceCombination T v * coordinateHessian d.potential x *
        sliceCombination T v * coordinateHessian d.potential x).trace
          ∂potentialMeasure d.potential := by
  have hi (i j : Fin n) := (actual_traceGram_integrable d T i j).const_mul (v i * v j)
  have he (i j : Fin n) : v i * v j * sourceMeanGram d T i j =
      ∫ x, v i * v j * matrixTraceGram (coordinateHessian d.potential x) T i j
        ∂potentialMeasure d.potential := (integral_const_mul _ _).symm
  have hinner (i : Fin n) :
      (∑ j, ∫ x, v i * v j * matrixTraceGram (coordinateHessian d.potential x) T i j
        ∂potentialMeasure d.potential) =
      ∫ x, ∑ j, v i * v j * matrixTraceGram (coordinateHessian d.potential x) T i j
        ∂potentialMeasure d.potential :=
    (integral_finsetSum _ (fun j _ => hi i j)).symm
  simp_rw [he]
  simp_rw [hinner]
  rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => sliceCombination_trace _ T v

theorem actual_meanGram_cap {μ : Measure (Space n)} (d : SourceData μ)
    (hiso : IsIsotropic μ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * sourceMeanGram d T i j) ≤
      2 * matrixFrobeniusSq (sliceCombination T v) := by
  rw [actual_meanGram_quadratic_identity]
  apply d.integral_signed_sandwich_le_two hiso
  change (∑ i, v i • T i).IsSymm
  change (∑ i, v i • T i).transpose = ∑ i, v i • T i
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, (hT _).eq]

end KLSConstantImprovement.ActualSourceMeanGram405
#print axioms KLSConstantImprovement.ActualSourceMeanGram405.sliceCombination_trace
#print axioms KLSConstantImprovement.ActualSourceMeanGram405.actual_traceGram_integrable
#print axioms KLSConstantImprovement.ActualSourceMeanGram405.actual_meanGram_quadratic_identity
#print axioms KLSConstantImprovement.ActualSourceMeanGram405.actual_meanGram_cap
