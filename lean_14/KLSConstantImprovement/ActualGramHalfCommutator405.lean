import KLSConstantImprovement.ActualGramHalf405
import KLS.TensorCommutatorComparison

/-! The exact combined commutator remainder of the concrete Gram-half
comparison. The negative Gram-half commutator remains in the identity. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualGramHalfCommutator405
open KLS ActualKroneckerGram405 ActualGramHalf405
variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem gram_half_commutator_identity (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ i, matrixFrobeniusSq (T i * H - H * T i)) -
      matrixFrobeniusSq (CFC.sqrt (sliceGram T) * H - H * CFC.sqrt (sliceGram T)) =
    2 * ((CFC.sqrt (sliceGram T) * H * CFC.sqrt (sliceGram T) * H).trace -
      ∑ i, (T i * H * T i * H).trace) := by
  let A := CFC.sqrt (sliceGram T)
  have hA : A.IsSymm := (CFC.sqrt_nonneg (sliceGram T)).posSemidef.isHermitian.isSymm
  have hAsq : A * A = sliceGram T := by
    change CFC.sqrt (sliceGram T) * CFC.sqrt (sliceGram T) = sliceGram T
    exact CFC.sqrt_mul_sqrt_self _ (sliceGram_posSemidef T hT).nonneg
  have hs : (∑ i, ((T i * T i) * (H * H)).trace) -
      (∑ i, (T i * H * T i * H).trace) =
      (1 / 2 : ℝ) * ∑ i, matrixFrobeniusSq (T i * H - H * T i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Matrix.mul_assoc] using matrix_trace_commutator_difference (T i) H (hT i) hH
  have hp : (∑ i, ((T i * T i) * (H * H)).trace) = ((A * A) * (H * H)).trace := by
    rw [hAsq]
    unfold sliceGram
    rw [Matrix.sum_mul, Matrix.trace_sum]
  rw [hp] at hs
  have ha := matrix_trace_commutator_difference A H hA hH
  change (∑ i, matrixFrobeniusSq (T i * H - H * T i)) - matrixFrobeniusSq (A * H - H * A) =
    2 * ((A * H * A * H).trace - ∑ i, (T i * H * T i * H).trace)
  simp only [Matrix.mul_assoc] at hs ha ⊢
  linarith

theorem gram_half_combined_commutator_nonneg (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    0 ≤ (∑ i, matrixFrobeniusSq (T i * H - H * T i)) -
      matrixFrobeniusSq (CFC.sqrt (sliceGram T) * H - H * CFC.sqrt (sliceGram T)) := by
  rw [gram_half_commutator_identity T hT H hH]
  exact mul_nonneg (by norm_num) (gram_half_gap_nonneg T hT H hH)

end KLSConstantImprovement.ActualGramHalfCommutator405

#print axioms KLSConstantImprovement.ActualGramHalfCommutator405.gram_half_commutator_identity
#print axioms KLSConstantImprovement.ActualGramHalfCommutator405.gram_half_combined_commutator_nonneg
