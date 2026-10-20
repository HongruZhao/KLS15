import KLSConstantImprovement.ActualTensorRowWhite405

/-! Exact finite indices in the cyclic first adjoint. Every transpose
and both full tensor symmetries are retained. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem sum4_ijab_jbia (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) = ∑ j, ∑ b, ∑ i, ∑ a, f i j a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ i, ∑ b, ∑ a, f i j a b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem full_tensor_cyclic_cross (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) (h23 : ∀ i j k, T i j k = T i k j)
    (hn12 : ∀ i j k, N i j k = N j i k) (hn23 : ∀ i j k, N i j k = N i k j)
    (p : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, T i a b * N a i j * p j b) =
      ∑ j, ∑ b, p j b * (T b * N j).trace := by
  rw [sum4_ijab_jbia]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  have ht : T i a b = T b a i := by rw [h23 i a b, h12 i b a, h23 b i a]
  have hn : N a i j = N j i a := by rw [hn23 a i j, hn12 a j i, hn23 j a i]
  rw [ht, hn]
  ring

theorem trace_metric_row_pair (H U Z : Matrix (Fin n) (Fin n) ℝ) :
    (H * U * H * Z.transpose).trace = ∑ i, ∑ j, ∑ b, H i j * (U * H) j b * Z i b := by
  rw [Matrix.mul_assoc H U H]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem full_tensor_affine_cross (H p : Matrix (Fin n) (Fin n) ℝ)
    (X : Fin n → ℝ) (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h12 : ∀ i j k, T i j k = T j i k) :
    (∑ i, ∑ j, ∑ a, ∑ b, T i a b * X a * H i j * p j b) =
      ∑ i, ∑ j, ∑ b, H i j * p j b * (∑ a, X a • T a) i b := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [h12 i a b]
  ring

end KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405
#print axioms KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405.full_tensor_cyclic_cross
#print axioms KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405.trace_metric_row_pair
#print axioms KLSConstantImprovement.ActualCyclicRowAdjointAlgebra405.full_tensor_affine_cross
