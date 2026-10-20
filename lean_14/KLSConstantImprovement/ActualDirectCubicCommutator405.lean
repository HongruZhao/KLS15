import KLS.TensorCommutatorComparison
import KLS.MatrixTracePositive

/-! The direct cubic source charge is a literal sum of matrix commutator
squares in a common white frame. Full tensor symmetry supplies the Gram
duality; no ordering of arbitrary matrix families is assumed. Binding the
white frame to actual weighted fields remains a separate step. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDirectCubicCommutator405
open KLS
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem full_tensor_gram_duality
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (T i * M * T j).trace = ∑ p, (T p * M * T p) i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro q _
  rw [hfirst i p q, hfirst j r p, hlast r j p, hfirst r p j]

theorem full_tensor_trace_pairing
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hfirst : ∀ i j k, T i j k = T j i k)
    (hlast : ∀ i j k, T i j k = T i k j)
    (A B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    (∑ i, ∑ j, A i j * (T i * B * T j).trace) =
      ∑ p, (T p * A * T p * B).trace := by
  simp_rw [full_tensor_gram_duality T hfirst hlast B]
  simp only [Finset.mul_sum]
  have hswap : (∑ i, ∑ j, ∑ p, A i j * (T p * B * T p) i j) =
      ∑ p, ∑ i, ∑ j, A i j * (T p * B * T p) i j := by
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro p _
  have hTp : (T p).IsSymm := Matrix.IsSymm.ext fun i j => (hlast p j i)
  have hprod : (T p * B * T p).IsSymm := by
    change (T p * B * T p).transpose = T p * B * T p
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hTp.eq, hB.eq]
    simp only [Matrix.mul_assoc]
  rw [matrix_entrywise_contraction_eq_trace _ _ hprod]
  calc
    _ = (A * T p * B * T p).trace := by simp only [Matrix.mul_assoc]
    _ = (T p * (A * T p * B)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem full_tensor_curvature_pairing
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hTfirst : ∀ i j k, T i j k = T j i k)
    (hTlast : ∀ i j k, T i j k = T i k j)
    (hNfirst : ∀ i j k, N i j k = N j i k)
    (hNlast : ∀ i j k, N i j k = N i k j) :
    (∑ i, ∑ j, (T i * T j).trace * (N i * N j).trace) =
      ∑ p, ∑ a, ((T p * T p) * (N a * N a)).trace := by
  have hg (i j : Fin n) : (T i * T j).trace = ∑ p, (T p * T p) i j := by
    simpa only [Matrix.mul_one, Matrix.one_mul] using
      full_tensor_gram_duality T hTfirst hTlast (1 : Matrix (Fin n) (Fin n) ℝ) i j
  simp_rw [hg]
  simp only [Finset.sum_mul]
  have hswap : (∑ i, ∑ j, ∑ p, (T p * T p) i j * (N i * N j).trace) =
      ∑ p, ∑ i, ∑ j, (T p * T p) i j * (N i * N j).trace := by
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_congr rfl fun p _ =>
    tensor_gram_contraction_eq_trace_square (T p) N hNfirst hNlast

theorem full_tensor_direct_commutator_square
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hTfirst : ∀ i j k, T i j k = T j i k)
    (hTlast : ∀ i j k, T i j k = T i k j)
    (hNfirst : ∀ i j k, N i j k = N j i k)
    (hNlast : ∀ i j k, N i j k = N i k j) :
    (∑ i, ∑ j, (T i * T j).trace * (N i * N j).trace) -
      (∑ a, ∑ i, ∑ j, N a i j * (T i * N a * T j).trace) =
        (1/2 : ℝ) * ∑ p, ∑ a, matrixFrobeniusSq (T p * N a - N a * T p) := by
  have hTs (p : Fin n) : (T p).IsSymm := Matrix.IsSymm.ext fun i j => hTlast p j i
  have hNs (a : Fin n) : (N a).IsSymm := Matrix.IsSymm.ext fun i j => hNlast a j i
  rw [full_tensor_curvature_pairing T N hTfirst hTlast hNfirst hNlast]
  simp_rw [full_tensor_trace_pairing T hTfirst hTlast _ _ (hNs _)]
  rw [Finset.sum_comm (f := fun a p => (T p * N a * T p * N a).trace)]
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Matrix.mul_assoc] using matrix_trace_commutator_difference (T p) (N a) (hTs p) (hNs a)

theorem full_tensor_direct_curvature_nonnegative
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hTfirst : ∀ i j k, T i j k = T j i k)
    (hTlast : ∀ i j k, T i j k = T i k j)
    (hNfirst : ∀ i j k, N i j k = N j i k)
    (hNlast : ∀ i j k, N i j k = N i k j) :
    (∑ a, ∑ i, ∑ j, N a i j * (T i * N a * T j).trace) ≤
      ∑ i, ∑ j, (T i * T j).trace * (N i * N j).trace := by
  have he := full_tensor_direct_commutator_square T N hTfirst hTlast hNfirst hNlast
  have hn : 0 ≤ ∑ p, ∑ a, matrixFrobeniusSq (T p * N a - N a * T p) := by
    unfold matrixFrobeniusSq
    positivity
  linarith

end KLSConstantImprovement.ActualDirectCubicCommutator405
#print axioms KLSConstantImprovement.ActualDirectCubicCommutator405.full_tensor_gram_duality
#print axioms KLSConstantImprovement.ActualDirectCubicCommutator405.full_tensor_direct_commutator_square
#print axioms KLSConstantImprovement.ActualDirectCubicCommutator405.full_tensor_direct_curvature_nonnegative
