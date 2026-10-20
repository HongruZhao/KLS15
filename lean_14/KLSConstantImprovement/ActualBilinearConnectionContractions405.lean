import KLSConstantImprovement.ActualConnectionContractions405

/-! Polarized connection contractions for two different genuine rows.
No symmetry of the raw Jacobians, positivity premise, or tensor
derivative enters these exact finite identities. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualBilinearConnectionContractions405
open KLS ActualCanonicalConnectionAlgebra405 ActualConnectionContractions405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {n : ℕ}

theorem connection_cross_bilinear (J Du Dv : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j a, N i j a = N j i a ∧ N i j a = N i a j) (u v : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (Du i a * v j + u i * Dv j a)) =
      (Du * J * thirdAlong N v).trace + (Dv * J * thirdAlong N u).trace := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [connection_first_cross J Du N hN v, connection_second_cross J Dv N u]

theorem connection_boundary_bilinear (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u v z : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (u i * v j) * z a) =
      z ⬝ᵥ ((J * thirdAlong N u) *ᵥ v) := by
  have he : J * thirdAlong N u = ∑ i, u i • (J * N i) := by
    simp only [thirdAlong, Matrix.mul_sum, Matrix.mul_smul]
  rw [he]
  have hs : (∑ i, ∑ j, ∑ a, (J * N i) a j * (u i * v j) * z a) =
      ∑ a, ∑ i, ∑ j, (J * N i) a j * (u i * v j) * z a := by
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hs]
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem traceGram_bilinear (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) :
    (∑ i, ∑ j, matrixTraceGram J N i j * u i * v j) =
      (J * thirdAlong N u * J * thirdAlong N v).trace := by
  simp only [matrixTraceGram, thirdAlong, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_tensor_forcing (T : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (∑ a, (T * N a).trace * v a) = (T * thirdAlong N v).trace := by
  simp only [thirdAlong, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end KLSConstantImprovement.ActualBilinearConnectionContractions405

#print axioms KLSConstantImprovement.ActualBilinearConnectionContractions405.connection_cross_bilinear
#print axioms KLSConstantImprovement.ActualBilinearConnectionContractions405.connection_boundary_bilinear
#print axioms KLSConstantImprovement.ActualBilinearConnectionContractions405.traceGram_bilinear
