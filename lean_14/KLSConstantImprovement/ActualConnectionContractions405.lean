import KLSConstantImprovement.ActualCanonicalConnectionAlgebra405

/-! Exact finite contractions of the aggregate weak-H product test.
The order of every raw Jacobian factor is retained. Analytic domains,
cutoffs and mass bounds are separate actual-source obligations. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualConnectionContractions405
open KLS ActualCanonicalConnectionAlgebra405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

private theorem sum3_last_first (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, f i j a) = ∑ a, ∑ i, ∑ j, f i j a := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem connection_first_cross (J B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j a, N i j a = N j i a ∧ N i j a = N i a j) (u : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (B i a * u j)) =
      (B * J * thirdAlong N u).trace := by
  have hj (i a : Fin n) : (∑ j, (J * N i) a j * u j) = (J * thirdAlong N u) a i := by
    change ((J * N i) *ᵥ u) a = _
    rw [← Matrix.mulVec_mulVec]
    simp_rw [Matrix.mulVec, dotProduct, thirdAlong_action N hN u]
    rfl
  calc
    _ = ∑ i, ∑ a, B i a * (∑ j, (J * N i) a j * u j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, ∑ a, B i a * (J * thirdAlong N u) a i := by simp_rw [hj]
    _ = _ := by simp only [Matrix.mul_assoc, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem connection_second_cross (J B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (u i * B j a)) =
      (B * J * thirdAlong N u).trace := by
  have he : J * thirdAlong N u = ∑ i, u i • (J * N i) := by
    simp only [thirdAlong, Matrix.mul_sum, Matrix.mul_smul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ a, ∑ i, (J * N i) a j * (u i * B j a) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ j, ∑ a, B j a * (∑ i, u i * (J * N i) a j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Matrix.mul_assoc, he]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul]

theorem connection_cross_contraction (J B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j a, N i j a = N j i a ∧ N i j a = N i a j) (u : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (B i a * u j + u i * B j a)) =
      2 * (B * J * thirdAlong N u).trace := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [connection_first_cross J B N hN u, connection_second_cross J B N u]
  ring

theorem connection_boundary_contraction (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u z : Fin n → ℝ) :
    (∑ i, ∑ j, ∑ a, (J * N i) a j * (u i * u j) * z a) =
      z ⬝ᵥ (J *ᵥ (thirdAlong N u *ᵥ u)) := by
  have he : J * thirdAlong N u = ∑ i, u i • (J * N i) := by
    simp only [thirdAlong, Matrix.mul_sum, Matrix.mul_smul]
  rw [Matrix.mulVec_mulVec, he]
  rw [sum3_last_first]
  simp only [dotProduct, Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end KLSConstantImprovement.ActualConnectionContractions405
#print axioms KLSConstantImprovement.ActualConnectionContractions405.connection_cross_contraction
#print axioms KLSConstantImprovement.ActualConnectionContractions405.connection_boundary_contraction
