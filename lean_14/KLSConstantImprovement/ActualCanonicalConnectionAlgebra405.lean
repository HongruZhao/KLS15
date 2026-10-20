import KLS.MatrixTracePositive

/-!
Finite algebra for the weak inverse-tensor connection cancellation.
The matrix N_k is the actual third-tensor slice when this is applied to
SourceData. This file proves the index contractions only; it does not
assume or provide any analytic domain or operator-core assertion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCanonicalConnectionAlgebra405
variable {n : ℕ}

def thirdAlong (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := ∑ k, u k • N k

@[simp] theorem thirdAlong_apply
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i j : Fin n) :
    thirdAlong N u i j = ∑ k, u k * N k i j := by
  simp only [thirdAlong, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

def inverseJacobian (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ a, (-(J * N j * J) i a * p a + J i a * C j a)

private theorem third_perm
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i) (j a k : Fin n) :
    N j a k = N k a j := by
  calc
    N j a k = N a j k := (hN j a k).1
    _ = N a k j := (hN a j k).2
    _ = N k a j := (hN a k j).1

theorem thirdAlong_action
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i)
    (u : Fin n → ℝ) (j a : Fin n) :
    (N j *ᵥ u) a = thirdAlong N u a j := by
  simp only [Matrix.mulVec, dotProduct, thirdAlong_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [third_perm N hN j a k, mul_comm]

theorem inverseTensor_action
    (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i)
    (p : Fin n → ℝ) (k a : Fin n) :
    ((J * N k * J) *ᵥ p) a = (J * thirdAlong N (J *ᵥ p)) a k := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (∑ b, J a b * (N k *ᵥ (J *ᵥ p)) b) = _
  simp_rw [thirdAlong_action N hN]
  rfl

/-- Full third-tensor symmetry converts the literal ordered raw derivative
to J(C-N_u), preserving the order of every matrix factor. -/
theorem inverseJacobian_eq
    (J C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i)
    (p : Fin n → ℝ) :
    inverseJacobian J N p C = J * (C - thirdAlong N (J *ᵥ p)) := by
  ext i j
  calc
    inverseJacobian J N p C i j =
        -((J * N j * J) *ᵥ p) i + (J * C) i j := by
      simp only [inverseJacobian, Matrix.of_apply, Matrix.mulVec, dotProduct,
        Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib, Matrix.mul_apply]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hC.apply a j]
    _ = -(J * thirdAlong N (J *ᵥ p)) i j + (J * C) i j := by
      rw [inverseTensor_action J N hN p j i]
    _ = _ := by
      rw [Matrix.mul_sub, Matrix.sub_apply]
      ring

private theorem thirdAlong_inverse_congruence
    (J : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    J * thirdAlong N u * J = ∑ k, u k • (J * N k * J) := by
  simp only [thirdAlong, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

private theorem first_connection_contraction
    (J D : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i) (p : Fin n → ℝ) :
    (∑ k, ∑ i, ∑ a, (J * N k * J) a i * (D k a * p i)) =
      (D * (J * thirdAlong N (J *ᵥ p))).trace := by
  calc
    _ = ∑ k, ∑ a, D k a * (∑ i, (J * N k * J) a i * p i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ k, ∑ a, D k a * (J * thirdAlong N (J *ᵥ p)) a k := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      rw [show (∑ i, (J * N k * J) a i * p i) = ((J * N k * J) *ᵥ p) a from rfl,
        inverseTensor_action J N hN p k a]
    _ = _ := by simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem second_connection_contraction
    (J C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    (∑ k, ∑ i, ∑ a, (J * N k * J) a i * (u k * C a i)) =
      (J * thirdAlong N u * J * C).trace := by
  calc
    _ = ∑ i, ∑ k, ∑ a, (J * N k * J) a i * (u k * C a i) := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ k, (J * N k * J) a i * (u k * C a i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ k, (J * N k * J) a i * (u k * C a i) := Finset.sum_comm
    _ = ∑ a, ∑ i, (∑ k, u k * (J * N k * J) a i) * C a i := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ a, ∑ i, (J * thirdAlong N u * J) a i * C a i := by
      rw [thirdAlong_inverse_congruence]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    _ = _ := KLS.matrix_entrywise_contraction_eq_trace _ C hC

/-- The exact connection contraction cancels the two mixed matrix terms
and the inverse-third square in the signed raw Jacobian trace. -/
theorem inverseJacobian_connection_trace
    (J C : Matrix (Fin n) (Fin n) ℝ) (hC : C.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i) (p : Fin n → ℝ) :
    let D := inverseJacobian J N p C
    (D * D).trace +
      (∑ k, ∑ i, ∑ a, (J * N k * J) a i *
        (D k a * p i + (J *ᵥ p) k * C a i)) = (J * C * J * C).trace := by
  dsimp only
  simp only [mul_add, Finset.sum_add_distrib]
  rw [first_connection_contraction J _ N hN p,
    second_connection_contraction J C hC N (J *ᵥ p), inverseJacobian_eq J C hC N hN p]
  rw [← Matrix.trace_add, ← Matrix.trace_add]
  congr 1
  noncomm_ring

private theorem curvature_contraction
    (H J : Matrix (Fin n) (Fin n) ℝ) (hHJ : H * J = 1) (p : Fin n → ℝ) :
    (∑ i, ∑ j, H i j * (J *ᵥ p) i * (J *ᵥ p) j) = p ⬝ᵥ (J *ᵥ p) := by
  have hHu : H *ᵥ (J *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, hHJ, Matrix.one_mulVec]
  calc
    _ = (J *ᵥ p) ⬝ᵥ (H *ᵥ (J *ᵥ p)) := by
      change (∑ i, ∑ j, H i j * (J *ᵥ p) i * (J *ᵥ p) j) =
        ∑ i, (J *ᵥ p) i * (∑ j, H i j * (J *ᵥ p) j)
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hHu, dotProduct_comm]

theorem connection_target_contraction
    (H J P : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hHJ : H * J = 1)
    (p : Fin n → ℝ) :
    (∑ k, ∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) k i - (H * P) k i) *
      ((J *ᵥ p) k * p i)) = p ⬝ᵥ (J *ᵥ p) - p ⬝ᵥ (P *ᵥ p) := by
  have hHu : H *ᵥ (J *ᵥ p) = p := by
    rw [Matrix.mulVec_mulVec, hHJ, Matrix.one_mulVec]
  have hcross : (J *ᵥ p) ⬝ᵥ (H *ᵥ (P *ᵥ p)) = p ⬝ᵥ (P *ᵥ p) := by
    calc
      _ = (J *ᵥ p) ⬝ᵥ (Hᵀ *ᵥ (P *ᵥ p)) := by rw [hH.eq]
      _ = (P *ᵥ p) ⬝ᵥ (H *ᵥ (J *ᵥ p)) :=
        Matrix.dotProduct_transpose_mulVec H (J *ᵥ p) (P *ᵥ p)
      _ = _ := by rw [hHu, dotProduct_comm]
  calc
    _ = (J *ᵥ p) ⬝ᵥ ((1 - H * P) *ᵥ p) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (J *ᵥ p) ⬝ᵥ p - (J *ᵥ p) ⬝ᵥ (H *ᵥ (P *ᵥ p)) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Matrix.mulVec_mulVec]
    _ = _ := by
      rw [hcross, dotProduct_comm (J *ᵥ p) p]

/-- Pointwise balance used before integration: the left connection is
exactly the term supplied by the genuine compact raw H1 product test. -/
theorem finite_compact_connection_balance
    (H J C P : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hC : C.IsSymm)
    (hHJ : H * J = 1)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ k i j, N k i j = N i k j ∧ N k i j = N k j i) (p : Fin n → ℝ) :
    let u := J *ᵥ p
    let D := inverseJacobian J N p C
    (∑ i, ∑ j, (H i j * u i * u j + D i j * D j i)) +
      (∑ k, ∑ i, ∑ a, (J * N k * J) a i *
        (D k a * p i + u k * C a i)) =
      (J * C * J * C).trace + p ⬝ᵥ (P *ᵥ p) +
        (∑ k, ∑ i, ((1 : Matrix (Fin n) (Fin n) ℝ) k i - (H * P) k i) *
          (u k * p i)) := by
  dsimp only
  simp only [Finset.sum_add_distrib]
  rw [curvature_contraction H J hHJ p, connection_target_contraction H J P hH hHJ p]
  have hd : (∑ i, ∑ j, inverseJacobian J N p C i j * inverseJacobian J N p C j i) =
      (inverseJacobian J N p C * inverseJacobian J N p C).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [hd]
  have hc := inverseJacobian_connection_trace J C hC N hN p
  dsimp only at hc
  linarith

end KLSConstantImprovement.ActualCanonicalConnectionAlgebra405

#print axioms KLSConstantImprovement.ActualCanonicalConnectionAlgebra405.inverseJacobian_eq
#print axioms KLSConstantImprovement.ActualCanonicalConnectionAlgebra405.inverseJacobian_connection_trace
#print axioms KLSConstantImprovement.ActualCanonicalConnectionAlgebra405.finite_compact_connection_balance
