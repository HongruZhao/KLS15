import KLS.PositiveMatrixSquareRoot

/-! Extending a genuine congruence contraction to every symmetric test
matrix, including indefinite matrices. The spectral factorization is the
actual old-release construction, not an assumed factorization. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem sum_transpose_products_le_squares (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, f i j*f j i) ≤ ∑ i, ∑ j, f i j^2 := by
  have hswap : (∑ i, ∑ j, f j i ^ 2) = ∑ i, ∑ j, f i j^2 := Finset.sum_comm
  calc
    (∑ i, ∑ j, f i j*f j i) ≤ ∑ i, ∑ j, (f i j^2+f j i^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (f i j-f j i)]
    _ = ∑ i, ∑ j, f i j^2 := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [hswap]
      ring

theorem trace_square_le_frobenius (M : Matrix (Fin n) (Fin n) ℝ) :
    (M*M).trace ≤ matrixFrobeniusSq M := by
  simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, matrixFrobeniusSq] using
    sum_transpose_products_le_squares (fun i j => M i j)

theorem frobenius_orthogonal_left (U T : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose*U = 1) :
    matrixFrobeniusSq (U*T) = matrixFrobeniusSq T := by
  rw [matrixFrobeniusSq_eq_trace_mul_transpose,
    matrixFrobeniusSq_eq_trace_mul_transpose, Matrix.transpose_mul]
  calc
    (U*T*(T.transpose*U.transpose)).trace =
        (U*(T*T.transpose)*U.transpose).trace := by simp only [Matrix.mul_assoc]
    _ = (U.transpose*U*(T*T.transpose)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (T*T.transpose).trace := by rw [hU, Matrix.one_mul]

theorem trace_factor_contraction_le
    (A U S : Matrix (Fin n) (Fin n) ℝ) (hU : U.transpose*U = 1) :
    ((A.transpose*U*A)*S*(A.transpose*U*A)*S).trace ≤
      matrixFrobeniusSq (A*S*A.transpose) := by
  have he : ((A.transpose*U*A)*S*(A.transpose*U*A)*S).trace =
      ((U*(A*S*A.transpose))*(U*(A*S*A.transpose))).trace := by
    calc
      _ = (A.transpose*(U*A*S*A.transpose*U*A*S)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((U*A*S*A.transpose*U*A*S)*A.transpose).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [he]
  exact (trace_square_le_frobenius _).trans_eq (frobenius_orthogonal_left U _ hU)

theorem symmetric_contraction_of_congruence_bound
    {ι : Type*} [Fintype ι] (S : ι → Matrix (Fin n) (Fin n) ℝ) (C : ℝ)
    (hbound : ∀ R : Matrix (Fin n) (Fin n) ℝ,
      (∑ k, matrixFrobeniusSq (R*S k*R.transpose)) ≤ C*matrixFrobeniusSq (R.transpose*R))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) :
    (∑ k, (H*S k*H*S k).trace) ≤ C*matrixFrobeniusSq H := by
  obtain ⟨A,U,B,_hA,_hU,_hB,hU,hAB,hAU,hFrob⟩ := exists_spectral_quadratic_transport H hH
  calc
    (∑ k, (H*S k*H*S k).trace) ≤
        ∑ k, matrixFrobeniusSq (A*S k*A.transpose) := by
      apply Finset.sum_le_sum
      intro k _
      rw [← hAU]
      exact trace_factor_contraction_le A U (S k) hU
    _ ≤ C*matrixFrobeniusSq (A.transpose*A) := hbound A
    _ = C*matrixFrobeniusSq H := by rw [hAB,hFrob]

#print axioms trace_square_le_frobenius
#print axioms symmetric_contraction_of_congruence_bound
end KLS.DeterministicBridgeIntegration
