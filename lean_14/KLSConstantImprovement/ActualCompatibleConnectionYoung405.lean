import KLSConstantImprovement.ActualWhitenedJacobianSymmetry405

/-! Compatible pointwise connection absorption. The signed Jacobian
trace is converted to its genuine nonnegative metric-conjugate square.
The boundary estimate retains both the vector H-mass and inverse-metric
cutoff energy. No integrated or global cutoff claim occurs here. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualCompatibleConnectionYoung405
open KLS ActualWhitenedJacobianEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem finite_bilinear_square_bound (A : Matrix (Fin n) (Fin n) ℝ) (z u : Fin n → ℝ) :
    (z ⬝ᵥ (A *ᵥ u)) ^ 2 ≤ (z ⬝ᵥ z) * (u ⬝ᵥ u) * matrixFrobeniusSq A := by
  have hz : 0 ≤ z ⬝ᵥ z := Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
  have hu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hrow (i : Fin n) : (A *ᵥ u) i ^ 2 ≤ (∑ j, A i j ^ 2) * (u ⬝ᵥ u) := by
    simpa only [Matrix.mulVec, dotProduct, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) u
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hsum : (A *ᵥ u) ⬝ᵥ (A *ᵥ u) ≤ matrixFrobeniusSq A * (u ⬝ᵥ u) := by
    simpa only [dotProduct, matrixFrobeniusSq, ← pow_two, ← Finset.sum_mul] using hs
  have hc : (z ⬝ᵥ (A *ᵥ u)) ^ 2 ≤ (z ⬝ᵥ z) * ((A *ᵥ u) ⬝ᵥ (A *ᵥ u)) := by
    simpa only [dotProduct, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ z (A *ᵥ u)
  have hm := mul_le_mul_of_nonneg_left hsum hz
  nlinarith

theorem finite_trace_young (Z A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    |2 * (Z * A).trace| ≤ (1/4 : ℝ) * matrixFrobeniusSq A + 4 * matrixFrobeniusSq Z := by
  have he (W : Matrix (Fin n) (Fin n) ℝ) : (W * A).trace = ∑ i, ∑ j, W i j * A i j := by
    rw [← matrix_entrywise_contraction_eq_trace _ A hA]
  have hp (W : Matrix (Fin n) (Fin n) ℝ) :
      2 * (W * A).trace ≤ (1/4 : ℝ) * matrixFrobeniusSq A + 4 * matrixFrobeniusSq W := by
    rw [he W]
    have hs : 0 ≤ ∑ i, ∑ j, (2 * W i j - A i j / 2) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hx : (∑ i, ∑ j, (2 * W i j - A i j / 2) ^ 2) =
        4 * matrixFrobeniusSq W - 2 * (∑ i, ∑ j, W i j * A i j) +
          (1/4 : ℝ) * matrixFrobeniusSq A := by
      simp only [matrixFrobeniusSq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    linarith
  have hm : -(2 * (Z * A).trace) ≤ (1/4 : ℝ) * matrixFrobeniusSq A + 4 * matrixFrobeniusSq Z := by
    have hn := hp (-Z)
    simpa only [Matrix.neg_mul, Matrix.trace_neg, mul_neg, matrixFrobeniusSq, Matrix.neg_apply,
      neg_sq] using hn
  exact abs_le.mpr ⟨by linarith, hp Z⟩

theorem whitened_connection_square (H N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hN : N.IsSymm) :
    matrixFrobeniusSq (inverseSqrtMatrix H * N * inverseSqrtMatrix H) =
      (H⁻¹ * N * H⁻¹ * N).trace := by
  let R := inverseSqrtMatrix H
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hA : (R * N * R).IsSymm := by
    change (R * N * R).transpose = _
    simp only [Matrix.transpose_mul, hR.eq, hN.eq, Matrix.mul_assoc]
  rw [matrixFrobeniusSq_eq_trace_sq hA]
  calc
    _ = (R * (N * (R * R) * N) * R).trace := by simp only [Matrix.mul_assoc]
    _ = ((N * (R * R) * N) * R * R).trace :=
      (Matrix.trace_mul_cycle (N * (R * R) * N) R R).symm
    _ = _ := by
      rw [Matrix.mul_assoc, hRR, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]

theorem compatible_connection_young (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hc : (H * B).IsSymm) (hN : N.IsSymm) :
    |2 * (B * H⁻¹ * N).trace| ≤
      (1/4 : ℝ) * (H⁻¹ * N * H⁻¹ * N).trace + 4 * (B * B).trace := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hdet : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hdet
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hA : (R * N * R).IsSymm := by
    change (R * N * R).transpose = _
    simp only [Matrix.transpose_mul, hR.eq, hN.eq, Matrix.mul_assoc]
  have ht : (whitenedJacobian H B * (R * N * R)).trace = (B * H⁻¹ * N).trace := by
    change (S * B * R * (R * N * R)).trace = _
    calc
      _ = (S * (B * (R * R) * N * R)).trace := by simp only [Matrix.mul_assoc]
      _ = ((B * (R * R) * N * R) * S).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc, hRS, Matrix.mul_one, hRR]
  have hy := finite_trace_young (whitenedJacobian H B) (R * N * R) hA
  rw [ht, whitenedJacobian_frobenius H B hH hc,
    whitened_connection_square H N hH hN] at hy
  exact hy

end KLSConstantImprovement.ActualCompatibleConnectionYoung405
#print axioms KLSConstantImprovement.ActualCompatibleConnectionYoung405.finite_bilinear_square_bound
#print axioms KLSConstantImprovement.ActualCompatibleConnectionYoung405.finite_trace_young
#print axioms KLSConstantImprovement.ActualCompatibleConnectionYoung405.compatible_connection_young
