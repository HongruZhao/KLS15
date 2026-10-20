import KLSConstantImprovement.ActualCompatibleConnectionYoung405

/-! Pointwise metric boundary bound used before actual cutoff passage.
It retains the vector mass as a factor; it asserts no boundary vanishing
when that mass is merely integrable. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualCompatibleConnectionBoundary405
open KLS ActualCompatibleConnectionYoung405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem compatible_connection_boundary_square (H N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hN : N.IsSymm) (z u : Fin n → ℝ) :
    (z ⬝ᵥ (H⁻¹ *ᵥ (N *ᵥ u))) ^ 2 ≤
      (z ⬝ᵥ (H⁻¹ *ᵥ z)) * (u ⬝ᵥ (H *ᵥ u)) * (H⁻¹ * N * H⁻¹ * N).trace := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hdet : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hdet
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hRtR : R.transpose * R = H⁻¹ := by rw [hR.eq, hRR]
  have hStS : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
  have hAv : (R * N * R) *ᵥ (S *ᵥ u) = R *ᵥ (N *ᵥ u) := by
    rw [Matrix.mulVec_mulVec]
    have he : R * N * R * S = R * N := by simp only [Matrix.mul_assoc, hRS, Matrix.mul_one]
    rw [he, ← Matrix.mulVec_mulVec]
  have hp : (R *ᵥ z) ⬝ᵥ ((R * N * R) *ᵥ (S *ᵥ u)) =
      z ⬝ᵥ (H⁻¹ *ᵥ (N *ᵥ u)) := by
    rw [hAv, dotProduct_comm (R *ᵥ z),
      ← Matrix.dotProduct_transpose_mulVec R z (R *ᵥ (N *ᵥ u)), Matrix.mulVec_mulVec, hRtR]
  have hz : (R *ᵥ z) ⬝ᵥ (R *ᵥ z) = z ⬝ᵥ (H⁻¹ *ᵥ z) := by
    rw [← Matrix.dotProduct_transpose_mulVec R z (R *ᵥ z), Matrix.mulVec_mulVec, hRtR]
  have hu : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ (H *ᵥ u) := by
    rw [← Matrix.dotProduct_transpose_mulVec S u (S *ᵥ u), Matrix.mulVec_mulVec, hStS]
  have hc := finite_bilinear_square_bound (R * N * R) (R *ᵥ z) (S *ᵥ u)
  rw [hp, hz, hu, whitened_connection_square H N hH hN] at hc
  exact hc

end KLSConstantImprovement.ActualCompatibleConnectionBoundary405
#print axioms KLSConstantImprovement.ActualCompatibleConnectionBoundary405.compatible_connection_boundary_square
