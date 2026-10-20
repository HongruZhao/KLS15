import KLSConstantImprovement.ActualCompatibleConnectionBoundary405

/-! Finite covariant Kato inequalities for the actual Hessian metric.
These are pointwise algebra only; weak Bochner and nonlinear test domains
are separate actual-source obligations. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualCovariantKatoAlgebra405
open KLS ActualCompatibleConnectionYoung405 ActualCompatibleConnectionBoundary405
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def covariantHessian (H B N : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  H * B + (1/2 : ℝ) • N

theorem covariantHessian_isSymm (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hB : (H * B).IsSymm) (hN : N.IsSymm) : (covariantHessian H B N).IsSymm := by
  change (H * B + (1/2 : ℝ) • N).transpose = (H * B + (1/2 : ℝ) • N)
  simp only [Matrix.transpose_add, Matrix.transpose_smul, hB.eq, hN.eq]

theorem canonical_square_kato (H C : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hC : C.IsSymm) (u : Fin n → ℝ) :
    (C *ᵥ u) ⬝ᵥ (H⁻¹ *ᵥ (C *ᵥ u)) ≤
      (u ⬝ᵥ (H *ᵥ u)) * (H⁻¹ * C * H⁻¹ * C).trace := by
  let q : ℝ := (C *ᵥ u) ⬝ᵥ (H⁻¹ *ᵥ (C *ᵥ u))
  let m : ℝ := u ⬝ᵥ (H *ᵥ u)
  let e : ℝ := (H⁻¹ * C * H⁻¹ * C).trace
  have hq : 0 ≤ q := hH.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hm : 0 ≤ m := hH.posSemidef.dotProduct_mulVec_nonneg _
  have he : 0 ≤ e := by
    change 0 ≤ (H⁻¹ * C * H⁻¹ * C).trace
    rw [← whitened_connection_square H C hH hC]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hb := compatible_connection_boundary_square H C hH hC (C *ᵥ u) u
  change q ^ 2 ≤ q * m * e at hb
  change q ≤ m * e
  by_cases hz : q = 0
  · rw [hz]
    exact mul_nonneg hm he
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
    exact le_of_mul_le_mul_left (by nlinarith only [hb] : q * q ≤ q * (m * e)) hqp

theorem covariant_mass_derivative_kato (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hB : (H * B).IsSymm) (hN : N.IsSymm) (u : Fin n → ℝ) :
    ((2 : ℝ) • (covariantHessian H B N *ᵥ u)) ⬝ᵥ
        (H⁻¹ *ᵥ ((2 : ℝ) • (covariantHessian H B N *ᵥ u))) ≤
      4 * (u ⬝ᵥ (H *ᵥ u)) *
        (H⁻¹ * covariantHessian H B N * H⁻¹ * covariantHessian H B N).trace := by
  have h := canonical_square_kato H (covariantHessian H B N) hH
    (covariantHessian_isSymm H B N hB hN) u
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  nlinarith only [h]

theorem canonical_Bochner_density_lower (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hB : (H * B).IsSymm) (hN : N.IsSymm) (u : Fin n → ℝ)
    {P : ℝ} (hP : 0 ≤ P) :
    (u ⬝ᵥ (H *ᵥ u)) / 2 ≤
      (H⁻¹ * covariantHessian H B N * H⁻¹ * covariantHessian H B N).trace +
        ((u ⬝ᵥ (H *ᵥ u)) + P) / 2 + (H⁻¹ * N * H⁻¹ * N).trace / 4 := by
  have hC := covariantHessian_isSymm H B N hB hN
  have h1 : 0 ≤ (H⁻¹ * covariantHessian H B N * H⁻¹ * covariantHessian H B N).trace := by
    rw [← whitened_connection_square H (covariantHessian H B N) hH hC]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ (H⁻¹ * N * H⁻¹ * N).trace := by
    rw [← whitened_connection_square H N hH hN]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

end KLSConstantImprovement.ActualCovariantKatoAlgebra405
#print axioms KLSConstantImprovement.ActualCovariantKatoAlgebra405.canonical_square_kato
#print axioms KLSConstantImprovement.ActualCovariantKatoAlgebra405.covariant_mass_derivative_kato
#print axioms KLSConstantImprovement.ActualCovariantKatoAlgebra405.canonical_Bochner_density_lower
