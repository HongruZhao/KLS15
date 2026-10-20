import KLSConstantImprovement.ActualCompatibleConnectionBoundary405
import KLSConstantImprovement.ActualWhitenedJacobianSymmetry405

/-! The extra signed term from Euclidean radial H testing. Compatibility
controls B-transpose in the inverse metric; no Euclidean contraction of
the vector PDE is asserted. Local condition bounds can then feed the
uniform radial Young inequality. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualCompatibleRadialExtra405
open KLS ActualCompatibleConnectionYoung405 ActualCompatibleConnectionBoundary405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

private theorem mulVec_square_le_frobenius (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ matrixFrobeniusSq A * (v ⬝ᵥ v) := by
  have hi (i : Fin n) : (A *ᵥ v) i ^ 2 ≤ (∑ j, A i j ^ 2) * (v ⬝ᵥ v) := by
    simpa only [Matrix.mulVec, dotProduct, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [dotProduct, matrixFrobeniusSq, ← pow_two, ← Finset.sum_mul] using hs

theorem compatible_transpose_inverse_energy (H B : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hc : (H * B).IsSymm) (u : Fin n → ℝ) :
    (B.transpose *ᵥ u) ⬝ᵥ (H⁻¹ *ᵥ (B.transpose *ᵥ u)) ≤
      (B * B).trace * (u ⬝ᵥ (H⁻¹ *ᵥ u)) := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  let D := whitenedJacobian H B
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hD : D.IsSymm := whitenedJacobian_isSymm H B hH hc
  have hdet : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hdet
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hBt : B.transpose = S * D * R := by
    have he := congrArg Matrix.transpose (whitenedJacobian_reconstruct H B hH)
    simpa only [R, S, D, Matrix.transpose_mul, hR.eq, hS.eq, hD.eq, mul_assoc] using he.symm
  have hv : R *ᵥ (B.transpose *ᵥ u) = D *ᵥ (R *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, hBt]
    simp only [← mul_assoc, hRS, one_mul, ← Matrix.mulVec_mulVec]
  have hnorm (z : Fin n → ℝ) : z ⬝ᵥ (H⁻¹ *ᵥ z) = (R *ᵥ z) ⬝ᵥ (R *ᵥ z) := by
    rw [← Matrix.dotProduct_transpose_mulVec R z (R *ᵥ z), Matrix.mulVec_mulVec,
      hR.eq, hRR]
  rw [hnorm (B.transpose *ᵥ u), hnorm u, hv]
  have hh := mulVec_square_le_frobenius D (R *ᵥ u)
  rwa [whitenedJacobian_frobenius H B hH hc] at hh

theorem compatible_radial_extra_square (H B N : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hc : (H * B).IsSymm) (hN : N.IsSymm) (u : Fin n → ℝ) :
    ((B.transpose *ᵥ u) ⬝ᵥ (H⁻¹ *ᵥ (N *ᵥ u))) ^ 2 ≤
      (H⁻¹ * N * H⁻¹ * N).trace * (B * B).trace *
        (u ⬝ᵥ (H *ᵥ u)) * (u ⬝ᵥ (H⁻¹ *ᵥ u)) := by
  have hΓ : 0 ≤ (H⁻¹ * N * H⁻¹ * N).trace := by
    rw [← whitened_connection_square H N hH hN]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hM : 0 ≤ u ⬝ᵥ (H *ᵥ u) := hH.posSemidef.dotProduct_mulVec_nonneg _
  have hb := compatible_transpose_inverse_energy H B hH hc u
  have he := compatible_connection_boundary_square H N hH hN (B.transpose *ᵥ u) u
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hM) hΓ
  exact he.trans (by nlinarith only [hh])

theorem radial_extra_young {E Γ Q U δ c : ℝ}
    (hΓ : 0 ≤ Γ) (hQ : 0 ≤ Q) (hU : 0 ≤ U) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (he : E ^ 2 ≤ c * Γ * Q * U ^ 2) :
    |2 * δ * E / (1 + δ * U) ^ 2| ≤
      Γ / (4 * (1 + δ * U)) + 4 * c * Q / (1 + δ * U) := by
  let f := 1 + δ * U
  have hf : 0 < f := by dsimp [f]; positivity
  have huf : δ * U ≤ f := by dsimp [f]; linarith
  have hp : (δ * U) ^ 2 ≤ f ^ 2 :=
    sq_le_sq₀ (mul_nonneg hδ hU) hf.le |>.mpr huf
  have hsq : (2 * δ * E) ^ 2 ≤ (4 * c * Γ * Q) * f ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * δ ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * c * Γ * Q by positivity)
    nlinarith only [h1, h2]
  have hbound : |2 * δ * E| ≤ (Γ / 4 + 4 * c * Q) * f := by
    have hr : 0 ≤ (Γ / 4 + 4 * c * Q) * f := by positivity
    have hgap := sq_nonneg (Γ / 4 - 4 * c * Q)
    have hm := mul_nonneg hgap (sq_nonneg f)
    nlinarith only [hsq, hr, hm, sq_abs (2 * δ * E)]
  have hh := div_le_div_of_nonneg_right hbound (sq_nonneg f)
  calc
    _ = |2 * δ * E| / f ^ 2 := by rw [abs_div, abs_of_pos (sq_pos_of_pos hf)]
    _ ≤ ((Γ / 4 + 4 * c * Q) * f) / f ^ 2 := hh
    _ = _ := by change _ = Γ / (4 * f) + 4 * c * Q / f; field_simp [hf.ne']

end KLSConstantImprovement.ActualCompatibleRadialExtra405
#print axioms KLSConstantImprovement.ActualCompatibleRadialExtra405.compatible_transpose_inverse_energy
#print axioms KLSConstantImprovement.ActualCompatibleRadialExtra405.compatible_radial_extra_square
#print axioms KLSConstantImprovement.ActualCompatibleRadialExtra405.radial_extra_young
