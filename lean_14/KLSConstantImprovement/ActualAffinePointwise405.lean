import KLSConstantImprovement.ActualAffineWhitening405

/-! The source affine connection square at an arbitrary positive metric.
The raw signed connection, positive mass and cross term are bound to the
same white source and target tensors before applying cyclic projection. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualAffinePointwise405
open KLS ActualQuarticThirdWhitening405 ActualQuarticCongruence405
open ActualAffineFiniteExpansion405 ActualAffineSlotAlgebra405 ActualAffineWhitening405
open ActualDirectCubicWhitening405 ActualDirectCubicMomentBinding405
open ActualSourceDirectCubicBalance405
open ActualFullSymmetricTensorOrdering MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem affine_pointwise_discount (H A : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hA : A.IsSymm) (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    affineSignedConnection H⁻¹ A N ≤ (A * H * A * rawGram H⁻¹ N).trace ∧
      ∀ t : ℝ, 0 ≤ ((A * H * A * rawGram H⁻¹ N).trace + 2 * affineSignedConnection H⁻¹ A N) / 3 -
        2 * t * affineCross H A T N + t ^ 2 * (H * rawGram H T).trace := by
  let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt H
  let R : Matrix (Fin n) (Fin n) ℝ := inverseSqrtMatrix H
  have hQ : Q.IsSymm := (CFC.sqrt_nonneg H).posSemidef.isHermitian.isSymm
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hQsq : Q * Q = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hunit : IsUnit Q := (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv Q hdet
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hRsq : R * R = H⁻¹ := by
    change (CFC.sqrt H)⁻¹ * (CFC.sqrt H)⁻¹ = H⁻¹
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hRtR : R.transpose * R = H⁻¹ := by rw [hR.eq, hRsq]
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hNs (a : Fin n) : (N a).IsSymm := Matrix.IsSymm.ext fun i j => hN23 a j i
  have hB : (Q * A * Q).IsSymm := by
    change (Q * A * Q).transpose = Q * A * Q
    simp only [Matrix.transpose_mul, hQ.eq, hA.eq, Matrix.mul_assoc]
  have hTw := whiteThirdSlice_full_symmetry Q hQ T hT12 hT23
  have hNw := whiteThirdSlice_full_symmetry R hR N hN12 hN23
  have hc := affine_cross_whitening Q R A hQ hR hA hQR hRQ T N hTs hNs
  have he1 := affine_signed_whitening Q R A hQR hRQ N
  have he2 := affine_mass_whitening Q R A hR hQR hRQ N
  have hw := direct_white_tensor_square Q hQ T hTs
  rw [hQsq] at hc hw
  rw [hRtR] at he1
  rw [hQsq, hRsq] at he2
  have hw' : cubicEnergy (whiteThirdSlice Q T) = (H * rawGram H T).trace := hw
  constructor
  · have hl := affine_signed_le_mass (Q * A * Q) hB (whiteThirdSlice R N) hNw.1 hNw.2
    rwa [he1, he2] at hl
  · intro t
    have htcyc (i j k : Fin n) : whiteThirdSlice Q T i j k = whiteThirdSlice Q T j k i :=
      (hTw.1 i j k).trans (hTw.2 j i k)
    have hp := affine_full_symmetric_square (Q * A * Q) hB (whiteThirdSlice R N)
      (whiteThirdSlice Q T) hNw.1 hNw.2 htcyc t
    rwa [he1, he2, hc, hw'] at hp

end KLSConstantImprovement.ActualAffinePointwise405

#print axioms KLSConstantImprovement.ActualAffinePointwise405.affine_pointwise_discount
