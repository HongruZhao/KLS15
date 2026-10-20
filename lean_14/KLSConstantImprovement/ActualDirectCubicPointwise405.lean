import KLSConstantImprovement.ActualDirectCubicCoefficients405

/-! Actual positive/inverse square roots bind the direct cubic finite
commutator square at every positive definite Hessian. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualDirectCubicPointwise405
open KLS ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualDirectCubicWhitening405 ActualDirectCubicCoefficients405 ActualDirectCubicCommutator405
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def directCubicCommutatorCharge (H : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ p, ∑ a, matrixFrobeniusSq
    (whiteThirdSlice (CFC.sqrt H) T p * whiteThirdSlice (inverseSqrtMatrix H) N a -
      whiteThirdSlice (inverseSqrtMatrix H) N a * whiteThirdSlice (CFC.sqrt H) T p)

theorem directCubicCommutatorCharge_nonnegative (H : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : 0 ≤ directCubicCommutatorCharge H T N := by
  unfold directCubicCommutatorCharge matrixFrobeniusSq
  positivity

theorem direct_cubic_pointwise_commutator_square (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    (rawGram H T * rawGram H⁻¹ N).trace - directHalfEnergy H T N =
      (1 / 2 : ℝ) * directCubicCommutatorCharge H T N := by
  let Q : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt H
  let R : Matrix (Fin n) (Fin n) ℝ := inverseSqrtMatrix H
  have hQs : Q.IsSymm := (CFC.sqrt_nonneg H).posSemidef.isHermitian.isSymm
  have hRs : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hQsq : Q * Q = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hunit : IsUnit Q := (CFC.isUnit_sqrt_iff H hH.posSemidef.nonneg).mpr hH.isUnit
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hQR : Q * R = 1 := Matrix.mul_nonsing_inv Q hdet
  have hRQ : R * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hRsq : R * R = H⁻¹ := by
    change (CFC.sqrt H)⁻¹ * (CFC.sqrt H)⁻¹ = H⁻¹
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hRtR : R.transpose * R = H⁻¹ := by rw [hRs.eq, hRsq]
  have hNsym (a : Fin n) : (N a).IsSymm := Matrix.IsSymm.ext fun i j => hN23 a j i
  have hmixsym (a : Fin n) : (mixFamily R N a).IsSymm := by
    change (∑ b, R a b • N b).transpose = ∑ b, R a b • N b
    simp only [Matrix.transpose_sum, Matrix.transpose_smul]
    exact Finset.sum_congr rfl fun b _ => by rw [(hNsym b).eq]
  have hA := whiteThirdSlice_full_symmetry Q hQs T hT12 hT23
  have hM := whiteThirdSlice_full_symmetry R hRs N hN12 hN23
  have hc := direct_white_curvature_binding Q R hQs hRs hQR hRQ T N
  rw [hQsq, hRsq] at hc
  simp only [ActualQuarticWhiteFrame405.whiteGram] at hc
  have hh : (∑ a, ∑ i, ∑ j, whiteThirdSlice R N a i j *
      (whiteThirdSlice Q T i * whiteThirdSlice R N a * whiteThirdSlice Q T j).trace) =
      directHalfEnergy H T N := by
    calc
      _ = ∑ a, ActualQuarticCompression405.entryPair (mixFamily R N a)
          (directLinear (Q * Q) T (mixFamily R N a)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact direct_white_half_cross_single Q R hQs hRs hQR hRQ T _ (hmixsym a)
      _ = ∑ a, ∑ b, (R.transpose * R) a b *
          ActualQuarticCompression405.entryPair (N a) (directLinear (Q * Q) T (N b)) :=
        direct_half_coefficient_whitening (Q * Q) T R N
      _ = _ := by rw [hRtR, hQsq]; rfl
  have he := full_tensor_direct_commutator_square (whiteThirdSlice Q T) (whiteThirdSlice R N)
    hA.1 hA.2 hM.1 hM.2
  rw [hc, hh] at he
  exact he

theorem direct_cubic_cross_energy_le_twice_curvature (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    directCrossEnergy H T N ≤ 2 * (rawGram H T * rawGram H⁻¹ N).trace := by
  have he := direct_cubic_pointwise_commutator_square H hH T N hT12 hT23 hN12 hN23
  have hn := directCubicCommutatorCharge_nonnegative H T N
  have hNs (a : Fin n) : (N a).IsSymm := Matrix.IsSymm.ext fun i j => hN23 a j i
  rw [directCrossEnergy_eq_twice_half H T N hNs]
  linarith

end KLSConstantImprovement.ActualDirectCubicPointwise405

#print axioms KLSConstantImprovement.ActualDirectCubicPointwise405.directCubicCommutatorCharge_nonnegative
#print axioms KLSConstantImprovement.ActualDirectCubicPointwise405.direct_cubic_pointwise_commutator_square
#print axioms KLSConstantImprovement.ActualDirectCubicPointwise405.direct_cubic_cross_energy_le_twice_curvature
