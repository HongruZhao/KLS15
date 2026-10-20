import KLSConstantImprovement.ActualQuarticCoefficientWhitening405

/-! The quartic pointwise gap for an arbitrary positive definite H,
an arbitrary symmetric row family, and the literal fully symmetric
source third tensor. No geometric or analytic witness is supplied. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualQuarticPointwise405
open KLS ActualQuarticCompression405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualQuarticCoefficientWhitening405
variable {n : ℕ} {κ : Type*} [Fintype κ]
set_option maxHeartbeats 1500000

def quarticRawEnergy (H : Matrix (Fin n) (Fin n) ℝ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, H⁻¹ a b * entryPair (rawGramDerivative H T (N a)) (rawGramDerivative H T (N b))

def quarticRawHessian (H : Matrix (Fin n) (Fin n) ℝ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, H⁻¹ a b * entryPair (rawGram H T) (rawGramSecond T (N a) (N b))

def quarticRawCommutatorCharge (H : Matrix (Fin n) (Fin n) ℝ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ l, entrySquare
    (ambientGram (rowColumns (rowWhitening (CFC.sqrt H) T)) *
        doubleSlot (whiteThirdSlice (inverseSqrtMatrix H) N l) -
      doubleSlot (whiteThirdSlice (inverseSqrtMatrix H) N l) *
        ambientGram (rowColumns (rowWhitening (CFC.sqrt H) T)))

theorem quarticRawCommutatorCharge_nonnegative (H : Matrix (Fin n) (Fin n) ℝ)
    (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ quarticRawCommutatorCharge H T N :=
  Finset.sum_nonneg fun _ _ => entrySquare_nonneg _

theorem quartic_pointwise_commutator_square (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k)
    (hN23 : ∀ i j k, N i j k = N i k j) :
    (rawQuarticGradient H T * rawGram H⁻¹ N).trace + quarticRawHessian H T N -
      quarticRawEnergy H T N = (1 / 2 : ℝ) * quarticRawCommutatorCharge H T N := by
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
  have hNs (a : Fin n) : (N a).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hN23 a j i
  have he := raw_quartic_family_gap Q hQs T hT (whiteThirdSlice R N)
    (whiteThirdSlice_symmetric R hRs N hNs)
  rw [hQsq, unwhiten_slice_square_curvature Q R hQR hRQ hRs N hN12 hN23,
    hRsq] at he
  simp only [unwhiten_whiteThirdSlice Q R hQR hRQ N] at he
  rw [← raw_second_contraction_whitening (rawGram H T) T R N,
    ← raw_derivative_energy_whitening H T R N, hRtR] at he
  exact he

theorem quartic_pointwise_energy_le (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (T : κ → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k)
    (hN23 : ∀ i j k, N i j k = N i k j) :
    quarticRawEnergy H T N ≤
      (rawQuarticGradient H T * rawGram H⁻¹ N).trace + quarticRawHessian H T N := by
  have he := quartic_pointwise_commutator_square H hH T hT N hN12 hN23
  have hn := quarticRawCommutatorCharge_nonnegative H T N
  linarith

end KLSConstantImprovement.ActualQuarticPointwise405

#print axioms KLSConstantImprovement.ActualQuarticPointwise405.quarticRawCommutatorCharge_nonnegative
#print axioms KLSConstantImprovement.ActualQuarticPointwise405.quartic_pointwise_commutator_square
#print axioms KLSConstantImprovement.ActualQuarticPointwise405.quartic_pointwise_energy_le
