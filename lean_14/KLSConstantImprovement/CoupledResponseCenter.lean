import KLSConstantImprovement.ActualResponseFullSymCoercivity405
import KLSConstantImprovement.CoupledCenterMetric
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.CoupledResponseCenter
open KLS ActualWeightedWhiteFamily405 ActualResponseProductionHalfSquare405
open ActualResponseProductionAlgebra405 ActualFullSymmetricProduction ActualTensorRowWhite405
open ActualFullSymmetricTensorOrdering ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualDirectCubicWhitening405 MixedCubicRankSlicing FourthCubicProjectionDefect
open ActualSourceQuarticBinding405 CoupledCenterMetric
variable {n : ℕ}
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
theorem response_fullSym_production_lower_center (H P F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j)
    (hT12 : ∀ i j k, T i j k = T j i k) (hT23 : ∀ i j k, T i j k = T i k j)
    (hD : ∀ i, (H * D i).IsSymm) :
    (H * (F * P * F.transpose)).trace +
      4 * (H * matrixTraceGram H T).trace / 3 -
        ((F * H * F.transpose) * matrixTraceGram H⁻¹ N).trace +
          3 * cubicEnergy (hook (firstAction ((inverseSqrtMatrix H)⁻¹ * F * (inverseSqrtMatrix H)⁻¹).transpose
            (whiteThirdSlice (inverseSqrtMatrix H) N))) / 2 +
            (3/2:ℝ) * cubicEnergy (fun i j k =>
              cyclicAverage (firstAction ((inverseSqrtMatrix H)⁻¹*F*(inverseSqrtMatrix H)⁻¹)
                (whiteThirdSlice (inverseSqrtMatrix H) N)) i j k-
                  (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k) ≤
              (H * responseProductionMatrix H H⁻¹ P F (mixFamily F N) D T).trace := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hunit : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hunit
  have hSR : S * R = 1 := Matrix.nonsing_inv_mul R hunit
  have hSS : S * S = H := by
    have he : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun j k => hN23 i k j
  have hTs (i : Fin n) : (T i).IsSymm := Matrix.IsSymm.ext fun j k => hT23 i k j
  have hNc (i j k : Fin n) : N i j k = N j k i := (hN12 i j k).trans (hN23 j i k)
  have hTc (i j k : Fin n) : T i j k = T j k i := (hT12 i j k).trans (hT23 j i k)
  let A : Fin n → Matrix (Fin n) (Fin n) ℝ := fun i => H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H)
  have hHJ : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)
  have hA (i : Fin n) : (H * A i).IsSymm := by
    have hNF := mixFamily_symmetric F N hNs i
    have hTHT : (H * T i * H).IsSymm := by
      change (H * T i * H).transpose = _
      simp only [Matrix.transpose_mul, hH.isHermitian.isSymm.eq, (hTs i).eq, Matrix.mul_assoc]
    change (H * (H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H))).IsSymm
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, hHJ, Matrix.one_mul]
    change (mixFamily F N i - (2 : ℝ) • (H * (T i * H))).IsSymm
    change (mixFamily F N i - (2 : ℝ) • (H * (T i * H))).transpose = _
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, hNF.eq,
      Matrix.transpose_mul, hH.isHermitian.isSymm.eq, (hTs i).eq, Matrix.mul_assoc]
  have hE := metricWhiteFamily_energy H hH A hA
  rw [metricWhiteFamily_response_error H F hH N T] at hE
  have hW : cubicEnergy (whiteThirdSlice S T) = (H * matrixTraceGram H T).trace := by
    rw [cubicEnergy_eq_trace_whiteGram _ (whiteThirdSlice_symmetric S hS T hTs),
      whiteGram_whiteThirdSlice S hS T, Matrix.trace_mul_cycle, hSS, rawGram_eq_matrixTraceGram]
  have hRow := white_row_tensor_energy S R F hS hR hSR hRS N hNs
  rw [hSS, hRR, rawGram_eq_matrixTraceGram] at hRow
  have hCoercive := actual_tensor_error_decomposition (S * F * S) (whiteThirdSlice R N) (whiteThirdSlice S T)
    (whiteThirdSlice_cyclic R hR N hNc) (whiteThirdSlice_cyclic S hS T hTc)
  change cubicEnergy (fun i j k => firstAction (S * F * S) (whiteThirdSlice R N) i j k -
    2 * whiteThirdSlice S T i j k) = (H * compatibleTraceGram A).trace at hE
  rw [hW, hRow, hE] at hCoercive
  have hHalf := response_production_half_square H P F hH (mixFamily F N) D T
    (mixFamily_symmetric F N hNs) hTs hD
  change (H * (F * P * F.transpose)).trace + (H * compatibleTraceGram A).trace / 2 ≤ _ at hHalf
  linarith only [hHalf, hCoercive]


theorem response_fullSym_coarse_center (H P F : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hP : P.PosSemidef)
    (N D T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k=N j i k) (hN23 : ∀ i j k, N i j k=N i k j)
    (hT12 : ∀ i j k, T i j k=T j i k) (hT23 : ∀ i j k, T i j k=T i k j)
    (hD : ∀ i, (H*D i).IsSymm) :
    4*(H*matrixTraceGram H T).trace/3+
      (3/2:ℝ)*cubicEnergy (fun i j k => whiteProjectedAction H F N i j k-
        (2/3:ℝ)*whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i j k) ≤
      (H*responseProductionMatrix H H⁻¹ P F (mixFamily F N) D T).trace+
        ((F*H*F.transpose)*(P+matrixTraceGram H⁻¹ N)).trace := by
  have he := response_fullSym_production_lower_center H P F hH N D T hN12 hN23 hT12 hT23 hD
  have hh := cubicEnergy_nonneg (hook (firstAction ((inverseSqrtMatrix H)⁻¹*F*(inverseSqrtMatrix H)⁻¹).transpose
    (whiteThirdSlice (inverseSqrtMatrix H) N)))
  have hFP : (F*P*F.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hP.conjTranspose_mul_mul_same F.transpose
  have hpcol := trace_mul_nonneg_of_posSemidef hH.posSemidef hFP
  have hFH : (F*H*F.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.transpose_transpose] using
      hH.posSemidef.conjTranspose_mul_mul_same F.transpose
  have hprow := trace_mul_nonneg_of_posSemidef hFH hP
  dsimp only [whiteProjectedAction]
  rw [Matrix.mul_add,Matrix.trace_add]
  linarith only [he,hh,hpcol,hprow]

end KLSConstantImprovement.CoupledResponseCenter
#print axioms KLSConstantImprovement.CoupledResponseCenter.response_fullSym_production_lower_center

#print axioms KLSConstantImprovement.CoupledResponseCenter.response_fullSym_coarse_center
