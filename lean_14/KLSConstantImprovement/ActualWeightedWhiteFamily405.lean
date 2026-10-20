import KLSConstantImprovement.ActualTensorRowWhite405
import KLSConstantImprovement.ActualResponseCompletionWhitening405
import KLSConstantImprovement.ActualWhitenedJacobianSymmetry405
import KLSConstantImprovement.ActualResponseProductionHalfSquare405

/-! Exact three-slot whitening of a compatible row family and of the
response error. No row/column contraction is interchanged. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace KLSConstantImprovement.ActualWeightedWhiteFamily405
open KLS ActualTensorRowWhite405 ActualQuarticThirdWhitening405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualFullSymmetricTensorOrdering
open ActualResponseProductionAlgebra405 ActualResponseCompletionWhitening405
open ActualWhitenedJacobianEnergy405 ActualWhitenedJacobianSymmetry405
open MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

theorem mixFamily_mul (A B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    mixFamily A (mixFamily B N) = mixFamily (A * B) N := by
  funext i
  simp only [mixFamily, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem mixFamily_congruence (M Q R : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    mixFamily M (fun i => Q * N i * R) = fun i => Q * mixFamily M N i * R := by
  funext i
  simp only [mixFamily, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem mixFamily_sub_smul (M : Matrix (Fin n) (Fin n) ℝ)
    (A B : Fin n → Matrix (Fin n) (Fin n) ℝ) (q : ℝ) :
    mixFamily M (fun i => A i - q • B i) = fun i => mixFamily M A i - q • mixFamily M B i := by
  funext i
  simp only [mixFamily, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, mul_comm]

def metricWhiteFamily (H : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Matrix (Fin n) (Fin n) ℝ :=
  mixFamily (inverseSqrtMatrix H)⁻¹ (fun i => whitenedJacobian H (A i))

theorem metricWhiteFamily_energy (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (H * A i).IsSymm) :
    cubicEnergy (metricWhiteFamily H A) = (H * compatibleTraceGram A).trace := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hSS : S * S = H := by
    have he : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH))
  have hGram : whiteGram (fun i => whitenedJacobian H (A i)) = compatibleTraceGram A := by
    ext i j
    exact trace_product_similarity S R (A i) (A j) hRS
  change cubicEnergy (mixFamily S (fun i => whitenedJacobian H (A i))) = _
  rw [cubicEnergy_eq_trace_whiteGram _ (mixFamily_symmetric S _ (fun i => whitenedJacobian_isSymm H (A i) hH (hA i))),
    whiteGram_mixFamily, hGram, hS.eq]
  calc
    _ = (S * S * compatibleTraceGram A).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (S * compatibleTraceGram A) S
    _ = _ := by rw [hSS]

theorem metricWhiteFamily_response_error (H F : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (N T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    metricWhiteFamily H (fun i => H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H)) =
      fun i a b => firstAction ((inverseSqrtMatrix H)⁻¹ * F * (inverseSqrtMatrix H)⁻¹)
        (whiteThirdSlice (inverseSqrtMatrix H) N) i a b -
          2 * whiteThirdSlice (inverseSqrtMatrix H)⁻¹ T i a b := by
  let R := inverseSqrtMatrix H
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm H
  have hS : S.IsSymm := hR.inv
  have hSS : S * S = H := by
    have he : S.transpose * S = H := inverseSqrtMatrix_inverse_gram hH
    simpa only [hS.eq] using he
  have hunit : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hH)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hunit
  have hSR : S * R = 1 := Matrix.nonsing_inv_mul R hunit
  have hRR : R * R = H⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg]
  have hSJ : S * H⁻¹ = R := by rw [← hRR, ← Matrix.mul_assoc, hSR, Matrix.one_mul]
  have hHR : H * R = S := by rw [← hSS, Matrix.mul_assoc, hSR, Matrix.mul_one]
  have hw (i : Fin n) : whitenedJacobian H (H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H)) =
      R * mixFamily F N i * R - (2 : ℝ) • (S * T i * S) := by
    change S * (H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H)) * R = _
    have hn : S * (H⁻¹ * mixFamily F N i) * R = R * mixFamily F N i * R := by
      simp only [← Matrix.mul_assoc, hSJ]
    have ht : S * (T i * H) * R = S * T i * S := by
      simp only [Matrix.mul_assoc, hHR]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hn, ht]
  have hb : firstAction (S * F * S) (whiteThirdSlice R N) =
      fun i => R * mixFamily (S * F) N i * R := by
    rw [firstAction_eq_mixFamily, whiteThirdSlice_eq_mix, mixFamily_mul]
    have hBR : (S * F * S) * R = S * F := by simp only [Matrix.mul_assoc, hSR, Matrix.mul_one]
    rw [hBR]
    exact mixFamily_congruence (S * F) R R N
  change mixFamily S (fun i => whitenedJacobian H (H⁻¹ * mixFamily F N i - (2 : ℝ) • (T i * H))) = _
  simp_rw [hw]
  rw [mixFamily_sub_smul, mixFamily_congruence S R R (mixFamily F N), mixFamily_mul,
    mixFamily_congruence S S S T]
  rw [hb]
  rfl

end KLSConstantImprovement.ActualWeightedWhiteFamily405
#print axioms KLSConstantImprovement.ActualWeightedWhiteFamily405.metricWhiteFamily_energy
#print axioms KLSConstantImprovement.ActualWeightedWhiteFamily405.metricWhiteFamily_response_error
