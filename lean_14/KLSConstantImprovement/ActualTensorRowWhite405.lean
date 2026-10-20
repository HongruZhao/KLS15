import KLSConstantImprovement.ActualDirectCubicWhitening405
import KLSConstantImprovement.ActualFullSymmetricProduction

/-! Exact opposite-frame row tensor energies and pairings. The same
root acts in all three tensor slots. The row matrix need not be symmetric. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualTensorRowWhite405
open KLS ActualQuarticCompression405 ActualQuarticWhiteFrame405 ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualDirectCubicWhitening405 ActualFullSymmetricTensorOrdering
open MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def crossTraceGram (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (T i * N j).trace

theorem firstAction_eq_mixFamily (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : firstAction B N = mixFamily B N := by
  funext i j k
  simp only [firstAction, mixFamily, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem mixFamily_symmetric (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ i, (N i).IsSymm) (i : Fin n) :
    (mixFamily B N i).IsSymm := by
  change (∑ a, B i a • N a).transpose = ∑ a, B i a • N a
  simp only [Matrix.transpose_sum, Matrix.transpose_smul, (hN _).eq]

theorem cubicEnergy_eq_trace_whiteGram (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i, (N i).IsSymm) : cubicEnergy N = (whiteGram N).trace := by
  change (∑ i, matrixFrobeniusSq (N i)) = ∑ i, (N i * N i).trace
  apply Finset.sum_congr rfl
  intro i _
  rw [matrixFrobeniusSq_eq_trace_mul_transpose, (hN i).eq]

theorem cubicEnergy_firstAction (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ i, (N i).IsSymm) :
    cubicEnergy (firstAction B N) = (B * whiteGram N * B.transpose).trace := by
  rw [firstAction_eq_mixFamily, cubicEnergy_eq_trace_whiteGram _ (mixFamily_symmetric B N hN),
    whiteGram_mixFamily]

theorem pairing_firstAction_transpose_trace (B : Matrix (Fin n) (Fin n) ℝ)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    pairing T (firstAction B.transpose N) = (B * crossTraceGram T N).trace := by
  rw [firstAction_eq_mixFamily]
  have hp : pairing T (mixFamily B.transpose N) = ∑ i, entryPair (T i) (mixFamily B.transpose N i) := rfl
  rw [hp]
  simp only [entryPair_eq_trace, (hT _).eq, mixFamily, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [crossTraceGram, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]

theorem crossTraceGram_white (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    crossTraceGram (whiteThirdSlice Q T) (whiteThirdSlice R N) =
      Q * crossTraceGram T N * R.transpose := by
  ext i j
  change ((Q * mixFamily Q T i * Q) * (R * mixFamily R N j * R)).trace = _
  rw [trace_inverse_congruences Q R _ _ hQR hRQ]
  simp only [mixFamily, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    crossTraceGram, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem white_row_tensor_pairing (Q R U : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hT : ∀ i, (T i).IsSymm) :
    pairing (whiteThirdSlice Q T)
      (firstAction (Q * U * Q).transpose (whiteThirdSlice R N)) =
        (U * (Q * Q) * crossTraceGram T N).trace := by
  rw [pairing_firstAction_transpose_trace _ _ _ (whiteThirdSlice_symmetric Q hQ T hT),
    crossTraceGram_white Q R hQR hRQ, hR.eq]
  calc
    _ = ((Q * U * (Q * Q) * crossTraceGram T N) * R).trace := by simp only [Matrix.mul_assoc]
    _ = (R * (Q * U * (Q * Q) * crossTraceGram T N)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [← Matrix.mul_assoc, hRQ, Matrix.one_mul]

theorem white_row_tensor_energy (Q R U : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ i, (N i).IsSymm) :
    cubicEnergy (firstAction (Q * U * Q).transpose (whiteThirdSlice R N)) =
      ((U * (Q * Q) * U.transpose) * rawGram (R * R) N).trace := by
  rw [cubicEnergy_firstAction _ _ (whiteThirdSlice_symmetric R hR N hN), Matrix.transpose_transpose,
    whiteGram_whiteThirdSlice R hR N]
  rw [Matrix.trace_mul_cycle]
  have hb : (Q * U * Q) * (Q * U * Q).transpose = Q * (U * (Q * Q) * U.transpose) * Q := by
    simp only [Matrix.transpose_mul, hQ.eq, Matrix.mul_assoc]
  rw [hb]
  exact trace_inverse_congruences Q R _ _ hQR hRQ

theorem tensor_pairing_square_le (T N : Fin n → Fin n → Fin n → ℝ) :
    pairing T N ^ 2 ≤ cubicEnergy T * cubicEnergy N := by
  have hp (t : ℝ) : 0 ≤ cubicEnergy T * (t * t) + (-2 * pairing T N) * t + cubicEnergy N := by
    have he := cubicEnergy_sub_mul N T t
    have hn := cubicEnergy_nonneg (fun i j k => N i j k - t * T i j k)
    nlinarith only [he, hn]
  have hd := discrim_le_zero hp
  simp only [discrim] at hd
  nlinarith only [hd]

end KLSConstantImprovement.ActualTensorRowWhite405
#print axioms KLSConstantImprovement.ActualTensorRowWhite405.white_row_tensor_pairing
#print axioms KLSConstantImprovement.ActualTensorRowWhite405.white_row_tensor_energy
#print axioms KLSConstantImprovement.ActualTensorRowWhite405.tensor_pairing_square_le
