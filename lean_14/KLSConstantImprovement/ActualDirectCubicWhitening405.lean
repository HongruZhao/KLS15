import KLSConstantImprovement.ActualSourceQuarticBinding405
import KLSConstantImprovement.ActualDirectCubicCommutator405

/-! Literal direct-cubic contractions in opposite full three-slot white
frames. Both tensors use a single matrix in all three tensor slots. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualDirectCubicWhitening405
open KLS ActualQuarticCompression405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualQuarticCoefficientWhitening405 ActualDirectCubicCommutator405
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem whiteThirdSlice_full_symmetry (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT12 : ∀ i j k, T i j k = T j i k)
    (hT23 : ∀ i j k, T i j k = T i k j) :
    (∀ i j k, whiteThirdSlice Q T i j k = whiteThirdSlice Q T j i k) ∧
      (∀ i j k, whiteThirdSlice Q T i j k = whiteThirdSlice Q T i k j) := by
  have hTs (a : Fin n) : (T a).IsSymm := Matrix.IsSymm.ext fun i j => hT23 a j i
  have hs := whiteThirdSlice_symmetric Q hQ T hTs
  have hc : ∀ i j k, whiteThirdSlice Q T i j k = whiteThirdSlice Q T j k i := by
    apply whiteThirdSlice_cyclic Q hQ T
    intro i j k
    exact (hT12 i j k).trans (hT23 j i k)
  exact ⟨fun i j k => (hc i j k).trans ((hs j).apply i k),
    fun i j k => (hs i).apply k j⟩

theorem whiteGram_symmetric (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (whiteGram T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact Matrix.trace_mul_comm (T j) (T i)

theorem whiteGram_whiteThirdSlice (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.IsSymm)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    whiteGram (whiteThirdSlice Q T) = Q * rawGram (Q * Q) T * Q := by
  rw [whiteThirdSlice_eq_mix, whiteGram_mixFamily, ← rawGram_eq_white Q T, hQ.eq]

theorem trace_inverse_congruences (Q R C D : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) :
    ((Q * C * Q) * (R * D * R)).trace = (C * D).trace := by
  calc
    _ = (Q * (C * (Q * R) * D * R)).trace := by simp only [Matrix.mul_assoc]
    _ = (Q * (C * D * R)).trace := by rw [hQR, Matrix.mul_one]
    _ = ((C * D * R) * Q).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc, hRQ, Matrix.mul_one]

theorem entryPair_inverse_congruences (Q R C D : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hC : C.IsSymm)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) :
    entryPair (Q * C * Q) (R * D * R) = entryPair C D := by
  rw [entryPair_eq_trace, entryPair_eq_trace, Matrix.transpose_mul, Matrix.transpose_mul,
    hQ.eq, hC.eq]
  simpa only [Matrix.mul_assoc] using trace_inverse_congruences Q R C D hQR hRQ

theorem direct_white_curvature_binding (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, whiteGram (whiteThirdSlice Q T) i j * whiteGram (whiteThirdSlice R N) i j) =
      (rawGram (Q * Q) T * rawGram (R * R) N).trace := by
  change entryPair (whiteGram (whiteThirdSlice Q T)) (whiteGram (whiteThirdSlice R N)) = _
  have hG : (rawGram (Q * Q) T).IsSymm := by
    rw [rawGram_eq_white]
    exact whiteGram_symmetric _
  rw [whiteGram_whiteThirdSlice Q hQ, whiteGram_whiteThirdSlice R hR,
    entryPair_inverse_congruences Q R _ _ hQ hR hG hQR hRQ, entryPair_eq_trace, hG.eq]

def directLinear (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => (T i * C * T j * H).trace

theorem directLinear_mix_rows (H : Matrix (Fin n) (Fin n) ℝ)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (C Q : Matrix (Fin n) (Fin n) ℝ) :
    directLinear H (mixFamily Q T) C = Q * directLinear H T C * Q.transpose := by
  ext i j
  simp only [directLinear, mixFamily, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem directLinear_opposite_matrix_congruence (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    directLinear 1 (rowWhitening Q T) (R * P * R) = directLinear (Q * Q) T P := by
  ext i j
  change ((Q * T i * Q) * (R * P * R) * (Q * T j * Q) * 1).trace = _
  rw [Matrix.mul_one]
  calc
    _ = (Q * (T i * (Q * R) * P * (R * Q) * T j * Q)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Q * (T i * P * T j * Q)).trace := by rw [hQR, hRQ, Matrix.mul_one, Matrix.mul_one]
    _ = ((T i * P * T j * Q) * Q).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [directLinear, Matrix.mul_assoc]

theorem directLinear_whiteThirdSlice (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    directLinear 1 (whiteThirdSlice Q T) (R * P * R) =
      Q * directLinear (Q * Q) T P * Q := by
  rw [whiteThirdSlice_eq_mix, directLinear_mix_rows,
    directLinear_opposite_matrix_congruence Q R hQR hRQ T P, hQ.eq]

theorem direct_white_half_cross_single (Q R : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T : Fin n → Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsSymm) :
    (∑ i, ∑ j, (R * P * R) i j *
      ((whiteThirdSlice Q T i) * (R * P * R) * (whiteThirdSlice Q T j)).trace) =
      entryPair P (directLinear (Q * Q) T P) := by
  have hD : (fun i j => ((whiteThirdSlice Q T i) * (R * P * R) * (whiteThirdSlice Q T j)).trace) =
      directLinear 1 (whiteThirdSlice Q T) (R * P * R) := by
    funext i j
    simp only [directLinear, Matrix.mul_one]
  change entryPair (R * P * R)
    (fun i j => ((whiteThirdSlice Q T i) * (R * P * R) * (whiteThirdSlice Q T j)).trace) = _
  rw [hD, directLinear_whiteThirdSlice Q R hQ hQR hRQ,
    entryPair_inverse_congruences R Q P _ hR hQ hP hRQ hQR]

end KLSConstantImprovement.ActualDirectCubicWhitening405

#print axioms KLSConstantImprovement.ActualDirectCubicWhitening405.whiteThirdSlice_full_symmetry
#print axioms KLSConstantImprovement.ActualDirectCubicWhitening405.direct_white_curvature_binding
#print axioms KLSConstantImprovement.ActualDirectCubicWhitening405.directLinear_whiteThirdSlice
#print axioms KLSConstantImprovement.ActualDirectCubicWhitening405.direct_white_half_cross_single
