import KLSConstantImprovement.ActualAffineSlotAlgebra405
import KLSConstantImprovement.ActualDirectCubicMomentBinding405

/-! The affine trace contractions in opposite literal three-slot white
frames. The same Q and R act on all three tensor slots, with QR=RQ=I. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineWhitening405
open KLS ActualQuarticCompression405 ActualQuarticWhiteFrame405
open ActualQuarticCongruence405 ActualQuarticThirdWhitening405
open ActualDirectCubicWhitening405 ActualAffineFiniteExpansion405 ActualAffineSlotAlgebra405
open ActualFullSymmetricTensorOrdering MixedCubicRankSlicing FourthCubicProjectionDefect
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem sum_mixed_family_trace (Q R : Matrix (Fin n) (Fin n) ℝ)
    (U V : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    (∑ l, (mixFamily Q U l * mixFamily R V l).trace) =
      ∑ a, ∑ b, (Q.transpose * R) a b * (U a * V b).trace := by
  have hp (l : Fin n) : (mixFamily Q U l * mixFamily R V l).trace =
      ∑ a, ∑ b, (Q l a * R l b) * (U a * V b).trace := by
    simp only [mixFamily, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [hp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem trace_white_affine_cross (Q R A C D : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) :
    ((Q * C * Q) * (Q * A * Q) * (R * D * R)).trace =
      (C * (Q * Q) * A * D).trace := by
  calc
    _ = (Q * (C * (Q * Q) * A * (Q * R) * D * R)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Q * (C * (Q * Q) * A * D * R)).trace := by rw [hQR, Matrix.mul_one]
    _ = ((C * (Q * Q) * A * D * R) * Q).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc, hRQ, Matrix.mul_one]

theorem trace_white_affine_signed (Q R A C D : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) :
    ((Q * A * Q) * (R * C * R) * (Q * A * Q) * (R * D * R)).trace =
      (A * C * A * D).trace := by
  calc
    _ = (Q * (A * (Q * R) * C * (R * Q) * A * (Q * R) * D * R)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (Q * (A * C * A * D * R)).trace := by
      rw [hQR, hRQ, Matrix.mul_one, Matrix.mul_one, Matrix.mul_one]
    _ = ((A * C * A * D * R) * Q).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc, hRQ, Matrix.mul_one]

theorem affine_cross_whitening (Q R A : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.IsSymm) (hR : R.IsSymm) (hA : A.IsSymm)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (T N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ i, (T i).IsSymm) (hN : ∀ i, (N i).IsSymm) :
    pairing (whiteThirdSlice Q T) (secondAction (Q * A * Q) (whiteThirdSlice R N)) =
      affineCross (Q * Q) A T N := by
  have hTw := whiteThirdSlice_symmetric Q hQ T hT
  have hmix (l : Fin n) : mixFamily Q (fun a => T a * (Q * Q) * A) l =
      mixFamily Q T l * (Q * Q) * A := by
    simp only [mixFamily, Matrix.sum_mul, Matrix.smul_mul]
  have hcoef : Q.transpose * R = 1 := by rw [hQ.eq, hQR]
  have hterm (l : Fin n) : entryPair (whiteThirdSlice Q T l)
      (secondAction (Q * A * Q) (whiteThirdSlice R N) l) =
      (mixFamily Q T l * (Q * Q) * A * mixFamily R N l).trace := by
    rw [second_action_matrix, entryPair_eq_trace, (hTw l).eq]
    change ((Q * mixFamily Q T l * Q) * ((Q * A * Q) * (R * mixFamily R N l * R))).trace = _
    rw [← Matrix.mul_assoc]
    exact trace_white_affine_cross Q R A _ _ hQR hRQ
  have hQQ : (Q * Q).IsSymm := by
    change (Q * Q).transpose = Q * Q
    rw [Matrix.transpose_mul, hQ.eq]
  change (∑ l, entryPair (whiteThirdSlice Q T l)
    (secondAction (Q * A * Q) (whiteThirdSlice R N) l)) = _
  simp_rw [hterm]
  have hm := sum_mixed_family_trace Q R (fun a => T a * (Q * Q) * A) N
  simp only [hmix, hcoef, Matrix.one_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, one_mul] at hm
  rw [hm]
  unfold affineCross
  exact Finset.sum_congr rfl fun a _ =>
    trace_four_reverse _ _ _ _ (hT a) hQQ hA (hN a)

theorem affine_signed_whitening (Q R A : Matrix (Fin n) (Fin n) ℝ)
    (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    whiteAffineSigned (Q * A * Q) (whiteThirdSlice R N) =
      affineSignedConnection (R.transpose * R) A N := by
  have hmix (l : Fin n) : mixFamily R (fun a => A * N a) l = A * mixFamily R N l := by
    simp only [mixFamily, Matrix.mul_sum, Matrix.mul_smul]
  unfold whiteAffineSigned
  simp only [whiteThirdSlice, trace_white_affine_signed Q R A _ _ hQR hRQ]
  have hm := sum_mixed_family_trace R R (fun a => A * N a) (fun a => A * N a)
  simp only [hmix, ← Matrix.mul_assoc] at hm
  exact hm

theorem affine_mass_whitening (Q R A : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.IsSymm) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    whiteAffineMass (Q * A * Q) (whiteThirdSlice R N) =
      (A * (Q * Q) * A * rawGram (R * R) N).trace := by
  unfold whiteAffineMass
  rw [whiteGram_whiteThirdSlice R hR]
  have he : (Q * A * Q) * (Q * A * Q) = Q * (A * (Q * Q) * A) * Q := by
    simp only [Matrix.mul_assoc]
  rw [he, trace_inverse_congruences Q R _ _ hQR hRQ]

end KLSConstantImprovement.ActualAffineWhitening405

#print axioms KLSConstantImprovement.ActualAffineWhitening405.sum_mixed_family_trace
#print axioms KLSConstantImprovement.ActualAffineWhitening405.affine_cross_whitening
#print axioms KLSConstantImprovement.ActualAffineWhitening405.affine_signed_whitening
#print axioms KLSConstantImprovement.ActualAffineWhitening405.affine_mass_whitening
