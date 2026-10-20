import KLSConstantImprovement.ActualAffineFiniteExpansion405
import KLSConstantImprovement.ActualFullSymmetricTensorOrdering
import KLS.SteinMatrixContraction

/-! Literal slot norms and signed pairings for a symmetric matrix acting
on a full symmetric source tensor. The cyclic projection retains the
connection discount without assuming that its signed pairing is positive. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualAffineSlotAlgebra405
open KLS MixedCubicRankSlicing FourthCubicProjectionDefect
open ActualFullSymmetricTensorOrdering ActualQuarticCompression405
open ActualQuarticWhiteFrame405 ActualQuarticThirdWhitening405
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def thirdAction (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → Fin n → ℝ :=
  fun i j k => ∑ a, B k a * N i j a

def whiteAffineSigned (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, (B * N i * B * N i).trace

def whiteAffineMass (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (B * B * whiteGram N).trace

theorem second_action_matrix (B : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    secondAction B N i = B * N i := rfl

theorem third_action_matrix (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    thirdAction B N i = N i * B := by
  ext j k
  simp only [thirdAction, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [hB.apply a k]; ring

theorem second_third_pairing (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ i, (N i).IsSymm) :
    pairing (secondAction B N) (thirdAction B N) = whiteAffineSigned B N := by
  change (∑ i, entryPair (secondAction B N i) (thirdAction B N i)) = _
  simp only [second_action_matrix, third_action_matrix B hB, entryPair_eq_trace,
    Matrix.transpose_mul, hB.eq, (hN _).eq, whiteAffineSigned]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (N i) (B * N i * B)

theorem second_action_cyclic_signed (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ) (hN : ∀ i, (N i).IsSymm)
    (hcyc : ∀ i j k, N i j k = N j k i) :
    cyclicPairing (secondAction B N) = whiteAffineSigned B N := by
  have hr : (fun i j k => secondAction B N j k i) = thirdAction B N := by
    funext i j k
    unfold secondAction thirdAction
    apply Finset.sum_congr rfl
    intro a _
    rw [hcyc j a i, hcyc a i j]
  unfold cyclicPairing
  rw [hr, tensor_pairing_comm]
  exact second_third_pairing B hB N hN

theorem second_action_mass (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    cubicEnergy (secondAction B N) = whiteAffineMass B N := by
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun j k => hN23 i k j
  have hpoint (i : Fin n) : matrixFrobeniusSq (B * N i) = (B * B * (N i * N i)).trace := by
    rw [matrixFrobeniusSq_eq_trace_mul_transpose, Matrix.transpose_mul, hB.eq, (hNs i).eq]
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle B (N i * N i) B
  change (∑ i, matrixFrobeniusSq (B * N i)) = _
  simp_rw [hpoint]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, full_symmetric_slice_square N hN12 hN23]
  rfl

theorem affine_cyclic_projection_energy (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    3 * cubicEnergy (cyclicAverage (secondAction B N)) =
      whiteAffineMass B N + 2 * whiteAffineSigned B N := by
  have hNs (i : Fin n) : (N i).IsSymm := Matrix.IsSymm.ext fun j k => hN23 i k j
  have hcyc (i j k : Fin n) : N i j k = N j k i :=
    (hN12 i j k).trans (hN23 j i k)
  have hp := cyclic_projection_energy (secondAction B N)
  rw [second_action_mass B hB N hN12 hN23,
    second_action_cyclic_signed B hB N hNs hcyc] at hp
  exact hp

theorem affine_signed_le_mass (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j) :
    whiteAffineSigned B N ≤ whiteAffineMass B N := by
  have hp := affine_cyclic_projection_energy B hB N hN12 hN23
  have hl := cyclicAverage_energy_le (secondAction B N)
  rw [second_action_mass B hB N hN12 hN23] at hl
  linarith

theorem affine_full_symmetric_square (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (N T : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hN12 : ∀ i j k, N i j k = N j i k) (hN23 : ∀ i j k, N i j k = N i k j)
    (hTcyc : ∀ i j k, T i j k = T j k i) (t : ℝ) :
    0 ≤ (whiteAffineMass B N + 2 * whiteAffineSigned B N) / 3 -
      2 * t * pairing T (secondAction B N) + t ^ 2 * cubicEnergy T := by
  have hn := cubicEnergy_nonneg (fun i j k => cyclicAverage (secondAction B N) i j k - t * T i j k)
  rw [cubicEnergy_sub_mul, pairing_cyclicAverage T _ hTcyc] at hn
  have hp := affine_cyclic_projection_energy B hB N hN12 hN23
  nlinarith

end KLSConstantImprovement.ActualAffineSlotAlgebra405

#print axioms KLSConstantImprovement.ActualAffineSlotAlgebra405.affine_cyclic_projection_energy
#print axioms KLSConstantImprovement.ActualAffineSlotAlgebra405.affine_signed_le_mass
#print axioms KLSConstantImprovement.ActualAffineSlotAlgebra405.affine_full_symmetric_square
