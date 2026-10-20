import KLSConstantImprovement.ActualCompatibleJacobianCoercivity405
import KLS.FrameHessianAlgebra

/-! The signed compatible Jacobian trace is the nonnegative Euclidean
square of its actual metric conjugate. This is the field used for the
global Hilbert weak limit; signed trace is not treated as convex on all
matrices. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWhitenedJacobianEnergy405
open KLS ActualCompatibleJacobianCoercivity405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def whitenedJacobian (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (inverseSqrtMatrix A)⁻¹ * B * inverseSqrtMatrix A

private theorem conjugate_frobenius_of_gram
    (R S A J B : Matrix (Fin n) (Fin n) ℝ) (hR : R.IsSymm) (hS : S.IsSymm)
    (hSS : S * S = A) (hRR : R * R = J) :
    matrixFrobeniusSq (S * B * R) = (A * B * J * B.transpose).trace := by
  rw [matrixFrobeniusSq_eq_trace_mul_transpose]
  simp only [Matrix.transpose_mul, hR.eq, hS.eq]
  calc
    _ = (S * (B * (R * R) * B.transpose) * S).trace := by simp only [mul_assoc]
    _ = ((B * (R * R) * B.transpose) * S * S).trace :=
      (Matrix.trace_mul_cycle (B * (R * R) * B.transpose) S S).symm
    _ = ((B * (R * R) * B.transpose) * (S * S)).trace := by rw [mul_assoc]
    _ = ((S * S) * (B * (R * R) * B.transpose)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [hSS, hRR]; simp only [mul_assoc]

theorem whitenedJacobian_frobenius (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hc : (A * B).IsSymm) :
    matrixFrobeniusSq (whitenedJacobian A B) = (B * B).trace := by
  let R := inverseSqrtMatrix A
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm A
  have hS : S.IsSymm := hR.inv
  have hSS : S * S = A := by
    have hg : S.transpose * S = A := inverseSqrtMatrix_inverse_gram hA
    simpa only [hS.eq] using hg
  have hRR : R * R = A⁻¹ := by
    unfold R inverseSqrtMatrix
    rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  exact (conjugate_frobenius_of_gram R S A A⁻¹ B hR hS hSS hRR).trans
    (compatible_jacobian_trace_identity A B hA hc).symm

end KLSConstantImprovement.ActualWhitenedJacobianEnergy405
#print axioms KLSConstantImprovement.ActualWhitenedJacobianEnergy405.whitenedJacobian_frobenius
