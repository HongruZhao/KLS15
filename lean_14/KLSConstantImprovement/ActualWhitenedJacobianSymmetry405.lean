import KLSConstantImprovement.ActualWhitenedJacobianEnergy405

/-! Compatibility becomes literal symmetry after the actual metric
conjugation, and inverse conjugation recovers the raw Jacobian. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualWhitenedJacobianSymmetry405
open KLS ActualWhitenedJacobianEnergy405
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

private theorem conjugate_symm_of_inverse_pair
    (A B R S : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hc : (A * B).IsSymm) (hR : R.IsSymm) (hS : S.IsSymm)
    (hSS : S * S = A) (hRS : R * S = 1) (hSR : S * R = 1) : (S * B * R).IsSymm := by
  have hrel : B.transpose * A = A * B := by
    simpa only [Matrix.transpose_mul, hA.eq] using hc.eq
  have hRA : R * A = S := by rw [← hSS, ← mul_assoc, hRS, one_mul]
  have hAR : A * R = S := by rw [← hSS, mul_assoc, hSR, mul_one]
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => R * M * R) hrel
  have hl : R * (B.transpose * A) * R = R * B.transpose * S := by simp only [mul_assoc, hAR]
  have hr : R * (A * B) * R = S * B * R := by simp only [← mul_assoc, hRA]
  rw [hl, hr] at he
  change (S * B * R).transpose = S * B * R
  simpa only [Matrix.transpose_mul, hR.eq, hS.eq, Matrix.mul_assoc] using he

theorem whitenedJacobian_isSymm (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hc : (A * B).IsSymm) : (whitenedJacobian A B).IsSymm := by
  let R := inverseSqrtMatrix A
  let S := R⁻¹
  have hR : R.IsSymm := inverseSqrtMatrix_isSymm A
  have hS : S.IsSymm := hR.inv
  have hSS : S * S = A := by
    have hg : S.transpose * S = A := inverseSqrtMatrix_inverse_gram hA
    simpa only [hS.eq] using hg
  have hdet : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
  exact conjugate_symm_of_inverse_pair A B R S hA.isHermitian.isSymm hc hR hS hSS
    (Matrix.mul_nonsing_inv R hdet) (Matrix.nonsing_inv_mul R hdet)

theorem whitenedJacobian_reconstruct (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    inverseSqrtMatrix A * whitenedJacobian A B * (inverseSqrtMatrix A)⁻¹ = B := by
  let R := inverseSqrtMatrix A
  let S := R⁻¹
  have hdet : IsUnit R.det := isUnit_iff_ne_zero.mpr (inverseSqrtMatrix_det_ne_zero_of_posDef hA)
  have hRS : R * S = 1 := Matrix.mul_nonsing_inv R hdet
  change R * (S * B * R) * S = B
  calc
    _ = (R * S) * B * (R * S) := by simp only [mul_assoc]
    _ = B := by rw [hRS, one_mul, mul_one]

end KLSConstantImprovement.ActualWhitenedJacobianSymmetry405
#print axioms KLSConstantImprovement.ActualWhitenedJacobianSymmetry405.whitenedJacobian_isSymm
#print axioms KLSConstantImprovement.ActualWhitenedJacobianSymmetry405.whitenedJacobian_reconstruct
