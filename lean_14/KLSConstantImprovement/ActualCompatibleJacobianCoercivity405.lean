import KLS.MatrixInverseCoercivity
import KLS.SteinMatrixContraction

/-! Finite coercivity of a genuine metric-compatible Jacobian.
For fixed regularization this pays Euclidean derivative cutoff errors;
the scalar ellipticity constants may depend on that regularization.
No Poisson regularity, global integration, or strong core is asserted here. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace KLSConstantImprovement.ActualCompatibleJacobianCoercivity405
open KLS
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem weighted_jacobian_trace_lower
    (A J B : Matrix (Fin n) (Fin n) ℝ) {α c : ℝ} (hα : 0 ≤ α)
    (hJ : J.PosSemidef)
    (hA : (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hJl : (J - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    α * c * matrixFrobeniusSq B ≤ (A * B * J * B.transpose).trace := by
  have hBJB : (B * J * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hJ.mul_mul_conjTranspose_same B
  have hfirst := trace_mul_nonneg_of_posSemidef hA hBJB
  have he : ((A - α • (1 : Matrix (Fin n) (Fin n) ℝ)) *
      (B * J * B.transpose)).trace =
      (A * B * J * B.transpose).trace - α * (B * J * B.transpose).trace := by
    simp only [sub_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, mul_assoc]
  rw [he] at hfirst
  have hsecond := (hJl.mul_mul_conjTranspose_same B).trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_one, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul] at hsecond
  rw [← matrixFrobeniusSq_eq_trace_mul_transpose] at hsecond
  nlinarith [mul_nonneg hα hsecond]

theorem compatible_jacobian_trace_identity
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hAB : (A * B).IsSymm) :
    (B * B).trace = (A * B * A⁻¹ * B.transpose).trace := by
  have hrel : B.transpose * A = A * B := by
    simpa only [Matrix.transpose_mul, hA.isHermitian.isSymm.eq] using hAB.eq
  have hAJ : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)
  have hBt : B.transpose = A * B * A⁻¹ := by
    calc
      B.transpose = B.transpose * (A * A⁻¹) := by rw [hAJ, mul_one]
      _ = (B.transpose * A) * A⁻¹ := (mul_assoc _ _ _).symm
      _ = _ := by rw [hrel]
  rw [← hBt, ← Matrix.transpose_mul, Matrix.trace_transpose]

theorem compatible_jacobian_trace_coercive
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hAB : (A * B).IsSymm)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hl : (A - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hu : (β • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef) :
    (α / β) * matrixFrobeniusSq B ≤ (B * B).trace := by
  rw [compatible_jacobian_trace_identity A B hA hAB]
  simpa only [div_eq_mul_inv, mul_assoc] using
    weighted_jacobian_trace_lower A A⁻¹ B hα hA.inv.posSemidef hl
      (inverse_lower_of_posDef_upper hA hβ hu)

theorem compatible_jacobian_trace_nonneg
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hAB : (A * B).IsSymm) :
    0 ≤ (B * B).trace := by
  rw [compatible_jacobian_trace_identity A B hA hAB]
  have hBJB : (B * A⁻¹ * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.inv.posSemidef.mul_mul_conjTranspose_same B
  simpa only [mul_assoc] using trace_mul_nonneg_of_posSemidef hA.posSemidef hBJB

end KLSConstantImprovement.ActualCompatibleJacobianCoercivity405
#print axioms KLSConstantImprovement.ActualCompatibleJacobianCoercivity405.weighted_jacobian_trace_lower
#print axioms KLSConstantImprovement.ActualCompatibleJacobianCoercivity405.compatible_jacobian_trace_identity
#print axioms KLSConstantImprovement.ActualCompatibleJacobianCoercivity405.compatible_jacobian_trace_coercive
#print axioms KLSConstantImprovement.ActualCompatibleJacobianCoercivity405.compatible_jacobian_trace_nonneg
