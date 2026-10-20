import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The real-to-complex matrix embedding preserves and reflects the
actual positive-semidefinite order. Positive preservation uses an actual
square-root Gram factorization. Reflection restricts complex quadratic
forms to real vectors. No matrix-order certificate is assumed. -/
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace KLSConstantImprovement.ActualRealComplexMatrixOrder405
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexMatrix : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix

theorem complexMatrix_star (M : Matrix ι ι ℝ) :
    complexMatrix M.conjTranspose = (complexMatrix M).conjTranspose := by
  ext i j
  simp [complexMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply]

theorem complexMatrix_posSemidef {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    (complexMatrix M).PosSemidef := by
  let R := CFC.sqrt M
  have hR : R.conjTranspose = R := (CFC.sqrt_nonneg M).posSemidef.isHermitian.eq
  have hfactor : R.conjTranspose * R = M := by
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self M hM.nonneg
  have he : (complexMatrix R).conjTranspose * complexMatrix R = complexMatrix M := by
    rw [← complexMatrix_star, ← map_mul, hfactor]
  exact he ▸ Matrix.posSemidef_conjTranspose_mul_self (complexMatrix R)

theorem posSemidef_of_complexMatrix {M : Matrix ι ι ℝ}
    (hM : (complexMatrix M).PosSemidef) : M.PosSemidef := by
  have hselfc : (M.map Complex.ofReal).IsHermitian := hM.isHermitian
  have hself : M.IsHermitian := (Matrix.isHermitian_map_iff
    (f := Complex.ofReal) (by intro x; simp) Complex.ofReal_injective).mp hselfc
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hself
  intro v
  have hc := hM.dotProduct_mulVec_nonneg (fun i => (v i : ℂ))
  have hr : 0 ≤ (star (fun i => (v i : ℂ)) ⬝ᵥ
      ((complexMatrix M) *ᵥ fun i => (v i : ℂ))).re := (RCLike.nonneg_iff.mp hc).1
  simpa [complexMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mulVec,
    dotProduct, Pi.star_apply, Complex.mul_re] using hr

theorem complexMatrix_posSemidef_iff (M : Matrix ι ι ℝ) :
    (complexMatrix M).PosSemidef ↔ M.PosSemidef :=
  ⟨posSemidef_of_complexMatrix, complexMatrix_posSemidef⟩

theorem complexMatrix_le_iff (M N : Matrix ι ι ℝ) :
    complexMatrix M ≤ complexMatrix N ↔ M ≤ N := by
  rw [Matrix.le_iff, Matrix.le_iff, ← map_sub]
  exact complexMatrix_posSemidef_iff (N - M)

end KLSConstantImprovement.ActualRealComplexMatrixOrder405

#print axioms KLSConstantImprovement.ActualRealComplexMatrixOrder405.complexMatrix_posSemidef
#print axioms KLSConstantImprovement.ActualRealComplexMatrixOrder405.posSemidef_of_complexMatrix
#print axioms KLSConstantImprovement.ActualRealComplexMatrixOrder405.complexMatrix_le_iff
