import KLSConstantImprovement.PSDDeficitCurveObstruction

/-! Polynomial-Hessian and literal slice indexing for the finite generic
PSD-curve obstruction. These are algebraic properties of that artificial
curve; its proved fourth-form permutation mismatch remains in force. -/
noncomputable section
namespace KLSConstantImprovement.PSDDeficitCurveHessianControl
open PSDDeficitCurveObstruction
open scoped BigOperators
set_option maxHeartbeats 3000000

def directionalHessian (t v : Two) (B : Three) : ℝ :=
  (v 0)^2*MvPolynomial.eval t
    (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (curvePolynomial B B)))+
  v 0*v 1*MvPolynomial.eval t
    (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (curvePolynomial B B)))+
  v 1*v 0*MvPolynomial.eval t
    (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (curvePolynomial B B)))+
  (v 1)^2*MvPolynomial.eval t
    (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (curvePolynomial B B)))

theorem directionalHessian_identity (t v : Two) (B : Three) :
    directionalHessian t v B=2*(ell v B)^2 := by
  simp [directionalHessian,curvePolynomial,linearPolynomial,ell,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,
    Pi.single_apply] <;> ring

theorem directionalHessian_nonnegative (t v : Two) (B : Three) :
    0≤directionalHessian t v B := by
  rw [directionalHessian_identity]
  positivity

theorem directionalHessian_upper_two (t v : Two) (B : Three) :
    directionalHessian t v B≤2*hsSquare B*vectorSquare v := by
  rw [directionalHessian_identity]
  have he := ell_square_le v B
  have hs : (B 0)^2+(B 1)^2≤hsSquare B := by
    unfold hsSquare
    nlinarith [sq_nonneg (B 2)]
  have hv : 0≤vectorSquare v := by
    unfold vectorSquare
    positivity
  have hm := mul_le_mul_of_nonneg_right hs hv
  nlinarith [he.trans hm]

def sliceMatrix (B : Three) : Fin 2→Fin 2→ℝ := ![![B 0,B 2],![B 2,B 1]]
def sliceVector (i : Fin 2) : Three := ![e11,e22] i

theorem testTensor_slice_zero : (fun j k => testTensor 0 j k)=sliceMatrix e11 := by
  funext j k
  fin_cases j <;> fin_cases k <;> norm_num [testTensor,sliceMatrix,e11]

theorem testTensor_slice_one : (fun j k => testTensor 1 j k)=sliceMatrix e22 := by
  funext j k
  fin_cases j <;> fin_cases k <;> norm_num [testTensor,sliceMatrix,e22]

theorem contractedCurvature_is_slice_sum :
    (∑ i : Fin 2,∑ j : Fin 2,MvPolynomial.eval (0 : Two)
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (curvePolynomial (sliceVector i) (sliceVector j)))))=contractedCurvature := by
  simp only [Fin.sum_univ_two]
  simp [sliceVector,contractedCurvature,add_assoc]

end KLSConstantImprovement.PSDDeficitCurveHessianControl
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.directionalHessian_identity
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.directionalHessian_nonnegative
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.directionalHessian_upper_two
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.testTensor_slice_zero
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.testTensor_slice_one
#print axioms KLSConstantImprovement.PSDDeficitCurveHessianControl.contractedCurvature_is_slice_sum
