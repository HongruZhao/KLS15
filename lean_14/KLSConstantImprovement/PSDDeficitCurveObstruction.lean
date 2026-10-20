import Mathlib

/-! A finite polynomial PSD-curve obstruction. This is an algebraic curve on
symmetric two-by-two matrix entries, not a probability law or cumulant jet.
Its scalar positivity, local cap, and gradient control coexist with d=0 and
contracted curvature J=-2. The fourth-form permutation mismatch explicitly
records why it cannot replace the actual cumulant deficit in the KLS route. -/
noncomputable section
namespace KLSConstantImprovement.PSDDeficitCurveObstruction
open scoped BigOperators
abbrev Two := Fin 2→ℝ
abbrev Three := Fin 3→ℝ
set_option maxHeartbeats 3000000

def ell (t : Two) (B : Three) : ℝ := t 1*B 0-t 0*B 1
def curve (t : Two) (B C : Three) : ℝ := ell t B*ell t C+12*B 2*C 2
def hsSquare (B : Three) : ℝ := (B 0)^2+(B 1)^2+2*(B 2)^2
def vectorSquare (t : Two) : ℝ := (t 0)^2+(t 1)^2
def e11 : Three := ![1,0,0]
def e22 : Three := ![0,1,0]
def offDiagonal : Three := ![0,0,1]
def testTensor (i j k : Fin 2) : ℝ := if i=j ∧ j=k then 1 else 0

def linearPolynomial (B : Three) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (B 0)*MvPolynomial.X 1-MvPolynomial.C (B 1)*MvPolynomial.X 0
def curvePolynomial (B C : Three) : MvPolynomial (Fin 2) ℝ :=
  linearPolynomial B*linearPolynomial C+MvPolynomial.C (12*B 2*C 2)
def diagonalDeficit : ℝ := curve 0 e11 e11+curve 0 e22 e22
def contractedCurvature : ℝ :=
  MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (curvePolynomial e11 e11)))+
  MvPolynomial.eval 0 (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (curvePolynomial e11 e22)))+
  MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 (curvePolynomial e22 e11)))+
  MvPolynomial.eval 0 (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (curvePolynomial e22 e22)))
def fourthForm (t : Two) (B C : Three) : ℝ :=
  6*(B 0*C 0+B 1*C 1+2*B 2*C 2)-curve t B C

theorem curvePolynomial_eval (t : Two) (B C : Three) :
    MvPolynomial.eval t (curvePolynomial B C)=curve t B C := by
  simp [curvePolynomial,linearPolynomial,curve,ell]
  ring

theorem curve_nonnegative (t : Two) (B : Three) : 0≤curve t B B := by
  unfold curve
  nlinarith [sq_nonneg (ell t B),sq_nonneg (B 2)]

theorem hsSquare_nonnegative (B : Three) : 0≤hsSquare B := by
  unfold hsSquare
  positivity

theorem ell_square_le (t : Two) (B : Three) :
    (ell t B)^2≤((B 0)^2+(B 1)^2)*vectorSquare t := by
  have h : ((B 0)^2+(B 1)^2)*vectorSquare t-(ell t B)^2=
      (B 0*t 0+B 1*t 1)^2 := by
    unfold vectorSquare ell
    ring
  nlinarith [sq_nonneg (B 0*t 0+B 1*t 1)]

theorem local_eight_cap (t : Two) (B : Three) (ht : vectorSquare t≤8) :
    curve t B B≤8*hsSquare B := by
  have he := ell_square_le t B
  have hm := mul_le_mul_of_nonneg_left ht (show 0≤(B 0)^2+(B 1)^2 by positivity)
  unfold curve hsSquare
  nlinarith [sq_nonneg (B 2)]

theorem linearPolynomial_pderiv_zero (B : Three) :
    MvPolynomial.pderiv 0 (linearPolynomial B)=MvPolynomial.C (-B 1) := by
  simp [linearPolynomial,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem linearPolynomial_pderiv_one (B : Three) :
    MvPolynomial.pderiv 1 (linearPolynomial B)=MvPolynomial.C (B 0) := by
  simp [linearPolynomial,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem diagonal_gradient_zero (t : Two) (B : Three) :
    MvPolynomial.eval t (MvPolynomial.pderiv 0 (curvePolynomial B B))=
      -2*B 1*ell t B := by
  unfold curvePolynomial
  rw [map_add,MvPolynomial.pderiv_mul,linearPolynomial_pderiv_zero,MvPolynomial.pderiv_C]
  simp [linearPolynomial,ell]
  ring

theorem diagonal_gradient_one (t : Two) (B : Three) :
    MvPolynomial.eval t (MvPolynomial.pderiv 1 (curvePolynomial B B))=
      2*B 0*ell t B := by
  unfold curvePolynomial
  rw [map_add,MvPolynomial.pderiv_mul,linearPolynomial_pderiv_one,MvPolynomial.pderiv_C]
  simp [linearPolynomial,ell]
  ring

theorem diagonal_gradient_square_identity (t : Two) (B : Three) :
    (MvPolynomial.eval t (MvPolynomial.pderiv 0 (curvePolynomial B B)))^2+
      (MvPolynomial.eval t (MvPolynomial.pderiv 1 (curvePolynomial B B)))^2=
      4*(ell t B)^2*((B 0)^2+(B 1)^2) := by
  rw [diagonal_gradient_zero,diagonal_gradient_one]
  ring

theorem diagonal_gradient_control (t : Two) (B : Three) :
    (MvPolynomial.eval t (MvPolynomial.pderiv 0 (curvePolynomial B B)))^2+
      (MvPolynomial.eval t (MvPolynomial.pderiv 1 (curvePolynomial B B)))^2≤
      4*hsSquare B*curve t B B := by
  rw [diagonal_gradient_square_identity]
  have h : 0≤4*(2*(B 2)^2*(ell t B)^2+12*hsSquare B*(B 2)^2) := by
    have hh := hsSquare_nonnegative B
    positivity
  have he : 4*hsSquare B*curve t B B-4*(ell t B)^2*((B 0)^2+(B 1)^2)=
      4*(2*(B 2)^2*(ell t B)^2+12*hsSquare B*(B 2)^2) := by
    unfold curve hsSquare
    ring
  linarith

theorem testTensor_symmetric :
    (∀ i j k,testTensor i j k=testTensor j i k) ∧
    (∀ i j k,testTensor i j k=testTensor i k j) := by
  constructor <;> intro i j k <;> fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [testTensor]

theorem testTensor_square_two : (∑ i,∑ j,∑ k,(testTensor i j k)^2)=2 := by
  simp only [Fin.sum_univ_two]
  norm_num [testTensor]

theorem diagonalDeficit_zero : diagonalDeficit=0 := by
  norm_num [diagonalDeficit,curve,ell,e11,e22]

theorem contractedCurvature_neg_two : contractedCurvature=-2 := by
  norm_num [contractedCurvature,curvePolynomial,linearPolynomial,e11,e22,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem finite_curvature_gate_fails (k : ℝ) : ¬ -k*diagonalDeficit≤contractedCurvature := by
  rw [diagonalDeficit_zero,contractedCurvature_neg_two]
  norm_num

theorem fourthForm_at_origin (B C : Three) :
    fourthForm 0 B C=6*B 0*C 0+6*B 1*C 1 := by
  simp [fourthForm,curve,ell]
  ring

theorem fourth_permutation_symmetry_fails :
    fourthForm (![1,1] : Two) offDiagonal offDiagonal≠
      4*fourthForm (![1,1] : Two) e11 e22 := by
  norm_num [fourthForm,curve,ell,offDiagonal,e11,e22]

end KLSConstantImprovement.PSDDeficitCurveObstruction
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.curvePolynomial_eval
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.curve_nonnegative
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.local_eight_cap
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.diagonal_gradient_square_identity
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.diagonal_gradient_control
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.testTensor_symmetric
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.testTensor_square_two
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.diagonalDeficit_zero
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.contractedCurvature_neg_two
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.finite_curvature_gate_fails
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.fourthForm_at_origin
#print axioms KLSConstantImprovement.PSDDeficitCurveObstruction.fourth_permutation_symmetry_fails
