import KLSConstantImprovement.DeficitCurvatureScalar

/-! Exact two-dimensional gamma-radial block coefficient positivity.
This module proves the literal displayed polynomial forms for every h>=0.
No density, centering, or whitening identification is silently assumed;
the actual-law block formula is an explicit input to the final corollary.
-/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.GammaRadialCurvatureCoefficients
set_option maxHeartbeats 3000000

def quadratic (A B C x y : ℝ) : ℝ := A*x^2+2*B*x*y+C*y^2

theorem quadratic_nonnegative {A B C : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdet : 0 ≤ A*C-B^2) (x y : ℝ) :
    0 ≤ quadratic A B C x y := by
  by_cases hz:A=0
  · have hB:B=0 := by rw [hz] at hdet;nlinarith [sq_nonneg B]
    simp only [quadratic,hz,hB,zero_mul,mul_zero,zero_add]
    exact mul_nonneg hC (sq_nonneg y)
  · have hp:0 < A := lt_of_le_of_ne hA (Ne.symm hz)
    have he:A*quadratic A B C x y=(A*x+B*y)^2+(A*C-B^2)*y^2 := by
      unfold quadratic;ring
    have hn:0 ≤ A*quadratic A B C x y := by
      rw [he]
      exact add_nonneg (sq_nonneg _) (mul_nonneg hdet (sq_nonneg y))
    exact (mul_nonneg_iff_of_pos_left hp).mp hn

theorem quadratic_positive {A B C : ℝ} (hA : 0 < A) (hdet : 0 < A*C-B^2)
    {x y : ℝ} (hne : x≠0 ∨ y≠0) : 0 < quadratic A B C x y := by
  by_cases hy:y=0
  · have hx:x≠0 := hne.resolve_right (not_not.mpr hy)
    simp only [quadratic,hy,mul_zero,zero_pow (by omega : 2≠0),add_zero]
    exact mul_pos hA (sq_pos_of_ne_zero hx)
  · have he:A*quadratic A B C x y=(A*x+B*y)^2+(A*C-B^2)*y^2 := by
      unfold quadratic;ring
    have hp:0 < A*quadratic A B C x y := by
      rw [he]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero hy))
    exact (mul_pos_iff_of_pos_left hA).mp hp
def eA (i : Fin 7) : ℝ := ![312,504,210,18,0,0,0] i
def eB (i : Fin 7) : ℝ := ![-312,-56,118,34,0,0,0] i
def eC (i : Fin 7) : ℝ := ![312,11672/5,37102/15,14278/15,2092/15,24/5,0] i
def oA (i : Fin 7) : ℝ := ![120,1456,1258,316,18,0,0] i
def oB (i : Fin 7) : ℝ := ![-120,352,1514/3,596/3,74/3,0,0] i
def oC (i : Fin 7) : ℝ := ![120,17904/35,19966/35,85172/315,6166/105,512/105,4/315] i

theorem even_coefficient_psd (i : Fin 7) :
    0 ≤ eA i ∧ 0 ≤ eC i ∧ 0 ≤ eA i*eC i-(eB i)^2 := by
  fin_cases i <;> norm_num [eA,eB,eC]
theorem odd_coefficient_psd (i : Fin 7) :
    0 ≤ oA i ∧ 0 ≤ oC i ∧ 0 ≤ oA i*oC i-(oB i)^2 := by
  fin_cases i <;> norm_num [oA,oB,oC]
theorem first_coefficients_positive_definite :
    0 < eA 1 ∧ 0 < eA 1*eC 1-(eB 1)^2 ∧
    0 < oA 1 ∧ 0 < oA 1*oC 1-(oB 1)^2 := by
  norm_num [eA,eB,eC,oA,oB,oC]

def evenForm (h a c : ℝ) : ℝ := ∑ i : Fin 7,h^(i:ℕ)*quadratic (eA i) (eB i) (eC i) a c
def oddForm (h b d : ℝ) : ℝ := ∑ i : Fin 7,h^(i:ℕ)*quadratic (oA i) (oB i) (oC i) b d
def fullCubicForm (h a b c d : ℝ) : ℝ := evenForm h a c+oddForm h b d

theorem evenForm_nonnegative {h : ℝ} (hh : 0 ≤ h) (a c : ℝ) : 0 ≤ evenForm h a c := by
  exact Finset.sum_nonneg fun i _=>mul_nonneg (pow_nonneg hh _) (quadratic_nonnegative
    (even_coefficient_psd i).1 (even_coefficient_psd i).2.1 (even_coefficient_psd i).2.2 a c)
theorem oddForm_nonnegative {h : ℝ} (hh : 0 ≤ h) (b d : ℝ) : 0 ≤ oddForm h b d := by
  exact Finset.sum_nonneg fun i _=>mul_nonneg (pow_nonneg hh _) (quadratic_nonnegative
    (odd_coefficient_psd i).1 (odd_coefficient_psd i).2.1 (odd_coefficient_psd i).2.2 b d)
theorem fullCubicForm_nonnegative {h : ℝ} (hh : 0 ≤ h) (a b c d : ℝ) :
    0 ≤ fullCubicForm h a b c d :=
  add_nonneg (evenForm_nonnegative hh a c) (oddForm_nonnegative hh b d)

theorem exponential_equality_form (a b c d : ℝ) :
    fullCubicForm 0 a b c d=312*(a-c)^2+120*(b-d)^2 := by
  norm_num [fullCubicForm,evenForm,oddForm,Fin.sum_univ_succ,eA,eB,eC,oA,oB,oC,quadratic]
  ring
theorem exponential_null_space (a b c d : ℝ) : fullCubicForm 0 a b c d=0 ↔ a=c ∧ b=d := by
  rw [exponential_equality_form]
  constructor
  · intro he
    have h₁:(a-c)^2=0 := by nlinarith [sq_nonneg (b-d),sq_nonneg (a-c)]
    have h₂:(b-d)^2=0 := by nlinarith [sq_nonneg (b-d),sq_nonneg (a-c)]
    exact ⟨sub_eq_zero.mp ((sq_eq_zero_iff).mp h₁),sub_eq_zero.mp ((sq_eq_zero_iff).mp h₂)⟩
  · rintro ⟨rfl,rfl⟩
    ring

theorem curvature_three_of_actual_block_identity {β J D a b c d : ℝ} (hβ : 2 ≤ β)
    (hactual : J+3*D=fullCubicForm (β-2) a b c d) : -3*D ≤ J := by
  have hp:=fullCubicForm_nonnegative (show 0 ≤ β-2 by linarith) a b c d
  rw [←hactual] at hp
  linarith

theorem curvature_65over2_of_actual_block_identity {β J D a b c d : ℝ} (hβ : 2 ≤ β)
    (hD : 0 ≤ D) (hactual : J+3*D=fullCubicForm (β-2) a b c d) :
    -(65/2 : ℝ)*D ≤ J :=
  DeficitCurvatureScalar.curvature_monotone hD (by norm_num)
    (curvature_three_of_actual_block_identity hβ hactual)

end KLSConstantImprovement.GammaRadialCurvatureCoefficients
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.quadratic_nonnegative
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.quadratic_positive
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.even_coefficient_psd
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.odd_coefficient_psd
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.first_coefficients_positive_definite
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.fullCubicForm_nonnegative
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.exponential_null_space
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.curvature_three_of_actual_block_identity
#print axioms KLSConstantImprovement.GammaRadialCurvatureCoefficients.curvature_65over2_of_actual_block_identity
