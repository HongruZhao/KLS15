import ProductCubicKernels
import ExponentialCriticalGram

/-! Exact two-head Bessel budget for the scalar rate-one exponential.
The cubic is orthogonalized against the quadratic before estimating it. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ScalarJoint
open KLSImprovement.Exponential KLSImprovement.ProductCubic
open KLSImprovement.ExponentialCriticalGram
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def cubicResidual (y : ℝ) : ℝ := appell 2 y-(9/2:ℝ)*appell 1 y

theorem cubicResidual_memLp : MemLp cubicResidual 2 (expMeasure 1) := by
  exact (scalarAppell_memLp 3).sub ((scalarAppell_memLp 2).const_mul (9/2:ℝ))

theorem integral_cubicResidual_appell (m : ℕ) :
    (∫ y,cubicResidual y*appell m y ∂expMeasure 1)=
      (∫ y,appell 2 y*appell m y ∂expMeasure 1)-
        (9/2:ℝ)*(∫ y,appell 1 y*appell m y ∂expMeasure 1) := by
  have hm : MemLp (appell m) 2 (expMeasure 1) := by
    simpa only [scalarAppell_succ] using scalarAppell_memLp (m+1)
  have h2 : MemLp (appell 2) 2 (expMeasure 1) := scalarAppell_memLp 3
  have h1 : MemLp (appell 1) 2 (expMeasure 1) := scalarAppell_memLp 2
  have he : (fun y=>cubicResidual y*appell m y)=
      (fun y=>appell 2 y*appell m y-(9/2:ℝ)*(appell 1 y*appell m y)) := by
    funext y
    unfold cubicResidual
    ring
  rw [he,integral_sub (f:=fun y=>appell 2 y*appell m y)
    (g:=fun y=>(9/2:ℝ)*(appell 1 y*appell m y))
    (h2.integrable_mul hm) ((h1.integrable_mul hm).const_mul _),
    integral_const_mul]

theorem integral_cubicResidual_quadratic :
    (∫ y,cubicResidual y*appell 1 y ∂expMeasure 1)=0 := by
  rw [integral_cubicResidual_appell,integral_appell_mul,integral_appell_mul]
  norm_num

theorem integral_cubicResidual_cubic :
    (∫ y,cubicResidual y*appell 2 y ∂expMeasure 1)=54 := by
  rw [integral_cubicResidual_appell,integral_appell_mul,integral_appell_mul]
  norm_num

theorem integral_cubicResidual_sq :
    (∫ y,(cubicResidual y)^2 ∂expMeasure 1)=54 := by
  have h2 : MemLp (appell 2) 2 (expMeasure 1) := scalarAppell_memLp 3
  have h1 : MemLp (appell 1) 2 (expMeasure 1) := scalarAppell_memLp 2
  have he : (fun y=>(cubicResidual y)^2)=
      (fun y=>cubicResidual y*appell 2 y-(9/2:ℝ)*(cubicResidual y*appell 1 y)) := by
    funext y
    unfold cubicResidual
    ring
  rw [he,integral_sub (f:=fun y=>cubicResidual y*appell 2 y)
    (g:=fun y=>(9/2:ℝ)*(cubicResidual y*appell 1 y))
    (cubicResidual_memLp.integrable_mul h2)
    ((cubicResidual_memLp.integrable_mul h1).const_mul _),integral_const_mul,
    integral_cubicResidual_cubic,integral_cubicResidual_quadratic]
  norm_num

theorem integral_div_pair {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω→ℝ) (a b : ℝ) :
    (∫ x,(p x/a)*(q x/b) ∂μ)=(∫ x,p x*q x ∂μ)/(a*b) := by
  simp_rw [div_mul_div_comm]
  rw [integral_div]

/-- Two orthogonal functions with squared norms eight and 54 give a joint
observation budget, with no hypothesis on the mean of the test function. -/
theorem orthogonal_two_head_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω→ℝ) (hp : MemLp p 2 μ) (hq : MemLp q 2 μ)
    (hpp : (∫ x,p x*p x ∂μ)=8) (hqq : (∫ x,q x*q x ∂μ)=54)
    (hpq : (∫ x,p x*q x ∂μ)=0) {f : Ω→ℝ} (hf : MemLp f 2 μ) :
    (∫ x,f x*p x ∂μ)^2/8+(∫ x,f x*q x ∂μ)^2/54≤∫ x,(f x)^2 ∂μ := by
  let head : Fin 2→Ω→ℝ := ![fun x=>p x/Real.sqrt 8,fun x=>q x/Real.sqrt 54]
  have hqp : (∫ x,q x*p x ∂μ)=0 := by
    convert hpq using 1
    congr 1
    funext x
    ring
  have hs8 : Real.sqrt 8*Real.sqrt 8=(8:ℝ) := Real.mul_self_sqrt (by norm_num)
  have hs54 : Real.sqrt 54*Real.sqrt 54=(54:ℝ) := Real.mul_self_sqrt (by norm_num)
  have hhead : ∀ i,MemLp (head i) 2 μ := by
    intro i
    fin_cases i
    · change MemLp (fun x=>p x/Real.sqrt 8) 2 μ
      simpa only [div_eq_mul_inv] using hp.mul_const (Real.sqrt 8)⁻¹
    · change MemLp (fun x=>q x/Real.sqrt 54) 2 μ
      simpa only [div_eq_mul_inv] using hq.mul_const (Real.sqrt 54)⁻¹
  have hgram : ∀ i j : Fin 2,(∫ x,head i x*head j x ∂μ)=if i=j then 1 else 0 := by
    intro i j
    fin_cases i <;>fin_cases j <;>
      simp [head,integral_div_pair,hpp,hqq,hpq,hqp,hs8,hs54]
  have hrow : ∀ i,∑ j,|∫ x,head i x*head j x ∂μ|≤(1:ℝ) := by
    intro i
    simp_rw [hgram]
    fin_cases i <;>norm_num
  have h := KLSImprovement.FiniteIntegralGram.observation_le_of_integral_gram_rows
    μ head hhead (by norm_num : (0:ℝ)<1) hrow hf
  have he (p : Ω→ℝ) (a : ℝ) :
      (∫ x,f x*(p x/a) ∂μ)=(∫ x,f x*p x ∂μ)/a := by
    simp_rw [←mul_div_assoc]
    rw [integral_div]
  simpa only [Fin.sum_univ_two,head,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,he,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤8),
    Real.sq_sqrt (by norm_num : (0:ℝ)≤54),one_mul] using h

theorem scalar_quadratic_residual_budget {f : ℝ→ℝ}
    (hf : MemLp f 2 (expMeasure 1)) :
    (∫ y,f y*appell 1 y ∂expMeasure 1)^2/8+
      (∫ y,f y*cubicResidual y ∂expMeasure 1)^2/54≤
        ∫ y,(f y)^2 ∂expMeasure 1 := by
  apply orthogonal_two_head_budget (expMeasure 1) (appell 1) cubicResidual
    (scalarAppell_memLp 2) cubicResidual_memLp _ _ _ hf
  · simpa only [pow_two] using (show (∫ y,(appell 1 y)^2 ∂expMeasure 1)=8 by
      rw [integral_appell_sq];norm_num)
  · simpa only [pow_two] using integral_cubicResidual_sq
  · convert integral_cubicResidual_quadratic using 1
    congr 1
    funext y
    ring

theorem scalar_quadratic_cubic_joint_budget {f : ℝ→ℝ}
    (hf : MemLp f 2 (expMeasure 1)) :
    (∫ y,f y*appell 1 y ∂expMeasure 1)^2/8+
      ((∫ y,f y*appell 2 y ∂expMeasure 1)-
        (9/2:ℝ)*(∫ y,f y*appell 1 y ∂expMeasure 1))^2/54≤
          ∫ y,(f y)^2 ∂expMeasure 1 := by
  have he : (∫ y,f y*cubicResidual y ∂expMeasure 1)=
      (∫ y,f y*appell 2 y ∂expMeasure 1)-
        (9/2:ℝ)*(∫ y,f y*appell 1 y ∂expMeasure 1) := by
    have he : (fun y=>f y*cubicResidual y)=
        (fun y=>f y*appell 2 y-(9/2:ℝ)*(f y*appell 1 y)) := by
      funext y
      unfold cubicResidual
      ring
    rw [he,integral_sub (f:=fun y=>f y*appell 2 y)
      (g:=fun y=>(9/2:ℝ)*(f y*appell 1 y))
      (hf.integrable_mul (scalarAppell_memLp 3))
      ((hf.integrable_mul (scalarAppell_memLp 2)).const_mul _),integral_const_mul]
  simpa only [he] using scalar_quadratic_residual_budget hf

end KLSImprovement.ScalarJoint
#print axioms KLSImprovement.ScalarJoint.integral_cubicResidual_sq
#print axioms KLSImprovement.ScalarJoint.orthogonal_two_head_budget
#print axioms KLSImprovement.ScalarJoint.scalar_quadratic_cubic_joint_budget
