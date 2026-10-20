import ProductQuadraticJointKernels

/-! A full product Bessel budget retaining quadratic energy and residual
cubic energy simultaneously, with no dimension factor. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic KLSImprovement.ProductPolynomial
open KLSImprovement.ScalarJoint
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)

def jointHead {n : ℕ} : ((Fin 2→Fin n)⊕(Fin 3→Fin n))→(Fin n→ℝ)→ℝ
  | Sum.inl I => fun y=>pairBasis I y/Real.sqrt 8
  | Sum.inr I => fun y=>residualBasis I y/Real.sqrt 54

theorem jointHead_memLp {n : ℕ} (I : (Fin 2→Fin n)⊕(Fin 3→Fin n)) :
    MemLp (jointHead I) 2 (product n) := by
  cases I with
  | inl I =>
    change MemLp (fun y=>pairBasis I y/Real.sqrt 8) 2 (product n)
    simpa only [div_eq_mul_inv] using (pairBasis_memLp I).mul_const (Real.sqrt 8)⁻¹
  | inr I =>
    change MemLp (fun y=>residualBasis I y/Real.sqrt 54) 2 (product n)
    simpa only [div_eq_mul_inv] using (residualBasis_memLp I).mul_const (Real.sqrt 54)⁻¹

theorem jointHead_gram_ll {n : ℕ} (I J : Fin 2→Fin n) :
    (∫ y,jointHead (Sum.inl I) y*jointHead (Sum.inl J) y ∂product n)=pairGram I J/8 := by
  rw [jointHead,jointHead,integral_div_pair,pairGram_integral,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤8)]

theorem jointHead_gram_lr {n : ℕ} (I : Fin 2→Fin n) (J : Fin 3→Fin n) :
    (∫ y,jointHead (Sum.inl I) y*jointHead (Sum.inr J) y ∂product n)=0 := by
  rw [jointHead,jointHead,integral_div_pair,crossGram_integral,crossGram_zero,zero_div]

theorem jointHead_gram_rl {n : ℕ} (I : Fin 3→Fin n) (J : Fin 2→Fin n) :
    (∫ y,jointHead (Sum.inr I) y*jointHead (Sum.inl J) y ∂product n)=0 := by
  convert jointHead_gram_lr J I using 1
  congr 1
  funext y
  ring

theorem jointHead_gram_rr {n : ℕ} (I J : Fin 3→Fin n) :
    (∫ y,jointHead (Sum.inr I) y*jointHead (Sum.inr J) y ∂product n)=residualGram I J/54 := by
  rw [jointHead,jointHead,integral_div_pair,residualGram_integral,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤54)]

theorem jointHead_abs_gram_row_le {n : ℕ} (I : (Fin 2→Fin n)⊕(Fin 3→Fin n)) :
    (∑ J,|∫ y,jointHead I y*jointHead J y ∂product n|)≤1 := by
  cases I with
  | inl I =>
    rw [Fintype.sum_sum_type]
    simp only [jointHead_gram_ll,jointHead_gram_lr,abs_zero,Finset.sum_const_zero,add_zero]
    simp_rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤8)]
    rw [←Finset.sum_div]
    exact (div_le_one (by norm_num : (0:ℝ)<8)).mpr (pairGram_abs_row_le I)
  | inr I =>
    rw [Fintype.sum_sum_type]
    simp only [jointHead_gram_rr,jointHead_gram_rl,abs_zero,Finset.sum_const_zero,zero_add]
    simp_rw [abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤54)]
    rw [←Finset.sum_div]
    exact (div_le_one (by norm_num : (0:ℝ)<54)).mpr (residualGram_abs_row_le I)

def quadraticEnergy {n : ℕ} (f : (Fin n→ℝ)→ℝ) : ℝ :=
  ∑ I,(∫ y,f y*pairBasis I y ∂product n)^2
def residualEnergy {n : ℕ} (f : (Fin n→ℝ)→ℝ) : ℝ :=
  ∑ I,(∫ y,f y*residualBasis I y ∂product n)^2

/-- Full ordered-index quadratic and residual cubic budget on the actual
independent exponential product, in every finite dimension. -/
theorem full_product_quadratic_residual_budget {n : ℕ} {f : (Fin n→ℝ)→ℝ}
    (hf : MemLp f 2 (product n)) :
    quadraticEnergy f/8+residualEnergy f/54≤∫ y,(f y)^2 ∂product n := by
  have h := KLSImprovement.FiniteIntegralGram.observation_le_of_integral_gram_rows
    (product n) (@jointHead n) jointHead_memLp (by norm_num : (0:ℝ)<1)
    jointHead_abs_gram_row_le hf
  rw [Fintype.sum_sum_type] at h
  have he (p : (Fin n→ℝ)→ℝ) (a : ℝ) :
      (∫ y,f y*(p y/a) ∂product n)=(∫ y,f y*p y ∂product n)/a := by
    simp_rw [←mul_div_assoc]
    rw [integral_div]
  simp only [jointHead,he,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤8),
    Real.sq_sqrt (by norm_num : (0:ℝ)≤54),one_mul,←Finset.sum_div] at h
  exact h

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.jointHead_abs_gram_row_le
#print axioms KLSImprovement.ProductJoint.full_product_quadratic_residual_budget
