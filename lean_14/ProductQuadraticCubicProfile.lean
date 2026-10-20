import ProductJointQuadraticLift

/-! The sharp product joint profile. Its maximum occurs at positive
quadratic energy, unlike the decreasing profiles in the old seed class. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace KLSImprovement.ProductJoint
open KLSImprovement.ProductCubic KLSImprovement.ProductPolynomial
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem finite_sqrt_triangle {ι : Type*} [Fintype ι] (r s : ι→ℝ) :
    Real.sqrt (∑ i,(r i+s i)^2)≤
      Real.sqrt (∑ i,(r i)^2)+Real.sqrt (∑ i,(s i)^2) := by
  let R : EuclideanSpace ℝ ι := WithLp.toLp 2 r
  let S : EuclideanSpace ℝ ι := WithLp.toLp 2 s
  have hn (v : EuclideanSpace ℝ ι) : Real.sqrt (∑ i,(v i)^2)=‖v‖ := by
    rw [←EuclideanSpace.real_norm_sq_eq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg v)]
  change Real.sqrt (∑ i,((R+S) i)^2)≤Real.sqrt (∑ i,(R i)^2)+Real.sqrt (∑ i,(S i)^2)
  simp only [hn]
  exact norm_add_le R S

def cubicEnergy {n : ℕ} (f : (Fin n→ℝ)→ℝ) : ℝ :=
  ∑ I,(∫ y,f y*cubicBasis I y ∂product n)^2

theorem quadraticEnergy_nonneg {n : ℕ} (f : (Fin n→ℝ)→ℝ) : 0≤quadraticEnergy f :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)
theorem residualEnergy_nonneg {n : ℕ} (f : (Fin n→ℝ)→ℝ) : 0≤residualEnergy f :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)
theorem cubicEnergy_nonneg {n : ℕ} (f : (Fin n→ℝ)→ℝ) : 0≤cubicEnergy f :=
  Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- The exact product benchmark upper profile, in full ordered-index form. -/
theorem full_product_quadratic_cubic_sqrt_profile {n : ℕ} {f : (Fin n→ℝ)→ℝ}
    (hf : MemLp f 2 (product n)) :
    Real.sqrt (cubicEnergy f)≤(9/2:ℝ)*Real.sqrt (quadraticEnergy f)+
      Real.sqrt (54*((∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8)) := by
  let a : Fin n→Fin n→ℝ := fun i j=>∫ y,f y*pairBasis ![i,j] y ∂product n
  let C : ℝ := ∑ I,(quadraticLift a I)^2
  have hC : C≤(81/4:ℝ)*quadraticEnergy f := by
    have h := quadraticLift_square_sum_le a
    simpa only [quadraticEnergy,sum_pairs,a] using h
  have hR : residualEnergy f≤54*((∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8) := by
    have h := full_product_quadratic_residual_budget hf
    linarith
  have htri : Real.sqrt (cubicEnergy f)≤Real.sqrt (residualEnergy f)+Real.sqrt C := by
    unfold cubicEnergy residualEnergy
    simp_rw [cubic_coefficient_eq_residual_add_lift hf]
    exact finite_sqrt_triangle (fun I=>∫ y,f y*residualBasis I y ∂product n)
      (quadraticLift a)
  have hCsqrt : Real.sqrt C≤(9/2:ℝ)*Real.sqrt (quadraticEnergy f) := by
    calc
      _ ≤ Real.sqrt ((81/4:ℝ)*quadraticEnergy f) := Real.sqrt_le_sqrt hC
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤81/4)];norm_num
  have hRsqrt := Real.sqrt_le_sqrt hR
  linarith

theorem full_product_quadratic_cubic_squared_profile {n : ℕ} {f : (Fin n→ℝ)→ℝ}
    (hf : MemLp f 2 (product n)) :
    cubicEnergy f≤((9/2:ℝ)*Real.sqrt (quadraticEnergy f)+
      Real.sqrt (54*((∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8)))^2 := by
  have h := full_product_quadratic_cubic_sqrt_profile hf
  have hn : 0≤(9/2:ℝ)*Real.sqrt (quadraticEnergy f)+
      Real.sqrt (54*((∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8)) := by positivity
  have he := Real.sq_sqrt (cubicEnergy_nonneg f)
  nlinarith [Real.sqrt_nonneg (cubicEnergy f)]

/-- Exact square defect: the sharp cap is reached at Y=6V. -/
theorem joint_profile_square_defect (V Y : ℝ) (hY : 0≤Y) (hrem : 0≤V-Y/8) :
    216*V-((9/2:ℝ)*Real.sqrt Y+Real.sqrt (54*(V-Y/8)))^2=
      3*((3/2:ℝ)*Real.sqrt Y-Real.sqrt (54*(V-Y/8)))^2 := by
  have hy:=Real.sq_sqrt hY
  have hr:=Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤54) hrem)
  nlinarith only [hy,hr]

theorem full_product_cubic_cap_with_quadratic_defect {n : ℕ} {f : (Fin n→ℝ)→ℝ}
    (hf : MemLp f 2 (product n)) :
    cubicEnergy f+3*((3/2:ℝ)*Real.sqrt (quadraticEnergy f)-
      Real.sqrt (54*((∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8)))^2≤
        216*(∫ y,(f y)^2 ∂product n) := by
  have hb:=full_product_quadratic_residual_budget hf
  have hr:=residualEnergy_nonneg f
  have hrem : 0≤(∫ y,(f y)^2 ∂product n)-quadraticEnergy f/8 := by linarith
  have hgap:=joint_profile_square_defect (∫ y,(f y)^2 ∂product n)
    (quadraticEnergy f) (quadraticEnergy_nonneg f) hrem
  have hp:=full_product_quadratic_cubic_squared_profile hf
  linarith

end KLSImprovement.ProductJoint
#print axioms KLSImprovement.ProductJoint.finite_sqrt_triangle
#print axioms KLSImprovement.ProductJoint.full_product_quadratic_cubic_sqrt_profile
#print axioms KLSImprovement.ProductJoint.full_product_quadratic_cubic_squared_profile
#print axioms KLSImprovement.ProductJoint.joint_profile_square_defect
#print axioms KLSImprovement.ProductJoint.full_product_cubic_cap_with_quadratic_defect
