import LaplaceJointProfileLaw
import ActualCubicPolynomialFormula
import ActualAppellQuadraticSeed

/-! The exponential product's sharp joint profile fails for the actual
variance-one symmetric Laplace law. The original coefficients are computed
from normalized tilt derivatives, not replaced by assumed polynomial data. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace KLSImprovement.LaplaceJoint
open KLS KLS.DeterministicBridgeIntegration KLS.DeterministicBridgeNext
open KLSImprovement.CubicFormula
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure laplaceMeasure := laplaceMeasure_isProbability

theorem moment_one : (∫ x:Space 1,x 0^1 ∂laplaceMeasure)=0 := by
  have h:=integral_laplace_odd 0
  norm_num at h
  simpa only [pow_one] using h
theorem moment_two : (∫ x:Space 1,x 0^2 ∂laplaceMeasure)=1 := by
  have h:=integral_laplace_even 1
  norm_num at h
  exact h
theorem moment_three : (∫ x:Space 1,x 0^3 ∂laplaceMeasure)=0 := by
  have h:=integral_laplace_odd 1
  norm_num at h
  exact h
theorem moment_four : (∫ x:Space 1,x 0^4 ∂laplaceMeasure)=6 := by
  have h:=integral_laplace_even 2
  norm_num at h
  exact h
theorem moment_five : (∫ x:Space 1,x 0^5 ∂laplaceMeasure)=0 := by
  have h:=integral_laplace_odd 2
  norm_num at h
  exact h
theorem moment_six : (∫ x:Space 1,x 0^6 ∂laplaceMeasure)=90 := by
  have h:=integral_laplace_even 3
  norm_num at h
  exact h

def cubicWitness (x : Space 1) : ℝ := x 0^3-3*x 0

theorem cubicWitness_memLp : MemLp cubicWitness 2 laplaceMeasure := by
  have h : MemLp (fun x:Space 1=>x 0) 2 laplaceMeasure := by
    simpa only [pow_one] using laplace_power_memLp 1
  exact (laplace_power_memLp 3).sub (h.const_mul 3)

theorem integral_cubicWitness_times_power (m : ℕ) :
    (∫ x:Space 1,cubicWitness x*x 0^m ∂laplaceMeasure)=
      (∫ x:Space 1,x 0^(m+3) ∂laplaceMeasure)-
        3*(∫ x:Space 1,x 0^(m+1) ∂laplaceMeasure) := by
  have he : (fun x:Space 1=>cubicWitness x*x 0^m)=
      (fun x=>x 0^(m+3)-3*x 0^(m+1)) := by
    funext x
    unfold cubicWitness
    simp only [pow_add,pow_one]
    ring
  rw [he,integral_sub (f:=fun x:Space 1=>x 0^(m+3))
    (g:=fun x:Space 1=>3*x 0^(m+1)) (laplace_power_integrable _)
    ((laplace_power_integrable _).const_mul 3),integral_const_mul]

theorem integral_cubicWitness : (∫ x,cubicWitness x ∂laplaceMeasure)=0 := by
  have h:=integral_cubicWitness_times_power 0
  norm_num only [Nat.zero_add,pow_zero,mul_one] at h
  rw [moment_three,moment_one] at h
  norm_num at h
  exact h

theorem integral_cubicWitness_coordinate :
    (∫ x:Space 1,cubicWitness x*x 0 ∂laplaceMeasure)=3 := by
  have h:=integral_cubicWitness_times_power 1
  norm_num only [Nat.reduceAdd,pow_one] at h
  rw [moment_four,moment_two] at h
  norm_num at h
  exact h

theorem integral_cubicWitness_square_coordinate :
    (∫ x:Space 1,cubicWitness x*x 0^2 ∂laplaceMeasure)=0 := by
  have h:=integral_cubicWitness_times_power 2
  norm_num only [Nat.reduceAdd] at h
  rw [moment_five,moment_three] at h
  norm_num at h
  exact h

theorem integral_cubicWitness_cube_coordinate :
    (∫ x:Space 1,cubicWitness x*x 0^3 ∂laplaceMeasure)=72 := by
  have h:=integral_cubicWitness_times_power 3
  norm_num only [Nat.reduceAdd] at h
  rw [moment_six,moment_four] at h
  norm_num at h
  exact h

theorem cubicWitness_square : (∫ x,(cubicWitness x)^2 ∂laplaceMeasure)=63 := by
  have h1 : MemLp (fun x:Space 1=>x 0) 2 laplaceMeasure := by
    simpa only [pow_one] using laplace_power_memLp 1
  have he : (fun x:Space 1=>(cubicWitness x)^2)=
      (fun x=>cubicWitness x*x 0^3-3*(cubicWitness x*x 0)) := by
    funext x
    unfold cubicWitness
    ring
  rw [he,integral_sub (f:=fun x:Space 1=>cubicWitness x*x 0^3)
    (g:=fun x:Space 1=>3*(cubicWitness x*x 0))
    (cubicWitness_memLp.integrable_mul (laplace_power_memLp 3))
    ((cubicWitness_memLp.integrable_mul h1).const_mul 3),integral_const_mul,
    integral_cubicWitness_cube_coordinate,integral_cubicWitness_coordinate]
  norm_num

theorem actual_cubicWitness_coefficient_two :
    actualAppellCoefficient laplaceMeasure cubicWitness 2 (fun _=>0)=0 := by
  rw [actualAppellCoefficient_two_eq_quadraticCovariance laplaceMeasure_admissible
    cubicWitness_memLp,quadraticCovarianceMatrix,
    covariance_eq_sub cubicWitness_memLp
      (laplaceMeasure_admissible.quadraticVarianceEight_unconditional.memLp_coordinate_mul 0 0),
    integral_cubicWitness,zero_mul,sub_zero]
  simpa only [Pi.mul_apply,pow_two] using integral_cubicWitness_square_coordinate

theorem actual_cubicWitness_coefficient_three :
    actualAppellCoefficient laplaceMeasure cubicWitness 3 (fun _=>0)=63 := by
  have hi : (fun _:Fin 3=>(0:Fin 1))=![0,0,0] := by funext a;fin_cases a <;>simp
  have hp : (∫ x:Space 1,x 0*cubicWitness x*(x 0*x 0) ∂laplaceMeasure)=72 := by
    convert integral_cubicWitness_cube_coordinate using 1
    congr 1
    funext x
    ring
  have hlinear : (∫ x:Space 1,x 0*cubicWitness x ∂laplaceMeasure)=3 := by
    convert integral_cubicWitness_coordinate using 1
    congr 1
    funext x
    ring
  rw [hi,actualAppellCoefficient_three_moment_formula laplaceMeasure_logConcave
    laplaceMeasure_isIsotropic cubicWitness_memLp]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    ite_true,hp,hlinear,integral_cubicWitness_coordinate,integral_cubicWitness,
    mul_zero,sub_zero,mul_one,one_mul]

theorem actual_energy_scalar (f : Space 1→ℝ) (m : ℕ) :
    actualAppellEnergy laplaceMeasure f m=
      (actualAppellCoefficient laplaceMeasure f m (fun _=>0))^2 := by
  simp only [actualAppellEnergy,Fintype.sum_unique]
  rfl

theorem actual_cubicWitness_energy_two : actualAppellEnergy laplaceMeasure cubicWitness 2=0 := by
  rw [actual_energy_scalar,actual_cubicWitness_coefficient_two]
  norm_num
theorem actual_cubicWitness_energy_three :
    actualAppellEnergy laplaceMeasure cubicWitness 3=3969 := by
  rw [actual_energy_scalar,actual_cubicWitness_coefficient_three]
  norm_num

/-- An actual admissible law disproves the zero-quadratic intercept 54. -/
theorem exists_admissible_failure_to_intercept_fifty_four :
    ∃ μ:Measure (Space 1),admissibleMeasure μ ∧∃ f:Space 1→ℝ,MemLp f 2 μ ∧
      actualAppellEnergy μ f 2=0 ∧
        54*(∫ x,(f x)^2 ∂μ)<actualAppellEnergy μ f 3 := by
  refine ⟨laplaceMeasure,laplaceMeasure_admissible,cubicWitness,cubicWitness_memLp,
    actual_cubicWitness_energy_two,?_⟩
  rw [cubicWitness_square,actual_cubicWitness_energy_three]
  norm_num

theorem universal_exponential_joint_profile_is_false :
    ¬∀ μ:Measure (Space 1),admissibleMeasure μ→∀ f:Space 1→ℝ,MemLp f 2 μ→
      Real.sqrt (actualAppellEnergy μ f 3)≤(9/2:ℝ)*Real.sqrt (actualAppellEnergy μ f 2)+
        Real.sqrt (54*((∫ x,(f x)^2 ∂μ)-actualAppellEnergy μ f 2/8)) := by
  intro h
  have hp:=h laplaceMeasure laplaceMeasure_admissible cubicWitness cubicWitness_memLp
  rw [actual_cubicWitness_energy_three,actual_cubicWitness_energy_two,cubicWitness_square] at hp
  norm_num at hp
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3402)
  nlinarith [Real.sqrt_nonneg (3402:ℝ)]

theorem actual_joint_profile_square_defect_violation :
    actualAppellEnergy laplaceMeasure cubicWitness 3+
      3*((3/2:ℝ)*Real.sqrt (actualAppellEnergy laplaceMeasure cubicWitness 2)-
        Real.sqrt (54*((∫ x,(cubicWitness x)^2 ∂laplaceMeasure)-
          actualAppellEnergy laplaceMeasure cubicWitness 2/8)))^2-
      216*(∫ x,(cubicWitness x)^2 ∂laplaceMeasure)=567 := by
  rw [actual_cubicWitness_energy_three,actual_cubicWitness_energy_two,cubicWitness_square]
  norm_num [Real.sq_sqrt]

end KLSImprovement.LaplaceJoint
#print axioms KLSImprovement.LaplaceJoint.actual_cubicWitness_coefficient_two
#print axioms KLSImprovement.LaplaceJoint.actual_cubicWitness_coefficient_three
#print axioms KLSImprovement.LaplaceJoint.actual_cubicWitness_energy_three
#print axioms KLSImprovement.LaplaceJoint.exists_admissible_failure_to_intercept_fifty_four
#print axioms KLSImprovement.LaplaceJoint.universal_exponential_joint_profile_is_false
#print axioms KLSImprovement.LaplaceJoint.actual_joint_profile_square_defect_violation
