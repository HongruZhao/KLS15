import KLSConstantImprovement.JointProductionHalfsum

/-! Future parameter optimization. Finite sum-of-squares only: this file
neither asserts actual source binding nor a universal cubic improvement. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.JointProductionParameterSOS
open MixedCubicRankSlicing FourthCubicProjectionDefect

theorem scalar_joint_parameter {k : ℝ} (hk : 0 ≤ k) (t a b z : ℝ) :
    (2*k/(3*(k+6)))*t^2 ≤ (k/2)*(a^2+b^2)+
      (3/2:ℝ)*(2*a+(4/3:ℝ)*t-z)^2+(2*b-z)^2/2 := by
  have h4 : 0 < k+4 := by linarith
  have h6 : 0 < k+6 := by linarith
  have h12 : 0 < k+12 := by linarith
  have hIdentity : (k/2)*(a^2+b^2)+(3/2:ℝ)*(2*a+(4/3:ℝ)*t-z)^2+
      (2*b-z)^2/2-(2*k/(3*(k+6)))*t^2 =
      ((k+12)/2)*(a-6*z/(k+12)+8*t/(k+12))^2+
        ((k+4)/2)*(b-2*z/(k+4))^2+
          (2*k*(k+6)/((k+12)*(k+4)))*(z-(k+4)*t/(k+6))^2 := by
    field_simp [ne_of_gt h4,ne_of_gt h6,ne_of_gt h12]
    <;> ring
  have hs1 : 0 ≤ ((k+12)/2)*(a-6*z/(k+12)+8*t/(k+12))^2 := by positivity
  have hs2 : 0 ≤ ((k+4)/2)*(b-2*z/(k+4))^2 := by positivity
  have hs3 : 0 ≤ (2*k*(k+6)/((k+12)*(k+4)))*(z-(k+4)*t/(k+6))^2 := by positivity
  linarith only [hIdentity,hs1,hs2,hs3]

variable {ι : Type*} [Fintype ι]
theorem tensor_joint_parameter {k : ℝ} (hk : 0 ≤ k) (T A B Z : ι → ι → ι → ℝ) :
    (2*k/(3*(k+6)))*cubicEnergy T ≤ (k/2)*(cubicEnergy A+cubicEnergy B)+
      (3/2:ℝ)*cubicEnergy (fun i j l => 2*A i j l+(4/3:ℝ)*T i j l-Z i j l)+
        cubicEnergy (fun i j l => 2*B i j l-Z i j l)/2 := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun (i : ι) _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun (j : ι) _ =>
      Finset.sum_le_sum (s:=Finset.univ) fun (l : ι) _ =>
        scalar_joint_parameter hk (T i j l) (A i j l) (B i j l) (Z i j l)
  simpa only [cubicEnergy,←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] using hh

end KLSConstantImprovement.JointProductionParameterSOS
#print axioms KLSConstantImprovement.JointProductionParameterSOS.scalar_joint_parameter
#print axioms KLSConstantImprovement.JointProductionParameterSOS.tensor_joint_parameter
