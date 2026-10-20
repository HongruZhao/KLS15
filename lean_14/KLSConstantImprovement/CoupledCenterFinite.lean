import KLSConstantImprovement.ActualWeightedWhiteFamily405
import KLSConstantImprovement.ActualFullSymmetricProduction
import KLSConstantImprovement.ActualAffineSlotAlgebra405

/-! Finite sum-of-squares for paying the actual row and response centers
jointly. This module alone does not construct analytic source fields. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace KLSConstantImprovement.CoupledCenterFinite
open KLS ActualWeightedWhiteFamily405 ActualFullSymmetricProduction
open ActualFullSymmetricTensorOrdering MixedCubicRankSlicing FourthCubicProjectionDefect
variable {ι : Type*} [Fintype ι]
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem cyclicAverage_first_second (B : Matrix ι ι ℝ) (N : ι → ι → ι → ℝ)
    (hN : ∀ i j k, N i j k=N j k i) :
    cyclicAverage (firstAction B N)=cyclicAverage (secondAction B N) := by
  funext i j k
  simp only [cyclicAverage,firstAction,secondAction]
  congr 1
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [hN i a k,hN a k i,hN j a i,hN a i j,hN k a j,hN a j k]
  ring

theorem coupled_center_square (X Y : ι → ι → ι → ℝ) :
    (3/50:ℝ)*cubicEnergy Y ≤ cubicEnergy X/4+
      (3/2:ℝ)*cubicEnergy (fun i j k => 2*X i j k+Y i j k) := by
  have hs (i j k : ι) := sq_nonneg ((5/2:ℝ)*X i j k+(6/5:ℝ)*Y i j k)
  have hp (i j k : ι) : (3/50:ℝ)*(Y i j k)^2 ≤
      (X i j k)^2/4+(3/2:ℝ)*(2*X i j k+Y i j k)^2 := by nlinarith only [hs i j k]
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun (i : ι) _ => Finset.sum_le_sum (s:=Finset.univ) fun (j : ι) _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun (k : ι) _ => hp i j k
  simpa only [cubicEnergy,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_div] using hh

theorem affine_target_separation (T Z : ι → ι → ι → ℝ) :
    (112/135:ℝ)*cubicEnergy T-(7/8:ℝ)*cubicEnergy Z ≤
      cubicEnergy (fun i j k => (4/3:ℝ)*T i j k-Z i j k) := by
  have hs (i j k : ι) := sq_nonneg ((8/9:ℝ)*T i j k-(5/4:ℝ)*Z i j k)
  have hp (i j k : ι) : (112/135:ℝ)*(T i j k)^2-(7/8:ℝ)*(Z i j k)^2 ≤
      ((4/3:ℝ)*T i j k-Z i j k)^2 := by nlinarith only [hs i j k]
  have hh := Finset.sum_le_sum (s:=Finset.univ) fun (i : ι) _ => Finset.sum_le_sum (s:=Finset.univ) fun (j : ι) _ =>
    Finset.sum_le_sum (s:=Finset.univ) fun (k : ι) _ => hp i j k
  simpa only [cubicEnergy,Finset.mul_sum,Finset.sum_sub_distrib] using hh

theorem scalar_combined_payment {Xi theta L C Y W q Z : ℝ}
    (hProduction : 4*W/3+3*C/2 ≤ Xi+theta)
    (hCoupled : 3*Y/50 ≤ L/2+3*C/2)
    (hSeparation : 112*W/135-7*Z/8 ≤ Y)
    (hAffine : Z=(W-q)/2) :
    (4/3+847/36000:ℝ)*W+(21/800:ℝ)*q ≤ Xi+theta+L/2 := by
  linarith only [hProduction,hCoupled,hSeparation,hAffine]

end KLSConstantImprovement.CoupledCenterFinite
#print axioms KLSConstantImprovement.CoupledCenterFinite.cyclicAverage_first_second
#print axioms KLSConstantImprovement.CoupledCenterFinite.coupled_center_square
#print axioms KLSConstantImprovement.CoupledCenterFinite.affine_target_separation
#print axioms KLSConstantImprovement.CoupledCenterFinite.scalar_combined_payment
