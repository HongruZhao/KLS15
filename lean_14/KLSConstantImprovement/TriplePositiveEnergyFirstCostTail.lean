import KLSConstantImprovement.TriplePositiveEnergyWeightedBudget
import KLSConstantImprovement.PositiveEnergyWeightTail

/-! Exact vanishing of the selected triple first-cost modification. -/
noncomputable section
open scoped BigOperators
namespace KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open KLSConstantImprovement.PositiveEnergyWeightedDrift
open KLSConstantImprovement.TriplePositiveEnergyWeightedDrift
open KLSConstantImprovement.TriplePositiveEnergyWeightedBudgetDrift
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

theorem rawFirstCost_eq_of_zero (young t theta lambda zeta : ℕ → ℝ)
    (d : ℕ) (hd : 4 ≤ d) (hz : zeta (d-2)=0) :
    rawFirstCost young t theta lambda zeta d=firstCost young t theta lambda d := by
  have htheta:tripleHarmonicThetaProfile zeta d=0 := by
    simp [tripleHarmonicThetaProfile,hd,hz,harmonicRatioTheta,selectedHarmonicTheta]
  have hlambda:tripleHarmonicLambdaProfile zeta (d-2)=0 := by
    simp [tripleHarmonicLambdaProfile,harmonicRatioLambda,selectedHarmonicLambda,hz]
  unfold rawFirstCost extra
  rw [ite_eq_left hd,htheta]
  simp only [zero_mul,add_zero]
  unfold selectedFirstCost firstCost
  apply Finset.sum_congr rfl
  intro a ha
  by_cases ha2:a=2
  · subst a
    have hs:d-2+1=d-1:=by omega
    simp [twoRowsProfile,twoRowsLambda,thetaTriangleCoefficient,selectiveTriangleFraction,hs]
  · by_cases ha3:a=3
    · subst a
      have hs:d-3+1=d-2:=by omega
      simp [twoRowsProfile,twoRowsLambda,thetaTriangleCoefficient,selectiveTriangleFraction,hs,htheta,hlambda]
    · simp [twoRowsProfile,twoRowsLambda,thetaTriangleCoefficient,selectiveTriangleFraction,ha2,ha3]

end KLSConstantImprovement.TriplePositiveEnergyFirstCostTail
#print axioms KLSConstantImprovement.TriplePositiveEnergyFirstCostTail.rawFirstCost_eq_of_zero
