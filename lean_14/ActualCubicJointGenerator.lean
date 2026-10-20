import ActualCubicJointProperNoise

/-! Weighted actual generator form of the signed rank-two/rank-three
completion. The canonical credit is explicit and must be supplied by a
retained-budget drift estimate before it can be canceled globally. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy KLSBelow25.CoupledEnergy
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem actual_weighted_generator_two_joint_proper_three_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K β θ s lmb : ℝ}
    (hK : 0 < K) (hβ : β < 1)
    (hQcoeff : 2+lmb/(K*s)-4*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0)
    (hRcoeff : 1-8*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0) :
    factorialWeight K 2*(β*actualAppellEnergy μ f 3-
      (64*(1+θ/(6*K))^2/(3*(1-β))-18-8*lmb/(K*s))*actualAppellEnergy μ f 2-
      2*(actualAppellCoefficient μ f 2 ⬝ᵥ actualAppellLowerDriftTensor μ f 2)) ≤
    factorialWeight K 2*actualAppellEnergyHeatGenerator μ f 2-
      2*θ*factorialWeight K 3*
        (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      (lmb*K/s)*(coupledAppellQ μ f K 2 2)^2 := by
  have hh := actual_weighted_noise_two_joint_proper_three_lower hμ hf hK hβ hQcoeff hRcoeff
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf 2]
  norm_num only [Nat.cast_ofNat]
  nlinarith [hh]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actual_weighted_generator_two_joint_proper_three_lower
