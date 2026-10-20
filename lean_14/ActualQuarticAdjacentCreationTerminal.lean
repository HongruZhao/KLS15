import ActualCenteredAdjacentTerminal
import ActualProperCubicCreation
import ActualProperQuarticCreation
import ActualSymmetricCubicNoise

/-! Literal centered rank-three/rank-four adjacent inequality, retaining
the second energy in both genuine proper-creation remainders. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actualAppell_centered_weighted_energy_inequality_three_creation {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {H : ℝ} (hH : 0 < H)
    {α q : ℝ} (hα0 : (1 : ℝ)/2 ≤ α) (hα1 : α < 1) (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor 4 f) (fullClassAppellTensor 4 ell)+
        actualAppellEnergy μ f 4*q/H*
          inner ℝ (fullClassAppellTensor 3 f) (fullClassAppellTensor 3 ell)=
        actualAppellEnergy μ f 4*(1+(actualAppellEnergy μ f 3/H)*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f 4+
      actualAppellEnergy μ f 4*q/H*actualAppellEnergyHeatGenerator μ f 3+
      actualAppellEnergy μ f 4*(1+(actualAppellEnergy μ f 3/H)*q)*
        actualAppellEnergy μ f 1 ≤ 0) :
    let X := actualAppellEnergy μ f 4
    let Y := actualAppellEnergy μ f 3
    let Z := actualAppellEnergy μ f 2
    let w := X*q/H
    w*α*X-28*X-w*(44/(1-α)-33)*Y-X*(1+(Y/H)*q)-
      2*Real.sqrt X*(Real.sqrt (176*Y)+Real.sqrt (13824*Z))-
      2*w*Real.sqrt Y*Real.sqrt (48*Z) ≤ 0 := by
  let X := actualAppellEnergy μ f 4
  let Y := actualAppellEnergy μ f 3
  let Z := actualAppellEnergy μ f 2
  let w := X*q/H
  let lam := X*(1+(Y/H)*q)
  have hw : 0 ≤ w := div_nonneg (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hH.le
  have hlam : 0 ≤ lam := mul_nonneg (actualAppellEnergy_nonneg _ _ _)
    (by have hu := div_nonneg (actualAppellEnergy_nonneg μ f 3) hH.le
        linarith [mul_nonneg hu hq])
  have ht := actual_adjacent_terminal_eq (k:=3) hμ f w lam hstat
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hlamb := mul_le_of_le_one_right hlam hb
  have hp4 := actualAppellProperRemainder_four_pairing_le_creation hμ (Lp.memLp f)
  have hp3 := actualAppellProperRemainder_three_pairing_le hμ (Lp.memLp f)
  have hp3' := mul_le_mul_of_nonneg_left hp3 hw
  have hsplit :
      (actualAppellCoefficient μ f 4 ⬝ᵥ actualAppellLowerDriftTensor μ f 4)+
        w*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellLowerDriftTensor μ f 3) =
      lam*actualAppellEnergy μ f 1+
        (actualAppellCoefficient μ f 4 ⬝ᵥ actualAppellProperRemainder μ f 4)+
        w*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) := by
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by norm_num),
      actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by norm_num),
      dotProduct_add,dotProduct_add]
    linarith [ht]
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) 4
    (β:=0) (by norm_num) (by norm_num)
  have hl := actualCovarianceAppellEnergy_generator_lower_three_symmetric hμ (Lp.memLp f) hα0 hα1
  have hm := mul_le_mul_of_nonneg_left hl hw
  change _ ≤ actualAppellEnergyHeatGenerator μ f 4 at hj
  norm_num at hj
  change actualAppellEnergyHeatGenerator μ f 4+w*actualAppellEnergyHeatGenerator μ f 3+
    lam*actualAppellEnergy μ f 1 ≤ 0 at hmaximum
  dsimp only
  change w*α*X-28*X-w*(44/(1-α)-33)*Y-lam-
    2*Real.sqrt X*(Real.sqrt (176*Y)+Real.sqrt (13824*Z))-
    2*w*Real.sqrt Y*Real.sqrt (48*Z) ≤ 0
  nlinarith [hj,hm,hsplit,hp4,hp3',hlamb,hmaximum]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_three_creation
