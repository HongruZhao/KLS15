import ActualCenteredAdjacentTerminal
import ActualProperCubicCreation
import ActualSymmetricQuadraticNoise

/-! Actual centered adjacent rank-two energy inequality retaining the literal
proper cubic creation norm and actual second-degree energy. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actualAppell_centered_weighted_energy_inequality_two_creation {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {h : ℕ → ℝ}
    (hhk : 0<h 2) (hh : ∀ r : ℕ,1≤r → r≤2 → 0≤h r)
    (hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r≤h r*(∫ x,(g x)^2 ∂μ))
    {α q : ℝ} (hα0 : (1 : ℝ)/3≤α) (hα1 : α<1) (hq : 0≤q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (2+1) f) (fullClassAppellTensor (2+1) ell)+
        actualAppellEnergy μ f (2+1)*q/(h 2)*
          inner ℝ (fullClassAppellTensor 2 f) (fullClassAppellTensor 2 ell)=
        actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/(h 2))*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f (2+1)+
      actualAppellEnergy μ f (2+1)*q/(h 2)*actualAppellEnergyHeatGenerator μ f 2+
      actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/(h 2))*q)*
        actualAppellEnergy μ f 1≤0) :
    let X := actualAppellEnergy μ f (2+1)
    let Y := actualAppellEnergy μ f 2
    let w := X*q/(h 2)
    w*α*X-15*X-
      w*(64/(3*(1-α))-18)*Y-
      X*(1+(Y/(h 2))*q)-2*Real.sqrt X*Real.sqrt (48*Y)-
      2*w*Real.sqrt Y*actualLowerConvolution h 2≤0 := by
  let X := actualAppellEnergy μ f (2+1)
  let Y := actualAppellEnergy μ f 2
  let w := X*q/(h 2)
  let lam := X*(1+(Y/(h 2))*q)
  have hw : 0≤w := div_nonneg (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hhk.le
  have hlam : 0≤lam := mul_nonneg (actualAppellEnergy_nonneg _ _ _)
    (by have hu := div_nonneg (actualAppellEnergy_nonneg μ f 2) hhk.le
        linarith [mul_nonneg hu hq])
  have ht := actual_adjacent_terminal_eq hμ f w lam hstat
  have hb : actualAppellEnergy μ f 1≤1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hlamb := mul_le_of_le_one_right hlam hb
  have hpj := actualAppellProperRemainder_three_pairing_le hμ (Lp.memLp f)
  have hpk := actualAppellProperRemainder_pairing_le hμ f hunit (show 2≤2+1 by omega) hh hprevious
  have hpk' := mul_le_mul_of_nonneg_left hpk hw
  have hsplit :
      (actualAppellCoefficient μ f (2+1) ⬝ᵥ actualAppellLowerDriftTensor μ f (2+1))+
        w*(actualAppellCoefficient μ f 2 ⬝ᵥ actualAppellLowerDriftTensor μ f 2) =
      lam*actualAppellEnergy μ f 1+
        (actualAppellCoefficient μ f (2+1) ⬝ᵥ actualAppellProperRemainder μ f (2+1))+
        w*(actualAppellCoefficient μ f 2 ⬝ᵥ actualAppellProperRemainder μ f 2) := by
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by omega),
      actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by norm_num),
      dotProduct_add,dotProduct_add]
    linarith [ht]
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) (2+1)
    (β:=0) (by norm_num) (by norm_num)
  have hl := actualCovarianceAppellEnergy_generator_lower_two_symmetric hμ (Lp.memLp f) hα0 hα1
  have hm := mul_le_mul_of_nonneg_left hl hw
  change _≤actualAppellEnergyHeatGenerator μ f (2+1) at hj
  norm_num only [sub_zero,div_one,zero_mul,zero_sub] at hj
  change actualAppellEnergyHeatGenerator μ f (2+1)+w*actualAppellEnergyHeatGenerator μ f 2+
    lam*actualAppellEnergy μ f 1≤0 at hmaximum
  dsimp only
  change w*α*X-15*X-
    w*(64/(3*(1-α))-18)*Y-
    lam-2*Real.sqrt X*Real.sqrt (48*Y)-
    2*w*Real.sqrt Y*actualLowerConvolution h 2≤0
  nlinarith [hj,hm,hsplit,hpj,hpk',hlamb,hmaximum]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_creation
