import ActualCubicRemainderBridge
import ActualSymmetricAdjacentTerminal

/-! A universally valid, actual-law replacement of the cubic convolution loss.
The remainder Gram is retained rather than replaced by a fixed coefficient cap. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actualAppellProperRemainder_two_eq_zero {n : ℕ}
    {μ : Measure (Space n)} (f : Space n → ℝ) :
    actualAppellProperRemainder μ f 2 = 0 := by
  classical
  funext γ
  change (∑ S : Finset (Fin 2),
    if 2 ≤ S.card ∧ S.card ≤ 2 - 1 then
      actualSubsetAppellContraction μ f 2 S γ else 0) = 0
  apply Finset.sum_eq_zero
  intro S hS
  split_ifs with h
  · omega
  · rfl

theorem actualAppell_centered_weighted_energy_inequality_two_gram_exact
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) {h2 : ℝ} (hh2 : 0 < h2)
    {α q : ℝ} (hα0 : (1 : ℝ)/3 ≤ α) (hα1 : α < 1) (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (2+1) f) (fullClassAppellTensor (2+1) ell)+
        actualAppellEnergy μ f (2+1)*q/h2*
          inner ℝ (fullClassAppellTensor 2 f) (fullClassAppellTensor 2 ell)=
        actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/h2)*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f (2+1)+
      actualAppellEnergy μ f (2+1)*q/h2*actualAppellEnergyHeatGenerator μ f 2+
      actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/h2)*q)*
        actualAppellEnergy μ f 1 ≤ 0) :
    let X := actualAppellEnergy μ f (2+1)
    let Y := actualAppellEnergy μ f 2
    let w := X*q/h2
    let lam := X*(1+(Y/h2)*q)
    w*α*X-15*X-w*(64/(3*(1-α))-18)*Y-
      lam*actualAppellEnergy μ f 1-
      2*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f) ≤ 0 := by
  let X := actualAppellEnergy μ f (2+1)
  let Y := actualAppellEnergy μ f 2
  let w := X*q/h2
  let lam := X*(1+(Y/h2)*q)
  have hw : 0 ≤ w := div_nonneg
    (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hh2.le
  have ht := actual_adjacent_terminal_eq hμ f w lam hstat
  have hpj := actualAppellProperRemainder_three_pairing_le_gram hμ (Lp.memLp f)
  have hr2 := actualAppellProperRemainder_two_eq_zero (μ := μ) f
  have hsplit :
      (actualAppellCoefficient μ f (2+1) ⬝ᵥ actualAppellLowerDriftTensor μ f (2+1))+
        w*(actualAppellCoefficient μ f 2 ⬝ᵥ actualAppellLowerDriftTensor μ f 2) =
      lam*actualAppellEnergy μ f 1+
        (actualAppellCoefficient μ f (2+1) ⬝ᵥ actualAppellProperRemainder μ f (2+1)) := by
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by omega),
      actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by norm_num),
      dotProduct_add, dotProduct_add, hr2, dotProduct_zero, add_zero]
    linarith [ht]
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) (2+1)
    (β := 0) (by norm_num) (by norm_num)
  have hl := actualCovarianceAppellEnergy_generator_lower_two_symmetric hμ (Lp.memLp f) hα0 hα1
  have hm := mul_le_mul_of_nonneg_left hl hw
  change _ ≤ actualAppellEnergyHeatGenerator μ f (2+1) at hj
  norm_num only [sub_zero, div_one, zero_mul, zero_sub] at hj
  change actualAppellEnergyHeatGenerator μ f (2+1)+w*actualAppellEnergyHeatGenerator μ f 2+
    lam*actualAppellEnergy μ f 1 ≤ 0 at hmaximum
  dsimp only
  change w*α*X-15*X-w*(64/(3*(1-α))-18)*Y-
    lam*actualAppellEnergy μ f 1-
    2*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f) ≤ 0
  nlinarith [hj, hm, hsplit, hpj, hmaximum]

theorem actualAppell_centered_weighted_energy_inequality_two_gram
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖ = 1)
    {h2 : ℝ} (hh2 : 0 < h2)
    {α q : ℝ} (hα0 : (1 : ℝ)/3 ≤ α) (hα1 : α < 1) (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (2+1) f) (fullClassAppellTensor (2+1) ell)+
        actualAppellEnergy μ f (2+1)*q/h2*
          inner ℝ (fullClassAppellTensor 2 f) (fullClassAppellTensor 2 ell)=
        actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/h2)*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f (2+1)+
      actualAppellEnergy μ f (2+1)*q/h2*actualAppellEnergyHeatGenerator μ f 2+
      actualAppellEnergy μ f (2+1)*(1+(actualAppellEnergy μ f 2/h2)*q)*
        actualAppellEnergy μ f 1 ≤ 0) :
    let X := actualAppellEnergy μ f (2+1)
    let Y := actualAppellEnergy μ f 2
    let w := X*q/h2
    w*α*X-15*X-w*(64/(3*(1-α))-18)*Y-
      X*(1+(Y/h2)*q)-2*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f) ≤ 0 := by
  have he := actualAppell_centered_weighted_energy_inequality_two_gram_exact
    hμ f hh2 hα0 hα1 hq hstat hmaximum
  have hb : actualAppellEnergy μ f 1 ≤ 1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit, one_pow] using
      fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hlam : 0 ≤ actualAppellEnergy μ f (2+1)*
      (1+(actualAppellEnergy μ f 2/h2)*q) := by
    apply mul_nonneg (actualAppellEnergy_nonneg _ _ _)
    have hu := div_nonneg (actualAppellEnergy_nonneg μ f 2) hh2.le
    linarith [mul_nonneg hu hq]
  have hb' := mul_le_of_le_one_right hlam hb
  dsimp only at he ⊢
  linarith

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeNext.actualAppellProperRemainder_two_eq_zero
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_gram_exact
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_gram
