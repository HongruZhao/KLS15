import ActualCubicJointTerminal

/-! Retain the nonnegative higher-coefficient defect discarded by the
degree-three beta-zero generator bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)}

def actualCubicHigherNoiseDefect (μ : Measure (Space n)) (f : Space n → ℝ) : ℝ :=
  (∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 3)
    (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
    (fun a => actualAppellCoefficient μ f 4 (Fin.cons i a)))+
  12*actualAppellEnergy μ f 3

theorem actualCubicHigherNoiseDefect_nonneg (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    0 ≤ actualCubicHigherNoiseDefect μ f := by
  have hn := actualAppell_noiseCorrection_lower hμ hf
    (fun i a => actualAppellCoefficient μ f (3+1) (Fin.cons i a))
    (β := 0) (by norm_num) (by norm_num)
  rw [actualAppell_next_slices_square, ← actualAppellEnergy_eq_dotProduct] at hn
  norm_num at hn
  unfold actualCubicHigherNoiseDefect
  linarith

theorem actualCubicGenerator_eq_with_higher_defect (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellEnergyHeatGenerator μ f 3 =
      -15*actualAppellEnergy μ f 3-
      2*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellLowerDriftTensor μ f 3)+
      actualCubicHigherNoiseDefect μ f := by
  have hh := actualCovarianceAppellEnergy_generator_exact hμ hf 3
  change actualAppellEnergyHeatGenerator μ f 3 = _ at hh
  norm_num only [Nat.cast_ofNat] at hh
  unfold actualCubicHigherNoiseDefect
  linarith

end KLS.DeterministicBridgeIntegration

namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLSBelow25.CubicSymmetricNoise KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actualAppell_centered_weighted_energy_inequality_two_joint_defect
    {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) {h2 : ℝ} (hh2 : 0 < h2)
    {q : ℝ} (hq : 0 ≤ q)
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
    (w-15)*X-2*w*Y-lam*actualAppellEnergy μ f 1+
      w*(2*square (actualCubicSlotArray μ f)+cross (actualCubicSlotArray μ f))-
      ((4/3 : ℝ)*w+2)*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f)+
      actualCubicHigherNoiseDefect μ f ≤ 0 := by
  let X := actualAppellEnergy μ f (2+1)
  let Y := actualAppellEnergy μ f 2
  let w := X*q/h2
  let lam := X*(1+(Y/h2)*q)
  have hw : 0 ≤ w := div_nonneg
    (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hh2.le
  have ht := actual_adjacent_terminal_eq hμ f w lam hstat
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
  have hj := actualCubicGenerator_eq_with_higher_defect hμ (Lp.memLp f)
  have hl := actualCovarianceAppellEnergy_generator_exact hμ (Lp.memLp f) 2
  change actualAppellEnergyHeatGenerator μ f 2 = _ at hl
  rw [← actualCubic_noise_eq hμ.logConcave (Lp.memLp f),
    actualCubic_noise_eq_remainder_pairing hμ (Lp.memLp f)] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm := mul_le_mul_of_nonneg_left (le_of_eq hl.symm) hw
  have hp := actualAppellProperRemainder_three_pairing_le_gram hμ (Lp.memLp f)
  have hc : 0 ≤ (4/3 : ℝ)*w+2 := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp hc
  change actualAppellEnergyHeatGenerator μ f (2+1)+w*actualAppellEnergyHeatGenerator μ f 2+
    lam*actualAppellEnergy μ f 1 ≤ 0 at hmaximum
  dsimp only
  change (w-15)*X-2*w*Y-lam*actualAppellEnergy μ f 1+
    w*(2*square (actualCubicSlotArray μ f)+cross (actualCubicSlotArray μ f))-
    ((4/3 : ℝ)*w+2)*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f)+
    actualCubicHigherNoiseDefect μ f ≤ 0
  nlinarith [hj, hm, hsplit, hp', hmaximum]

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeIntegration.actualCubicHigherNoiseDefect_nonneg
#print axioms KLS.DeterministicBridgeIntegration.actualCubicGenerator_eq_with_higher_defect
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_joint_defect
