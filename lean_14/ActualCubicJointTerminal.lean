import ActualCubicGramTerminal

/-! The rank-two covariance noise and the cubic proper remainder share one
pairing. Retaining it gives an exact joint replacement before any norm bound. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators

namespace KLSBelow25.CubicRemainderImprovement
open CubicSymmetricNoise
variable {ι : Type*} [Fintype ι]

theorem noise_eq_remainder_pairing (U W : Array3 ι)
    (hW12 : ∀ i j k, W i j k = W j i k)
    (hW23 : ∀ i j k, W i j k = W i k j) :
    noise U W = square W-(4/3 : ℝ)*
      tripleSum (fun i j k => W i j k*remainder U i j k)+2*square U+cross U := by
  have hscale : tripleSum (fun i j k => W i j k*symPart U i j k) =
      (2/3 : ℝ)*tripleSum (fun i j k => W i j k*remainder U i j k) := by
    rw [← tripleSum_smul]
    congr 1
    funext i j k
    unfold symPart remainder
    ring
  rw [noise_eq, symmetric_pairing U W hW12 hW23, hscale]
  ring

end KLSBelow25.CubicRemainderImprovement

namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25.CubicSymmetricNoise
open KLSBelow25.CubicRemainderImprovement
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem actualCubic_noise_eq_remainder_pairing (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    noise (actualCubicSlotArray μ f) (actualCubicNextArray μ f) =
      actualAppellEnergy μ f 3-(4/3 : ℝ)*
        (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      2*square (actualCubicSlotArray μ f)+cross (actualCubicSlotArray μ f) := by
  have hpair : tripleSum (fun i j k => actualCubicNextArray μ f i j k*
      remainder (actualCubicSlotArray μ f) i j k) =
      actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3 := by
    unfold dotProduct
    rw [sum_fin_three_coordinates]
    simp_rw [actualAppellProperRemainder_three_coordinates hμ hf]
    rfl
  rw [noise_eq_remainder_pairing _ _
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf),
    actualCubicNextArray_square, hpair]

end KLS.DeterministicBridgeIntegration

namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLSBelow25.CubicSymmetricNoise KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actualAppell_centered_weighted_energy_inequality_two_joint_pairing
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
      ((4/3 : ℝ)*w+2)*
        (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤ 0 := by
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
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) (2+1)
    (β := 0) (by norm_num) (by norm_num)
  change _ ≤ actualAppellEnergyHeatGenerator μ f (2+1) at hj
  norm_num only [sub_zero, div_one, zero_mul, zero_sub] at hj
  have hl := actualCovarianceAppellEnergy_generator_exact hμ (Lp.memLp f) 2
  change actualAppellEnergyHeatGenerator μ f 2 = _ at hl
  rw [← actualCubic_noise_eq hμ.logConcave (Lp.memLp f),
    actualCubic_noise_eq_remainder_pairing hμ (Lp.memLp f)] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm := mul_le_mul_of_nonneg_left (le_of_eq hl.symm) hw
  change actualAppellEnergyHeatGenerator μ f (2+1)+w*actualAppellEnergyHeatGenerator μ f 2+
    lam*actualAppellEnergy μ f 1 ≤ 0 at hmaximum
  dsimp only
  change (w-15)*X-2*w*Y-lam*actualAppellEnergy μ f 1+
    w*(2*square (actualCubicSlotArray μ f)+cross (actualCubicSlotArray μ f))-
    ((4/3 : ℝ)*w+2)*
      (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤ 0
  nlinarith [hj, hm, hsplit, hmaximum]

theorem actualAppell_centered_weighted_energy_inequality_two_joint_gram
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
      ((4/3 : ℝ)*w+2)*Real.sqrt X*Real.sqrt (actualCubicRemainderGram μ f) ≤ 0 := by
  have he := actualAppell_centered_weighted_energy_inequality_two_joint_pairing
    hμ f hh2 hq hstat hmaximum
  have hp := actualAppellProperRemainder_three_pairing_le_gram hμ (Lp.memLp f)
  have hw : 0 ≤ actualAppellEnergy μ f (2+1)*q/h2 := div_nonneg
    (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hh2.le
  have hc : 0 ≤ (4/3 : ℝ)*(actualAppellEnergy μ f (2+1)*q/h2)+2 := by positivity
  have hp' := mul_le_mul_of_nonneg_left hp hc
  dsimp only at he ⊢
  nlinarith [he, hp']

end KLS.DeterministicBridgeNext

#print axioms KLS.DeterministicBridgeIntegration.actualCubic_noise_eq_remainder_pairing
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_joint_pairing
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality_two_joint_gram
