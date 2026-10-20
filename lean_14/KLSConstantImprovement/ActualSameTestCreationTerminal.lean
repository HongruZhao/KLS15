import KLSConstantImprovement.ActualSameTestCubicCreationCovariance
import ActualCreationCenteredAdjacentTerminal

/-! Full original-law same-test creation terminal. Both entries of the
minimum are genuine bounds for the same f and its full proper remainder.
The positive threshold transfer divides by X rather than sqrt(XY), and
therefore needs no X >= 18Y restriction. Author performs no compilation. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLSConstantImprovement.OriginalUpperRecovery6SameTestTerminalDraft
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open OriginalUpperRecovery6PiecewiseEnvelopeDraft
open OriginalUpperRecovery6SameTestCovarianceDraft
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

def sameTestClosedRatio (M Y : ℝ) : ℝ :=
  (Y+Real.sqrt ((4*supportC-Y)*Y*(72*supportC/M-1)))/(2*supportC)

def sameTestCreationRatio (M Y : ℝ) : ℝ :=
  min (sameTestClosedRatio M Y) (Real.sqrt (48*Y)/Real.sqrt M)

theorem sameTestCreationRatio_le_closed (M Y : ℝ) :
    sameTestCreationRatio M Y ≤ sameTestClosedRatio M Y := min_le_left _ _

theorem sameTestCreationRatio_le_cap (M Y : ℝ) :
    sameTestCreationRatio M Y ≤ Real.sqrt (48*Y)/Real.sqrt M := min_le_right _ _

theorem sameTestClosedRatio_nonneg {M Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ sameTestClosedRatio M Y := by
  unfold sameTestClosedRatio
  exact div_nonneg (add_nonneg hY (Real.sqrt_nonneg _)) (by norm_num [supportC])

theorem sameTestCreationRatio_nonneg {M Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ sameTestCreationRatio M Y := by
  exact le_min (sameTestClosedRatio_nonneg hY)
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem same_test_closed_threshold_transfer {M X Y : ℝ}
    (hM : 0 < M) (hMX : M ≤ X) (hY : 0 ≤ Y) (hY8 : Y ≤ 8) :
    (X*Y+Real.sqrt ((4*supportC-Y)*X*Y*(72*supportC-X)))/(2*supportC) ≤
      X*sameTestClosedRatio M Y := by
  have hX : 0 < X := hM.trans_le hMX
  have hC : 0 < supportC := by norm_num [supportC]
  have hD : 0 ≤ (4*supportC-Y)*Y := mul_nonneg (by norm_num [supportC] at *; linarith) hY
  have hd : 72*supportC/X ≤ 72*supportC/M :=
    div_le_div_of_nonneg_left (by positivity) hM hMX
  have hs := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hd 1) hD)
  have he : (4*supportC-Y)*X*Y*(72*supportC-X) =
      X^2*((4*supportC-Y)*Y*(72*supportC/X-1)) := by
    field_simp [hX.ne'] <;> ring
  have hr : Real.sqrt ((4*supportC-Y)*X*Y*(72*supportC-X)) ≤
      X*Real.sqrt ((4*supportC-Y)*Y*(72*supportC/M-1)) := by
    rw [he,Real.sqrt_mul (sq_nonneg X),Real.sqrt_sq hX.le]
    exact mul_le_mul_of_nonneg_left hs hX.le
  unfold sameTestClosedRatio
  have hb := div_le_div_of_nonneg_right
    (add_le_add_left hr (X*Y)) (show 0 ≤ 2*supportC by positivity)
  convert hb using 1 <;> ring

theorem actual_same_test_proper_pairing_le_barrier {n : ℕ} {μ : Measure (Space n)}
    (hn : 1 ≤ n) (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1)
    {M : ℝ} (hM : 0 < M) (hMX : M ≤ actualAppellEnergy μ f 3) :
    (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤
      actualAppellEnergy μ f 3*sameTestCreationRatio M (actualAppellEnergy μ f 2) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hi : (∫ x,(f x)^2 ∂μ) = 1 := by
    rw [←actualLp_norm_sq_eq_integral,hunit]
    norm_num
  have hY := actualAppellEnergy_nonneg μ f 2
  have hY8 := actualAppellEnergy_two_le_eight_integral hμ (Lp.memLp f)
  rw [hi,mul_one] at hY8
  have hb := actual_creation_same_test_upper_unit hn hμ (Lp.memLp f) hi
  have hnew : (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤
      actualAppellEnergy μ f 3*sameTestClosedRatio M (actualAppellEnergy μ f 2) :=
    hb.trans (same_test_closed_threshold_transfer hM hMX hY hY8)
  have hX : 0 < actualAppellEnergy μ f 3 := hM.trans_le hMX
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hroot := Real.sqrt_le_sqrt hMX
  have hx : Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt M ≤ actualAppellEnergy μ f 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (actualAppellEnergy μ f 3)),
      Real.sq_sqrt hX.le]
  have hcap : (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) ≤
      actualAppellEnergy μ f 3*(Real.sqrt (48*actualAppellEnergy μ f 2)/Real.sqrt M) := by
    have hp := actualAppellProperRemainder_three_pairing_le hμ (Lp.memLp f)
    have hh := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg (48*actualAppellEnergy μ f 2))
    have hc : Real.sqrt (actualAppellEnergy μ f 3)*Real.sqrt (48*actualAppellEnergy μ f 2) ≤
        (actualAppellEnergy μ f 3*Real.sqrt (48*actualAppellEnergy μ f 2))/Real.sqrt M := by
      apply (le_div_iff₀ hsM).mpr
      nlinarith [hh]
    exact hp.trans (by convert hc using 1 <;> ring)
  unfold sameTestCreationRatio
  by_cases hc : sameTestClosedRatio M (actualAppellEnergy μ f 2) ≤
      Real.sqrt (48*actualAppellEnergy μ f 2)/Real.sqrt M
  · rw [min_eq_left hc]
    exact hnew
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hc))]
    exact hcap

theorem actualAppell_centered_weighted_energy_inequality_two_same_test_creation {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {h : ℕ → ℝ}
    (hhk : 0<h 2) (hh : ∀ r : ℕ,1≤r → r≤2 → 0≤h r)
    (hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r≤h r*(∫ x,(g x)^2 ∂μ))
    {M : ℝ} (hM : 0 < M) (hMX : M≤actualAppellEnergy μ f 3)
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
    w*α*X-15*X-w*(64/(3*(1-α))-18)*Y-
      X*(1+(Y/(h 2))*q)-2*X*sameTestCreationRatio M Y-
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
  have hpj := actual_same_test_proper_pairing_le_barrier hn hμ f hunit hM hMX
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
  change w*α*X-15*X-w*(64/(3*(1-α))-18)*Y-
    lam-2*X*sameTestCreationRatio M Y-
    2*w*Real.sqrt Y*actualLowerConvolution h 2≤0
  nlinarith [hj,hm,hsplit,hpj,hpk',hlamb,hmaximum]

end KLSConstantImprovement.OriginalUpperRecovery6SameTestTerminalDraft
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestTerminalDraft.same_test_closed_threshold_transfer
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestTerminalDraft.actual_same_test_proper_pairing_le_barrier
#print axioms KLSConstantImprovement.OriginalUpperRecovery6SameTestTerminalDraft.actualAppell_centered_weighted_energy_inequality_two_same_test_creation
