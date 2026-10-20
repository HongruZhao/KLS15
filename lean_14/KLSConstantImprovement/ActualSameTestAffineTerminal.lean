import KLSConstantImprovement.ActualSameTestAffineCreation
import KLSConstantImprovement.ActualSameTestCreationTerminal

/-! Pay the affine saving and the matching original coordinate term together.
The lower threshold is explicit. The upper energy bound is supplied by the
already accepted original-law 23849 cubic cap. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLSConstantImprovement.ActualSameTestAffineTerminal
open KLS KLSBelow25 KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration
open ActualSameTestAffineCreation SameTestAffineTerminalScalar
open OriginalUpperRecovery6SameTestCovarianceDraft OriginalUpperRecovery6SameTestTerminalDraft
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

def affineClosedRatio (M Y : ℝ) : ℝ :=
  (Y+Real.sqrt ((4*affineEffectiveC-Y)*Y*(72*affineEffectiveC/M-1)))/(2*affineEffectiveC)

def affineCreationRatio (M Y : ℝ) : ℝ :=
  min (affineClosedRatio M Y) (Real.sqrt (48*Y)/Real.sqrt M)

theorem affineCreationRatio_le_closed (M Y : ℝ) :
    affineCreationRatio M Y≤affineClosedRatio M Y := min_le_left _ _

theorem affineCreationRatio_le_cap (M Y : ℝ) :
    affineCreationRatio M Y≤Real.sqrt (48*Y)/Real.sqrt M := min_le_right _ _

theorem affine_doubleRatio_eq_closed (M Y : ℝ) :
    doubleRatio affineEffectiveC M Y=2*affineClosedRatio M Y := by
  have hc : 0<affineEffectiveC := by norm_num [affineEffectiveC]
  have hid : radical affineEffectiveC M Y = (1/affineEffectiveC)^2*
      ((4*affineEffectiveC-Y)*Y*(72*affineEffectiveC/M-1)) := by
    unfold radical
    ring
  unfold doubleRatio
  rw [hid,Real.sqrt_mul (sq_nonneg (1/affineEffectiveC)),
    Real.sqrt_sq (one_div_nonneg.mpr hc.le)]
  unfold affineClosedRatio
  field_simp [hc.ne']
  <;> ring

theorem affine_doubleRatio_threshold {M X Y : ℝ}
    (hM : 0<M) (hMX : M≤X) (hY0 : 0≤Y) (hY8 : Y≤8) :
    doubleRatio affineEffectiveC X Y≤doubleRatio affineEffectiveC M Y := by
  have hc : 0<affineEffectiveC := by norm_num [affineEffectiveC]
  have hD : 0≤(4*affineEffectiveC-Y)*Y :=
    mul_nonneg (by norm_num [affineEffectiveC] at *; linarith) hY0
  have hd : 72*affineEffectiveC/X≤72*affineEffectiveC/M :=
    div_le_div_of_nonneg_left (by positivity) hM hMX
  have hr : radical affineEffectiveC X Y≤radical affineEffectiveC M Y := by
    unfold radical
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hd 1) hD) (sq_nonneg _)
  unfold doubleRatio
  exact add_le_add (le_refl _) (Real.sqrt_le_sqrt hr)

theorem actual_affine_coordinate_and_pairing_le_barrier {n : ℕ} {μ : Measure (Space n)}
    (hn : 1≤n) (hμ : admissibleMeasure μ) (f : Lp ℝ 2 μ) (hunit : ‖f‖=1)
    {M lam : ℝ} (hM : 360≤M) (hMX : M≤actualAppellEnergy μ f 3)
    (hlam : actualAppellEnergy μ f 3≤lam) :
    lam*actualAppellEnergy μ f 1+
      2*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)≤
      lam+2*actualAppellEnergy μ f 3*affineCreationRatio M (actualAppellEnergy μ f 2) := by
  letI : IsProbabilityMeasure μ := hμ.isProb
  have hMp : 0<M := by linarith
  have hX0 : 360≤actualAppellEnergy μ f 3 := hM.trans hMX
  have hXp : 0<actualAppellEnergy μ f 3 := by linarith
  have hXcap := actual_appell_energy_three_joint_creation23849_le_norm_sq hμ f
  rw [hunit,one_pow,mul_one] at hXcap
  have hX1 : actualAppellEnergy μ f 3≤859 := by
    norm_num [OptimizedJointCreationSeed23849.B] at hXcap
    linarith
  have hr0 := actualAppellEnergy_nonneg μ f 1
  have hr1 := actual_unit_first_energy_le_one hμ f hunit
  have hY0 := actualAppellEnergy_nonneg μ f 2
  have hY8 := actualAppellEnergy_two_le_eight_norm_sq hμ f
  rw [hunit,one_pow,mul_one] at hY8
  have hj := actual_creation_same_test_affine_upper_unit hn hμ f hunit hXp
  have hc := same_terminal_coordinate_compensation (C := affineBaseC) (by norm_num [affineBaseC])
    hr0 hr1 hX0 hX1 hY0 hY8 hlam
  rw [←affineEffectiveC_eq] at hc
  have ht := mul_le_mul_of_nonneg_left
    (affine_doubleRatio_threshold hMp hMX hY0 hY8) hXp.le
  simp only [affine_doubleRatio_eq_closed] at hc ht
  have hnew : lam*actualAppellEnergy μ f 1+2*properThirdPairing μ f≤
      lam+2*actualAppellEnergy μ f 3*affineClosedRatio M (actualAppellEnergy μ f 2) := by
    nlinarith [hj,hc,ht]
  have hcap := (actual_same_test_proper_pairing_le_barrier hn hμ f hunit hMp hMX).trans
    (mul_le_mul_of_nonneg_left (sameTestCreationRatio_le_cap M (actualAppellEnergy μ f 2)) hXp.le)
  have hlr := mul_le_of_le_one_right (hXp.le.trans hlam) hr1
  unfold affineCreationRatio
  by_cases hb : affineClosedRatio M (actualAppellEnergy μ f 2)≤
      Real.sqrt (48*actualAppellEnergy μ f 2)/Real.sqrt M
  · rw [min_eq_left hb]
    exact hnew
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hb))]
    nlinarith [hcap,hlr]

theorem actualAppell_centered_weighted_energy_inequality_two_affine_creation {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hn : 1 ≤ n) (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {h : ℕ → ℝ}
    (hhk : 0<h 2) (hh : ∀ r : ℕ,1≤r → r≤2 → 0≤h r)
    (hprevious : ∀ r : ℕ,1≤r → r≤2 → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r≤h r*(∫ x,(g x)^2 ∂μ))
    {M : ℝ} (hM : 360 ≤ M) (hMX : M≤actualAppellEnergy μ f 3)
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
      X*(1+(Y/(h 2))*q)-2*X*affineCreationRatio M Y-
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
  have hlamX : X≤lam := by
    have hX := actualAppellEnergy_nonneg μ f 3
    have hu : 0≤Y/(h 2) := div_nonneg (actualAppellEnergy_nonneg μ f 2) hhk.le
    have hqY := mul_nonneg hu hq
    dsimp only [lam]
    nlinarith [mul_nonneg hX hqY]
  have hpaid := actual_affine_coordinate_and_pairing_le_barrier hn hμ f hunit hM hMX hlamX
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
    lam-2*X*affineCreationRatio M Y-
    2*w*Real.sqrt Y*actualLowerConvolution h 2≤0
  nlinarith [hj,hm,hsplit,hpaid,hpk',hmaximum]


end KLSConstantImprovement.ActualSameTestAffineTerminal
#print axioms KLSConstantImprovement.ActualSameTestAffineTerminal.affine_doubleRatio_eq_closed
#print axioms KLSConstantImprovement.ActualSameTestAffineTerminal.affine_doubleRatio_threshold
#print axioms KLSConstantImprovement.ActualSameTestAffineTerminal.actual_affine_coordinate_and_pairing_le_barrier
#print axioms KLSConstantImprovement.ActualSameTestAffineTerminal.actualAppell_centered_weighted_energy_inequality_two_affine_creation
