import ActualCenteredAdjacentHeat
import ActualAppellWeightedEnergy

/-! Exact adjacent terminal cancellation against the genuine variance heat gain. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeNext
open KLS KLSBelow25 KLS.DeterministicBridgeIntegration
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem actual_adjacent_terminal_eq {n k : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (w lam : ℝ)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
        w*inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell)=lam*inner ℝ f ell) :
    (actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellCoefficient μ
        (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) (k+1))+
      w*(actualAppellCoefficient μ f k ⬝ᵥ actualAppellCoefficient μ
        (fun x => inner ℝ x (affineProjectionVector hμ.isotropic f)) k)=
      lam*actualAppellEnergy μ f 1 := by
  have hs := hstat (isotropicLinearObservable hμ.isotropic (affineProjectionVector hμ.isotropic f))
  rw [fullClassAppellTensor_linear_observable,fullClassAppellTensor_linear_observable,
    actualAppell_tensor_inner_array,actualAppell_tensor_inner_array,
    inner_isotropicLinearObservable_projection] at hs
  rw [hs,actualAppellEnergy_eq_norm_sq,
    fullClassAppellTensor_one_norm_sq hμ.logConcave hμ.isotropic]

theorem actualAppell_centered_weighted_energy_inequality {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {k : ℕ} (hk : 2 ≤ k) {h : ℕ → ℝ}
    (hhk : 0<h k) (hh : ∀ r : ℕ,1≤r → r≤k → 0≤h r)
    (hprevious : ∀ r : ℕ,1≤r → r≤k → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r≤h r*(∫ x,(g x)^2 ∂μ))
    {α q : ℝ} (hα0 : 0≤α) (hα1 : α<1) (hq : 0≤q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
        actualAppellEnergy μ f (k+1)*q/(h k)*
          inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell)=
        actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/(h k))*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f (k+1)+
      actualAppellEnergy μ f (k+1)*q/(h k)*actualAppellEnergyHeatGenerator μ f k+
      actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/(h k))*q)*
        actualAppellEnergy μ f 1≤0) :
    let X := actualAppellEnergy μ f (k+1)
    let Y := actualAppellEnergy μ f k
    let w := X*q/(h k)
    let A := 4/(1-α)-2
    w*α*X-(2*((k+1 : ℕ):ℝ)^2-((k+1 : ℕ):ℝ))*X-
      w*(A*(k:ℝ)^2+(A-3)*(k:ℝ))*Y-
      X*(1+(Y/(h k))*q)-2*Real.sqrt X*actualLowerConvolution h (k+1)-
      2*w*Real.sqrt Y*actualLowerConvolution h k≤0 := by
  let X := actualAppellEnergy μ f (k+1)
  let Y := actualAppellEnergy μ f k
  let w := X*q/(h k)
  let lam := X*(1+(Y/(h k))*q)
  have hw : 0≤w := div_nonneg (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hhk.le
  have hlam : 0≤lam := mul_nonneg (actualAppellEnergy_nonneg _ _ _)
    (by have hu := div_nonneg (actualAppellEnergy_nonneg μ f k) hhk.le
        linarith [mul_nonneg hu hq])
  have ht := actual_adjacent_terminal_eq hμ f w lam hstat
  have hb : actualAppellEnergy μ f 1≤1 := by
    rw [actualAppellEnergy_eq_norm_sq]
    simpa only [hunit,one_pow] using fullClassAppellTensor_one_norm_sq_le hμ.logConcave hμ.isotropic f
  have hlamb := mul_le_of_le_one_right hlam hb
  have hpj := actualAppellProperRemainder_pairing_le hμ f hunit (show k+1≤k+1 from le_rfl) hh hprevious
  have hpk := actualAppellProperRemainder_pairing_le hμ f hunit (show k≤k+1 by omega) hh hprevious
  have hpk' := mul_le_mul_of_nonneg_left hpk hw
  have hsplit :
      (actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellLowerDriftTensor μ f (k+1))+
        w*(actualAppellCoefficient μ f k ⬝ᵥ actualAppellLowerDriftTensor μ f k) =
      lam*actualAppellEnergy μ f 1+
        (actualAppellCoefficient μ f (k+1) ⬝ᵥ actualAppellProperRemainder μ f (k+1))+
        w*(actualAppellCoefficient μ f k ⬝ᵥ actualAppellProperRemainder μ f k) := by
    rw [actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f (by omega),
      actualAppellLowerDriftTensor_terminal_split hμ.logConcave hμ.isotropic f hk,
      dotProduct_add,dotProduct_add]
    linarith [ht]
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) (k+1)
    (β:=0) (by norm_num) (by norm_num)
  have hl := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) k hα0 hα1
  have hm := mul_le_mul_of_nonneg_left hl hw
  change _≤actualAppellEnergyHeatGenerator μ f (k+1) at hj
  norm_num only [sub_zero,div_one,zero_mul,zero_sub] at hj
  norm_num only [show (4-2 : ℝ)-3 = -1 by norm_num,show (4-2 : ℝ)=2 by norm_num] at hj
  change _≤actualAppellEnergyHeatGenerator μ f k at hl
  change actualAppellEnergyHeatGenerator μ f (k+1)+w*actualAppellEnergyHeatGenerator μ f k+
    lam*actualAppellEnergy μ f 1≤0 at hmaximum
  dsimp only
  change w*α*X-(2*((k+1 : ℕ):ℝ)^2-((k+1 : ℕ):ℝ))*X-
    w*((4/(1-α)-2)*(k:ℝ)^2+((4/(1-α)-2)-3)*(k:ℝ))*Y-
    lam-2*Real.sqrt X*actualLowerConvolution h (k+1)-
    2*w*Real.sqrt Y*actualLowerConvolution h k≤0
  nlinarith [hj,hm,hsplit,hpj,hpk',hlamb,hmaximum]

end KLS.DeterministicBridgeNext
#print axioms KLS.DeterministicBridgeNext.actual_adjacent_terminal_eq
#print axioms KLS.DeterministicBridgeNext.actualAppell_centered_weighted_energy_inequality
