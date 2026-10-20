import ActualAppellCombinedTerminal

/-! Literal weighted scalar inequality at the genuine maximizer, obtained
from the actual law generator, test stationarity and prior coefficient bounds. -/
noncomputable section
open MeasureTheory InnerProductSpace Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLSBelow25
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 3
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem actualAppellCoefficient_congr_ae_any_measure
    {μ : Measure (Space n)} {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g)
    (d : ℕ) (a : Fin d → Fin n) :
    actualAppellCoefficient μ f d a = actualAppellCoefficient μ g d a := by
  have he : (fun z => ∫ x, f x ∂exponentialTilt μ z) =
      (fun z => ∫ x, g x ∂exponentialTilt μ z) := by
    funext z
    exact integral_congr_ae
      ((tilted_absolutelyContinuous μ (fun x => inner ℝ z x)).ae_eq hfg)
  unfold actualAppellCoefficient
  rw [he]

 theorem actualCovarianceAppellEnergy_congr_ae_any_measure
    {μ : Measure (Space n)} {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    actualCovarianceAppellEnergy μ f d = actualCovarianceAppellEnergy μ g d := by
  have he : actualAppellCoefficient μ f d = actualAppellCoefficient μ g d := by
    funext a
    exact actualAppellCoefficient_congr_ae_any_measure hfg d a
  unfold actualCovarianceAppellEnergy
  rw [he]

 theorem actualAppellEnergyHeatGenerator_congr_ae
    {μ : Measure (Space n)} {f g : Space n → ℝ} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    actualAppellEnergyHeatGenerator μ f d = actualAppellEnergyHeatGenerator μ g d := by
  have he : (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) f d) =
      (fun s z => actualCovarianceAppellEnergy (actualDampedTiltLaw μ z s) g d) := by
    funext s z
    apply actualCovarianceAppellEnergy_congr_ae_any_measure
    exact (tilted_absolutelyContinuous μ _).ae_eq hfg
  unfold actualAppellEnergyHeatGenerator
  rw [he]

 theorem actualAppell_weighted_energy_inequality
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : admissibleMeasure μ)
    (f : Lp ℝ 2 μ) (hunit : ‖f‖=1) {k : ℕ} (hk : 2 ≤ k) {h : ℕ → ℝ}
    (hhk : 0 < h k) (hh : ∀ r : ℕ, 1 ≤ r → r ≤ k → 0 ≤ h r)
    (hprevious : ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ g : Space n → ℝ, MemLp g 2 μ →
      actualAppellEnergy μ g r ≤ h r*(∫ x, (g x)^2 ∂μ))
    {α q : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hq : 0 ≤ q)
    (hstat : ∀ ell : Lp ℝ 2 μ,
      inner ℝ (fullClassAppellTensor (k+1) f) (fullClassAppellTensor (k+1) ell)+
        actualAppellEnergy μ f (k+1)*q/(h k)*
          inner ℝ (fullClassAppellTensor k f) (fullClassAppellTensor k ell) =
        actualAppellEnergy μ f (k+1)*(1+(actualAppellEnergy μ f k/(h k))*q)*inner ℝ f ell)
    (hmaximum : actualAppellEnergyHeatGenerator μ f (k+1)+
      actualAppellEnergy μ f (k+1)*q/(h k)*actualAppellEnergyHeatGenerator μ f k ≤ 0) :
    let X := actualAppellEnergy μ f (k+1)
    let Y := actualAppellEnergy μ f k
    let w := X*q/(h k)
    let A := 4/(1-α)-2
    w*α*X-(2*((k+1 : ℕ) : ℝ)^2-((k+1 : ℕ) : ℝ))*X-
      w*(A*(k : ℝ)^2+(A-3)*(k : ℝ))*Y-
      2*X*(1+(Y/(h k))*q)-
      2*Real.sqrt X*actualLowerConvolution h (k+1)-
      2*w*Real.sqrt Y*actualLowerConvolution h k ≤ 0 := by
  have ht := actualAppell_weighted_drift_pairing_le hμ f hunit hk hhk hh hprevious hq hstat
  have hj := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) (k+1)
    (β := 0) (by norm_num) (by norm_num)
  have hl := actualCovarianceAppellEnergy_generator_lower hμ (Lp.memLp f) k hα0 hα1
  have hw : 0 ≤ actualAppellEnergy μ f (k+1)*q/(h k) :=
    div_nonneg (mul_nonneg (actualAppellEnergy_nonneg _ _ _) hq) hhk.le
  have hm := mul_le_mul_of_nonneg_left hl hw
  change _ ≤ actualAppellEnergyHeatGenerator μ f (k+1) at hj
  change _ ≤ actualAppellEnergyHeatGenerator μ f k at hl
  norm_num only [sub_zero,div_one,zero_mul,zero_sub] at hj
  have hc : (4-2 : ℝ)-3 = -1 := by norm_num
  norm_num only [hc,show (4-2 : ℝ)=2 by norm_num] at hj
  dsimp only
  nlinarith [hj,hm,ht,hmaximum]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualAppell_weighted_energy_inequality
#print axioms KLS.DeterministicBridgeIntegration.actualAppellEnergyHeatGenerator_congr_ae
