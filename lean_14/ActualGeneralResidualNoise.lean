import ActualGeneralPairNoise
import ActualPairTensorCreationRecurrence
import GeneralResidualCoefficientAlgebra
import ActualSymmetricCubicNoise

/-! The all-rank covariance-noise refinement for every original admissible
law and L2 test. Creation/annihilation and all pair-domain identities are
proved internally; no tensor contraction or generator premise remains. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext
open KLSBelow25.PairTensor KLSBelow25.PairProjection
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem actualAppell_noiseCorrection_lower_general_residual
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (d : ℕ) (hd : 3≤d)
    {β : ℝ} (hβ0 : 0≤β) (hβhi : β≤((d : ℝ)-1)/((d : ℝ)+1)) :
    β*actualAppellEnergy μ f (d+1)-
      (leadingNoiseCoefficient (d : ℝ)/(1-β)-positiveNoiseCoefficient (d : ℝ))*
        actualAppellEnergy μ f d≤
      ∑ i : Fin n,KLS.TensorEnergy.energyNoiseCorrection (actualAppellCoefficient μ f d)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f (d+1) (Fin.cons i a)) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hd
  have hdr : d=r+3 := by omega
  rw [hdr] at hβhi ⊢
  have hT := actualAppellCoefficient_pair_symmetric (d:=r+3) hμ.logConcave hf
  have hW := actualAppellCoefficient_pair_symmetric (d:=r+4) hμ.logConcave hf
  have hs := actual_pair_disjoint_le hμ (actualAppellCoefficient μ f (r+3)) hT
  have hb : β≤((r : ℝ)+2)/((r : ℝ)+4) := by
    convert hβhi using 1; push_cast; ring
  have hh := actual_general_pair_noise_lower_of_disjoint hμ
    (actualAppellCoefficient μ f (r+3)) hT
    (actualAppellCoefficient μ f (r+4)) hW hβ0 hb hs
  simpa only [square,actualAppellEnergy,Nat.cast_add,Nat.cast_ofNat] using hh

theorem actualCovarianceAppellEnergy_generator_lower_general_residual
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) (d : ℕ) (hd : 3≤d)
    {β : ℝ} (hβ0 : 0≤β) (hβhi : β≤((d : ℝ)-1)/((d : ℝ)+1)) :
    β*actualAppellEnergy μ f (d+1)-generalResidualGeneratorLoss β d*actualAppellEnergy μ f d-
      2*(actualAppellCoefficient μ f d ⬝ᵥ actualAppellLowerDriftTensor μ f d)≤
      actualAppellEnergyHeatGenerator μ f d := by
  have hdr : (3 : ℝ)≤d := by exact_mod_cast hd
  have hβ1 : β<1 := hβhi.trans_lt ((div_lt_one (by linarith : 0<(d : ℝ)+1)).mpr (by linarith))
  have hh := actualAppell_noiseCorrection_lower_general_residual hμ hf d hd hβ0 hβhi
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf d]
  rw [generalResidualGeneratorLoss_eq d hd hβ1]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceAppellEnergy_generator_lower_general_residual
