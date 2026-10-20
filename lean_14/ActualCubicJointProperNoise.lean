import CubicJointProperNoiseAlgebra
import ActualQuarticProperOverlapOneSigned
import ActualPairAppellAffineQ
import PairTensorDisjointFrame
import ActualCoupledAppellDrift

/-! The rank-two covariance noise and the literal signed rank-three proper
drift share the same cubic next tensor. Their retained canonical (2,1)
square is exactly the slot square Q. The full preceding joint budget is
not reduced in any assertion of this file. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

 theorem actualCanonicalContractionSquare_two_one_eq_slot_square
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualCanonicalContractionSquare μ f 2 1 = square (actualCubicSlotArray μ f) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hh := actual_pair_kernel_square_eq_canonical (r:=0) hμ hf
    (KLSBelow25.PairTensor.incidentPair (0 : Fin 2))
  rw [KLSBelow25.PairTensor.kernel_incident_zero_eq_cons
    (actualThirdCubicArray μ) (actualThirdCumulant_swap_first μ)
    (actualAppellCoefficient μ f 2) (actualAppellCoefficient_pair_symmetric hμ.logConcave hf)] at hh
  have he (i j k : Fin n) :
      KLSBelow25.PairTensor.kernelInFrame (actualThirdCubicArray μ)
        (actualAppellCoefficient μ f 2) (KLSBelow25.PairTensor.consFrame 1) ![i,j,k] =
      actualCubicSlotArray μ f i j k := by
    unfold KLSBelow25.PairTensor.kernelInFrame actualCubicSlotArray actualThirdCubicArray
    simp only [KLSBelow25.PairTensor.consFrame_left_zero,KLSBelow25.PairTensor.consFrame_left_one,
      KLSBelow25.PairTensor.consFrame_right,Matrix.cons_val_zero,Matrix.cons_val_one]
    apply Finset.sum_congr rfl
    intro m _
    congr 1
  change (∑ a : Fin 3 → Fin n,
    (KLSBelow25.PairTensor.kernelInFrame (actualThirdCubicArray μ)
      (actualAppellCoefficient μ f 2) (KLSBelow25.PairTensor.consFrame 1) a)^2) =
    actualCanonicalContractionSquare μ f 2 1 at hh
  rw [sum_fin_three_coordinates] at hh
  simpa only [he,square,tripleSum] using hh.symm

 theorem actualProperRemainder_three_pairing_eq_symmetric_noise_pairing
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3 =
      (3/2 : ℝ)*tripleSum (fun i j k => actualCubicNextArray μ f i j k*
        symPart (actualCubicSlotArray μ f) i j k) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hs := actualQuarticProperSymmetricSlice_pairing_eq_proper_three hμ hf
  have hp := symmetric_pairing (actualCubicSlotArray μ f) (actualCubicNextArray μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
  have he : tripleSum (fun i j k => actualCubicNextArray μ f i j k*
      actualQuarticProperSymmetricSlice μ f i j k) =
      (1/2 : ℝ)*tripleSum (fun i j k => actualCubicNextArray μ f i j k*
        (actualCubicSlotArray μ f i j k+actualCubicSlotArray μ f i k j)) := by
    rw [←tripleSum_smul]
    congr 1
    funext i j k
    unfold actualQuarticProperSymmetricSlice
    ring
  rw [he,hp] at hs
  linarith

 theorem actual_noise_two_joint_proper_three_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K β θ t : ℝ}
    (_hK : 0 < K) (hβ : β < 1)
    (hQcoeff : 2+t-4*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0)
    (hRcoeff : 1-8*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0) :
    β*actualAppellEnergy μ f 3-
      (64*(1+θ/(6*K))^2/(3*(1-β))-20-8*t)*actualAppellEnergy μ f 2 ≤
      (∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 2)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f 3 (Fin.cons i a)))-
      (2*θ/(9*K))*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      t*actualCanonicalContractionSquare μ f 2 1 := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hh := joint_lower_of_bounds (g:=1+θ/(6*K)) (t:=t) hβ hQcoeff hRcoeff
    (actualCubicSlotArray μ f) (actualCubicNextArray μ f)
    (actualCubicSlotArray_first_symmetry μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
    (actualCubicSlotArray_square_le_eight hμ f) (actualCubicSlotArray_cross_le_four hμ hf)
  rw [actualCubicNextArray_square,actualCubic_noise_eq hμ.logConcave hf] at hh
  rw [actualCanonicalContractionSquare_two_one_eq_slot_square hμ hf,
    actualProperRemainder_three_pairing_eq_symmetric_noise_pairing hμ hf]
  convert hh using 1
  ring

 theorem actual_cubic_canonical_budget_credit
    {μ : Measure (Space n)} (f : Space n → ℝ) {K : ℝ} (hK : 0 < K)
    (s lmb : ℝ) :
    (lmb*K/s)*(coupledAppellQ μ f K 2 2)^2 =
      (lmb/(K*s))*KLSBelow25.CoupledEnergy.factorialWeight K 2*
        actualCanonicalContractionSquare μ f 2 1 := by
  rw [coupledAppellQ_sq f hK,coupledAppellScale_sq hK]
  norm_num only [Nat.factorial,Nat.cast_ofNat,Nat.reduceSub]
  unfold KLSBelow25.CoupledEnergy.factorialWeight
  norm_num only [Nat.factorial,Nat.cast_ofNat]
  field_simp

 theorem actual_weighted_noise_two_joint_proper_three_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {K β θ s lmb : ℝ}
    (hK : 0 < K) (hβ : β < 1)
    (hQcoeff : 2+lmb/(K*s)-4*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0)
    (hRcoeff : 1-8*(1+θ/(6*K))^2/(3*(1-β)) ≤ 0) :
    KLSBelow25.CoupledEnergy.factorialWeight K 2*
      (β*actualAppellEnergy μ f 3-
        (64*(1+θ/(6*K))^2/(3*(1-β))-20-8*lmb/(K*s))*actualAppellEnergy μ f 2) ≤
      KLSBelow25.CoupledEnergy.factorialWeight K 2*
        (∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 2)
          (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
          (fun a => actualAppellCoefficient μ f 3 (Fin.cons i a)))-
      2*θ*KLSBelow25.CoupledEnergy.factorialWeight K 3*
        (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      (lmb*K/s)*(coupledAppellQ μ f K 2 2)^2 := by
  have hh := mul_le_mul_of_nonneg_left
    (actual_noise_two_joint_proper_three_lower hμ hf hK hβ hQcoeff hRcoeff)
    (KLSBelow25.CoupledEnergy.factorialWeight_nonneg hK 2)
  rw [actual_cubic_canonical_budget_credit f hK s lmb]
  have hw := KLSBelow25.CoupledEnergy.factorialWeight_step hK 2
  norm_num only [Nat.cast_ofNat] at hw
  convert hh using 1 <;> simp only [hw] <;> field_simp [ne_of_gt hK]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCanonicalContractionSquare_two_one_eq_slot_square
#print axioms KLS.DeterministicBridgeIntegration.actualProperRemainder_three_pairing_eq_symmetric_noise_pairing
#print axioms KLS.DeterministicBridgeIntegration.actual_weighted_noise_two_joint_proper_three_lower
