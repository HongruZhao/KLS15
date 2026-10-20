import ActualCubicJointProperNoise

/-! Both parameter branches of the actual rank-two signed covariance estimate. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLSConstantImprovement.SignedQuadraticReservedNoise
open KLS KLS.DeterministicBridgeNext KLS.DeterministicBridgeIntegration KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

theorem cross_le_square (U : Array3 ι) : cross U ≤ square U := by
  have hs : 0 ≤ tripleSum (fun i j k => (U i j k-U i k j)^2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _
  have he : tripleSum (fun i j k => (U i j k-U i k j)^2)=
      square U+square (fun i j k => U i k j)-2*cross U := by
    unfold square cross
    simp only [sub_eq_add_neg,←tripleSum_neg,←tripleSum_add,←tripleSum_smul]
    congr 1
    funext i j k
    ring
  rw [he,permuted_square U] at hs
  linarith

def quadraticNoiseLoss (β g t : ℝ) : ℝ :=
  max (16*g^2/(1-β)-12-4*t) (64*g^2/(3*(1-β))-20-8*t)

theorem joint_lower_unrestricted {β g t E : ℝ} (hβ : β < 1) (ht : 0≤t)
    (hpay : 3+t≤4*g^2/(1-β)) (hE : 0≤E)
    (U W : Array3 ι) (hU : ∀ i j k, U i j k=U j i k)
    (hW12 : ∀ i j k, W i j k=W j i k)
    (hW23 : ∀ i j k, W i j k=W i k j)
    (hQ : square U≤8*E) (hR : cross U≤4*E) :
    β*square W-quadraticNoiseLoss β g t*E ≤
      noise U W-2*(g-1)*tripleSum (fun i j k => W i j k*symPart U i j k)+t*square U := by
  by_cases hqc : 0≤2+t-4*g^2/(3*(1-β))
  · have hh := joint_completion (g:=g) (t:=t) hβ U W hU hW12 hW23
    have hq := mul_le_mul_of_nonneg_left (cross_le_square U) hqc
    have hc : 3+t-4*g^2/(1-β)≤0 := by linarith
    have hr := mul_le_mul_of_nonpos_left hR hc
    have hid : (2+t-4*g^2/(3*(1-β)))*cross U+
        (1-8*g^2/(3*(1-β)))*cross U =
        (3+t-4*g^2/(1-β))*cross U := by field_simp; ring
    have hcE : (3+t-4*g^2/(1-β))*(4*E)=-(16*g^2/(1-β)-12-4*t)*E := by ring
    have htgt : β*square W-(16*g^2/(1-β)-12-4*t)*E ≤
        noise U W-2*(g-1)*tripleSum (fun i j k => W i j k*symPart U i j k)+t*square U := by
      linarith only [hh,hq,hr,hid,hcE]
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hE) _).trans htgt
  · have hrc : 1-8*g^2/(3*(1-β))≤0 := by
      have hid : 8*g^2/(3*(1-β))=(2/3:ℝ)*(4*g^2/(1-β)) := by field_simp; ring
      rw [hid]
      linarith
    have hh := joint_lower_of_bounds hβ (le_of_lt (lt_of_not_ge hqc)) hrc U W hU hW12 hW23 hQ hR
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_right _ _) hE) _).trans hh

variable {n : ℕ}

theorem actual_noise_two_signed_reserved_lower
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) {β g t : ℝ}
    (hβ : β<1) (ht : 0≤t) (hpay : 3+t≤4*g^2/(1-β)) :
    β*actualAppellEnergy μ f 3-quadraticNoiseLoss β g t*actualAppellEnergy μ f 2 ≤
    (∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 2)
      (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (fun a => actualAppellCoefficient μ f 3 (Fin.cons i a)))-
      (4*(g-1)/3)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
      t*actualCanonicalContractionSquare μ f 2 1 := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hh := joint_lower_unrestricted hβ ht hpay (actualAppellEnergy_nonneg μ f 2)
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

end KLSConstantImprovement.SignedQuadraticReservedNoise
#print axioms KLSConstantImprovement.SignedQuadraticReservedNoise.cross_le_square
#print axioms KLSConstantImprovement.SignedQuadraticReservedNoise.joint_lower_unrestricted
#print axioms KLSConstantImprovement.SignedQuadraticReservedNoise.actual_noise_two_signed_reserved_lower
