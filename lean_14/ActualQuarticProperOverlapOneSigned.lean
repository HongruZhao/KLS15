import ActualQuarticProperOverlapOne
import ActualFourthCumulantSpectralDefect
import ActualProperCubicCreation

/-! The mixed quartic one-overlap retains its signed proper cubic pairing.
Centering the actual fourth-cumulant flat map at 2I has norm at most 4. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise KLSBelow25.CubicCreation
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem actualFourthCumulantFlat_centered_square_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (H : Matrix (Fin n) (Fin n) ℝ) :
    matrixFrobeniusSq (fun i j=>actualFourthCumulantFlat μ H i j-2*H i j)≤
      16*matrixFrobeniusSq H := by
  have he : matrixFrobeniusSq (fun i j=>actualFourthCumulantFlat μ H i j-2*H i j)=
      matrixFrobeniusSq (actualFourthCumulantFlat μ H)-
      4*(∑ i,∑ j,H i j*actualFourthCumulantFlat μ H i j)+4*matrixFrobeniusSq H := by
    unfold matrixFrobeniusSq
    simp only [←Finset.sum_add_distrib,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hh := actual_fourth_cumulant_flat_square_le_signed_pairing hμ H
  linarith

 theorem actualQuarticProperSymmetricSlice_pairing_eq_proper_three
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
      actualQuarticProperSymmetricSlice μ f a i j)=
      (1/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3) := by
  let : IsProbabilityMeasure μ := hμ.isProb
  have hsym := symmetric_pairing (actualCubicSlotArray μ f) (actualCubicNextArray μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
  have hs : tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
      actualQuarticProperSymmetricSlice μ f a i j)=
      (1/2:ℝ)*tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
        (actualCubicSlotArray μ f a i j+actualCubicSlotArray μ f a j i)) := by
    rw [←tripleSum_smul]
    congr 1
    funext a i j
    unfold actualQuarticProperSymmetricSlice
    ring
  have hc : (actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)=
      (3/2:ℝ)*tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
        symPart (actualCubicSlotArray μ f) a i j) := by
    simp only [dotProduct,sum_fin_three_coordinates,actualAppellProperRemainder_three_creation hμ hf]
    rw [←tripleSum_smul]
    change tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
      creation (actualThirdCubicArray μ) (fun l m=>actualAppellCoefficient μ f 2 ![l,m]) a i j)=_
    congr 1
    funext a i j
    unfold creation actualThirdCubicArray actualCubicSlotArray symPart
    ring
  rw [hs,hsym,hc]
  ring

 theorem actualQuarticProperOverlapOne_signed_sq_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    (actualQuarticProperOverlapOne μ f-
      (2/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3))^2≤
      96*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2 := by
  let W : Array3 (Fin n) := fun a i j=>
    actualFourthCumulantFlat μ (actualQuarticProperSymmetricSlice μ f a) i j-
      2*actualQuarticProperSymmetricSlice μ f a i j
  have hW : square W≤96*actualAppellEnergy μ f 2 := by
    have hh := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin n)))=>
      actualFourthCumulantFlat_centered_square_le hμ (actualQuarticProperSymmetricSlice μ f a))
    simp only [matrixFrobeniusSq,←Finset.mul_sum] at hh
    change square W≤16*(∑ a,matrixFrobeniusSq (actualQuarticProperSymmetricSlice μ f a)) at hh
    have hs := actualQuarticProperSymmetricSlice_square_le hμ hf
    linarith
  have he : actualQuarticProperOverlapOne μ f-
      (2/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)=
      tripleSum (fun a i j=>actualCubicNextArray μ f a i j*W a i j) := by
    rw [actualQuarticProperOverlapOne_eq_matrix_pairing hμ hf,
      show (2/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)=
        2*tripleSum (fun a i j=>actualCubicNextArray μ f a i j*
          actualQuarticProperSymmetricSlice μ f a i j) from by
        rw [actualQuarticProperSymmetricSlice_pairing_eq_proper_three hμ hf];ring]
    simp only [←tripleSum_smul,←tripleSum_neg,←tripleSum_add,sub_eq_add_neg]
    congr 1
    funext a i j
    dsimp [W]
    ring
  rw [he]
  have hc := triple_pairing_sq_le (actualCubicNextArray μ f) W
  rw [actualCubicNextArray_square] at hc
  have hb := mul_le_mul_of_nonneg_left hW (actualAppellEnergy_nonneg μ f 3)
  exact hc.trans (by nlinarith)

 theorem actualQuarticProperOverlapOne_signed_le {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n→ℝ} (hf : MemLp f 2 μ) :
    actualQuarticProperOverlapOne μ f-
      (2/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)≤
      4*Real.sqrt (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2) := by
  have hs := actualQuarticProperOverlapOne_signed_sq_le hμ hf
  have hr := Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6)
    (actualAppellEnergy_nonneg μ f 3)) (actualAppellEnergy_nonneg μ f 2))
  have hp := Real.sqrt_nonneg (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2)
  nlinarith [sq_nonneg (actualQuarticProperOverlapOne μ f-
    (2/3:ℝ)*(actualAppellCoefficient μ f 3 ⬝ᵥ actualAppellProperRemainder μ f 3)+
    4*Real.sqrt (6*actualAppellEnergy μ f 3*actualAppellEnergy μ f 2))]

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualFourthCumulantFlat_centered_square_le
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperSymmetricSlice_pairing_eq_proper_three
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperOverlapOne_signed_sq_le
#print axioms KLS.DeterministicBridgeIntegration.actualQuarticProperOverlapOne_signed_le
