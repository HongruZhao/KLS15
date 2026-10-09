import CubicSymmetricNoiseAlgebra
import ActualThirdCumulantSymmetry
import FinTwoCoordinateEnumeration
import ActualAppellEnergyEvolution
import ActualEnergyQuotientMaximum

/-! Full symmetry of the genuine third Appell coefficient improves the
rank-two covariance noise completion. -/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace KLS.DeterministicBridgeIntegration
open KLS KLS.DeterministicBridgeNext KLS.TensorEnergy
open KLSBelow25.CubicSymmetricNoise
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def actualCubicSlotArray (μ : Measure (Space n)) (f : Space n → ℝ) : Array3 (Fin n) :=
  fun i j k => ∑ l, thirdCumulantMatrix μ (MomentMap.coordinateVector i) j l *
    actualAppellCoefficient μ f 2 ![l,k]

def actualCubicNextArray (μ : Measure (Space n)) (f : Space n → ℝ) : Array3 (Fin n) :=
  fun i j k => actualAppellCoefficient μ f 3 ![i,j,k]

theorem actualCubicSlotArray_first_symmetry (μ : Measure (Space n)) (f : Space n → ℝ) :
    ∀ i j k, actualCubicSlotArray μ f i j k=actualCubicSlotArray μ f j i k := by
  intro i j k
  unfold actualCubicSlotArray
  simp_rw [actualThirdCumulant_swap_first μ i j]

 theorem actualAppell_two_swap {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) (j k : Fin n) :
    actualAppellCoefficient μ f 2 ![j,k]=actualAppellCoefficient μ f 2 ![k,j] := by
  have hh := actualAppellCoefficient_symmetric hLC hf (0 : Fin 2) 1 ![j,k]
  have he : (![j,k] ∘ Equiv.swap (0 : Fin 2) 1)=![k,j] := by
    ext a; fin_cases a <;> simp
  rw [he] at hh
  exact hh.symm

 theorem actualCubicNextArray_first_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k, actualCubicNextArray μ f i j k=actualCubicNextArray μ f j i k := by
  intro i j k
  have hh := actualAppellCoefficient_symmetric hLC hf (0 : Fin 3) 1 ![i,j,k]
  have he : (![i,j,k] ∘ Equiv.swap (0 : Fin 3) 1)=![j,i,k] := by
    ext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [he] at hh
  exact hh.symm

 theorem actualCubicNextArray_last_symmetry {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    ∀ i j k, actualCubicNextArray μ f i j k=actualCubicNextArray μ f i k j := by
  intro i j k
  have hh := actualAppellCoefficient_symmetric hLC hf (1 : Fin 3) 2 ![i,j,k]
  have he : (![i,j,k] ∘ Equiv.swap (1 : Fin 3) 2)=![i,k,j] := by
    ext a; fin_cases a <;> simp [Equiv.swap_apply_def]
  rw [he] at hh
  exact hh.symm

 theorem actualCubicSlotArray_slot_zero (μ : Measure (Space n)) (f : Space n → ℝ)
    (i j k : Fin n) :
    coordinateSlot (0 : Fin 2) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (actualAppellCoefficient μ f 2) ![j,k]=actualCubicSlotArray μ f i j k := by
  exact coordinateSlot_zero_pair _ _ _ _

 theorem actualCubicSlotArray_slot_one {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    (i j k : Fin n) :
    coordinateSlot (1 : Fin 2) (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
      (actualAppellCoefficient μ f 2) ![j,k]=actualCubicSlotArray μ f i k j := by
  rw [coordinateSlot_one_pair]
  unfold actualCubicSlotArray
  exact Finset.sum_congr rfl fun l _ => by rw [actualAppell_two_swap hLC hf j l]

 theorem actualCubicSlotArray_square_le_eight {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) (f : Space n → ℝ) :
    square (actualCubicSlotArray μ f)≤8*actualAppellEnergy μ f 2 := by
  have hh := thirdCumulant_tensor_single_slot_le_eight hμ (0 : Fin 2)
    (actualAppellCoefficient μ f 2)
  simp only [←coordinateSlot_eq_tensorSlot,dotProduct,sum_fin_two_coordinates,
    actualCubicSlotArray_slot_zero,←pow_two] at hh
  simpa only [square,tripleSum,actualAppellEnergy,sum_fin_two_coordinates] using hh

 theorem actualCubicSlotArray_cross_le_four {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    cross (actualCubicSlotArray μ f)≤4*actualAppellEnergy μ f 2 := by
  have : IsProbabilityMeasure μ := hμ.isProb
  have hh := thirdCumulant_distinct_slot_pairing_le_four hμ
    (actualAppellCoefficient_symmetric hμ.logConcave hf) (s:=(0 : Fin 2)) (t:=1)
    (by decide)
  simp only [sum_fin_two_coordinates,actualCubicSlotArray_slot_zero,
    actualCubicSlotArray_slot_one hμ.logConcave hf] at hh
  simpa only [cross,tripleSum,actualAppellEnergy,sum_fin_two_coordinates] using hh

 theorem actualCubicNextArray_square (μ : Measure (Space n)) (f : Space n → ℝ) :
    square (actualCubicNextArray μ f)=actualAppellEnergy μ f 3 := by
  simp only [square,tripleSum,actualCubicNextArray,actualAppellEnergy,
    sum_fin_three_coordinates]

 theorem actualCubic_noise_eq {μ : Measure (Space n)} [IsProbabilityMeasure μ]
    (hLC : measureLogConcave μ) {f : Space n → ℝ} (hf : MemLp f 2 μ) :
    noise (actualCubicSlotArray μ f) (actualCubicNextArray μ f)=
      ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 2)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f 3 (Fin.cons i a)) := by
  have hsum (H : Matrix (Fin n) (Fin n) ℝ) (T : (Fin 2 → Fin n) → ℝ) :
      tensorSlotSum H *ᵥ T=coordinateSlot (0 : Fin 2) H T+coordinateSlot 1 H T := by
    simp only [tensorSlotSum,Fin.sum_univ_two,Matrix.add_mulVec,
      coordinateSlot_eq_tensorSlot]
  unfold noise tripleSum energyNoiseCorrection
  simp only [hsum,dotProduct,Fin.sum_univ_two,sum_fin_two_coordinates,
    ←coordinateSlot_eq_tensorSlot,Pi.add_apply,actualCubicSlotArray_slot_zero,
    actualCubicSlotArray_slot_one hLC hf,←pow_two]
  apply Finset.sum_congr rfl
  intro i _
  simp only [←Finset.sum_add_distrib,←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he : Fin.cons i ![j,k]=![i,j,k] := by ext a; fin_cases a <;> rfl
  simp only [he,actualCubicNextArray]
  ring

 theorem actualAppell_noiseCorrection_lower_two_symmetric {μ : Measure (Space n)}
    (hμ : admissibleMeasure μ) {f : Space n → ℝ} (hf : MemLp f 2 μ)
    {β : ℝ} (hβ0 : (1 : ℝ)/3≤β) (hβ1 : β<1) :
    β*actualAppellEnergy μ f 3-(64/(3*(1-β))-20)*actualAppellEnergy μ f 2 ≤
      ∑ i : Fin n, energyNoiseCorrection (actualAppellCoefficient μ f 2)
        (thirdCumulantMatrix μ (MomentMap.coordinateVector i))
        (fun a => actualAppellCoefficient μ f 3 (Fin.cons i a)) := by
  have : IsProbabilityMeasure μ := hμ.isProb
  have hh := lower_of_bounds hβ0 hβ1 (actualCubicSlotArray μ f) (actualCubicNextArray μ f)
    (actualCubicSlotArray_first_symmetry μ f)
    (actualCubicNextArray_first_symmetry hμ.logConcave hf)
    (actualCubicNextArray_last_symmetry hμ.logConcave hf)
    (actualCubicSlotArray_square_le_eight hμ f) (actualCubicSlotArray_cross_le_four hμ hf)
  rwa [actualCubicNextArray_square,actualCubic_noise_eq hμ.logConcave hf] at hh

 theorem actualCovarianceAppellEnergy_generator_lower_two_symmetric
    {μ : Measure (Space n)} (hμ : admissibleMeasure μ)
    {f : Space n → ℝ} (hf : MemLp f 2 μ) {β : ℝ}
    (hβ0 : (1 : ℝ)/3≤β) (hβ1 : β<1) :
    β*actualAppellEnergy μ f 3-(64/(3*(1-β))-18)*actualAppellEnergy μ f 2-
      2*(actualAppellCoefficient μ f 2 ⬝ᵥ actualAppellLowerDriftTensor μ f 2) ≤
    actualAppellEnergyHeatGenerator μ f 2 := by
  have hh := actualAppell_noiseCorrection_lower_two_symmetric hμ hf hβ0 hβ1
  unfold actualAppellEnergyHeatGenerator
  rw [actualCovarianceAppellEnergy_generator_exact hμ hf 2]
  norm_num only [Nat.cast_ofNat]
  linarith

end KLS.DeterministicBridgeIntegration
#print axioms KLS.DeterministicBridgeIntegration.actualCovarianceAppellEnergy_generator_lower_two_symmetric
